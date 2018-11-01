:- module(semantics, [wmgu/4, derivation/4, inference/4, admissible_step/4, interpretive_step/4, apply/3, compose/3, rename/2]).



% VISIBLE PREDICATES

% to_prolog/2
% to_prolog(+FASILL, ?Prolog)
%
% This predicate takes the FASILL object +FASILL
% and returns the object ?Prolog in Prolog notation.
to_prolog([], []) :- !.
to_prolog([X|Xs], [Y|Ys]) :-
    !, to_prolog(X,Y),
    to_prolog(Xs,Ys).
to_prolog(num(X), X) :- !.
to_prolog(term(X,Xs), Term) :-
    atom(X),
    !, to_prolog(Xs, Ys),
    Term =.. [X|Ys].

% from_prolog/2
% from_prolog(+Prolog, ?FASILL)
%
% This predicate takes the Prolog object +Prolog
% and returns the object ?FASILL in FASILL notation.
from_prolog([], term([], [])) :- !.
from_prolog([X|Xs], term('.', [Y,Ys])) :-
    !, from_prolog(X,Y),
    from_prolog(Xs,Ys).
from_prolog(X, num(X)) :- number(X), !.
from_prolog(X, term(X, [])) :- atom(X), !.
from_prolog(X, term(H,Args)) :-
    compound(X), !,
    X =.. [H|T],
    maplist(from_prolog, T, Args).

% wmgu/4
% wmgu(+ExpressionA, +ExpressionB, +SimilarityRelation, ?State)
%
% This predicate returns the weak most general unifier (wmgu)
% ?State of the expressions +ExpressionA and +ExpressionB
% with the similarity relation +SimilarityRelation. The
% similarity relation +SimilarityRelation is a term
% '+'(Sim,Tnorm) where Sim is an atom representing
% a similarity relation predicate and Tnorm is an atom
% representing a conjunction operator.
wmgu(ExprA, ExprB, Sim+Tnorm, State) :-
    call(Sim, X, X, _, Top), !,
    wmgu(ExprA, ExprB, Sim+Tnorm, state(Top,[]), State).
%%% var with expression
wmgu(var(X), Y, Similarity, state(TD,Subs), State_) :-
    member(X/Z, Subs), !,
    wmgu(Z, Y, Similarity, state(TD,Subs), State_).
wmgu(var(X), Y, _, state(TD,Subs), state(TD,[X/Y|Subs])) :- !.
%%% expression with var
wmgu(X, var(Y), Similarity, State, State_) :- !, wmgu(var(Y), X, Similarity, State, State_).
%%% num with num
wmgu(num(X), num(X), _, State, State) :- !.
%%% term with term
wmgu(term(X,Xs), term(Y,Ys), Sim+Tnorm, state(TD, Subs), State) :- !,
    length(Xs, Length),
    length(Ys, Length),
    call(Sim, X, Y, Length, TDxy),
    to_prolog(TD, PLtd),
    to_prolog(TDxy, PLtdxy),
    call(Tnorm, PLtd, PLtdxy, PLtd2),
    from_prolog(PLtd2, TD2),
    wmgu(Xs, Ys, Sim+Tnorm, state(TD2, Subs), State).
%%% arguments
wmgu([], [], _, State, State) :- !.
wmgu([X|Xs], [Y|Ys], Sim, State, State_) :- !,
    wmgu(X, Y, Sim, State, StateXY),
    wmgu(Xs, Ys, Sim, StateXY, State_).

% select_atom/4
% select_atom(+Expression, ?ExprVar, ?Var, ?Atom)
%
% This predicate selects an atom ?Atom from the expression
% +Expression, where ?ExprVar is the expression +Expression
% with the variable ?Var instead of the atom ?Atom.
select_atom(term(Term, Args), term(Term, Args_), Var, Atom) :-
    ( Term =.. [Op,_], member(Op, ['@','&','|']) ;
      member(Term, ['@','&','|']) ), !,
    select_atom(Args, Args_, Var, Atom).
select_atom(term(Term, Args), Var, Var, term(Term, Args)).
select_atom([Term|Args], [Term_|Args], Var, Atom) :- select_atom(Term, Term_, Var, Atom), !.
select_atom([Term|Args], [Term|Args_], Var, Atom) :- select_atom(Args, Args_, Var, Atom).

% select_expression/5
% select_expression(+Expression, ?ExprVar, ?Var, ?Atom, +Members)
%
% This predicate selects an interpretable expression ?Atom
% from the expression +Expression, where ?ExprVar is the
% expression +Expression with the variable ?Var instead of
% the atom ?Atom. +Members is an atom representing the
% members predicate of a lattice.
select_expression(top, Var, Var, top, _) :- !.
select_expression(top, Var, Var, bot, _) :- !.
select_expression(term(Term, Args), Var, Var, term(Term, Args), Members) :-
    ( Term =.. [Op,_], member(Op, ['@','&','|']) ;
      member(Term, ['@','&','|']) ),
    maplist(is_member(Members), Args), !.
select_expression(term(Term, Args), term(Term, Args_), Var, Expr, Members) :- select_expression(Args, Args_, Var, Expr, Members).
select_expression([Term|Args], [Term_|Args], Var, Atom, Members) :- select_expression(Term, Term_, Var, Atom, Members), !.
select_expression([Term|Args], [Term|Args_], Var, Atom, Members) :- select_expression(Args, Args_, Var, Atom, Members).

% is_member/2
% is_member(+Member, +Element)
%
% This predicate succeeds when the element +Element
% is a member of the lattice. +Member is an atom
% representing the member predicate of the lattice.
is_member(Member, X) :- to_prolog(X, Y), call(Member, Y).

% interpretable/1
% interpretable(+Expression)
%
% This predicate succeeds when the expression +Expression
% can be interpreted (i.e., there is no atoms in the expression).
interpretable(Expr) :- \+select_atom(Expr, _, _, _).

% derivation/4
% derivation(+Program, +State1, ?State2, ?Info)
%
% This predicate performs a complete derivation from
% an initial state ?State1 to the final state ?State2,
% using the program +Program. ?Info is a list containing
% the information of each step.
derivation(Program, State, State_, [X|Xs]) :-
    inference(Program, State, State1, X),
    derivation(Program, State1, State_, Xs).
derivation(program(_,_,Lattice), state(Goal,Subs), state(Goal,Subs), []) :-
    member(member(Members), Lattice),
    to_prolog(Goal, GoalProlog),
    call(Members, GoalProlog).

% inference/4
% inference(+Program, +State1, ?State2, ?Info)
%
% This predicate performs an inference step from the
% initial state +State1 to the final step ?State2. ?Info
% is an atom containg information about the rule used in
% the derivation.
inference(Program, State, State_, Info) :- admissible_step(Program, State, State_, Info).
inference(Program, state(Goal,Subs), State_, Info) :- interpretable(Goal), interpretive_step(Program, state(Goal,Subs), State_, Info).

% admissible_step/4
% admissible_step(+Program, +State1, ?State2, ?Info)
%
% This predicate performs an admissible step from the
% state +State1 to the state ?State2 using the program
% +Program. ?Info is an atom containg information about
% the rule used in the derivation.
:- dynamic(check_success/0).
admissible_step(Program, State1, State2, Info) :-
    assertz(check_success),
    success_step(Program, State1, State2, Info),
    retractall(check_success).
admissible_step(Program, State1, State2, Info) :-
    check_success,
    retractall(check_success),
    failure_step(Program, State1, State2, Info).

% success_step/4
% success_step(+Program, +State1, ?State2, ?Info)
%
% This predicate performs a successful admissible step
% from the state +State1 to the state ?State2 using the
% program +Program. ?Info is an atom containg information
% about the rule used in the derivation.
success_step(program(Pi,Sim+Tnorm,_), state(Goal,Subs), state(Goal_,Subs_), Info) :-
    select_atom(Goal, ExprVar, Var, Expr),
    Expr = term(Name, Args),
    length(Args, Arity),
    (is_builtin_predicate(Name/Arity) -> (
        eval_builtin_predicate(Name/Arity, state(Goal,Subs), selected(ExprVar, Var, Expr), state(Goal_,Subs_)),
        Info = Name
    ) ; (
        member(Rule, Pi),
        rename(Rule, rule(head(Head),Body,_)),
        wmgu(Expr, Head, Sim+Tnorm, state(TD,SubsExpr)),
        (Body = empty -> Var = TD ; (Body = body(Body_), Var = term('&'(Tnorm), [TD,Body_]))),
        apply(ExprVar, SubsExpr, Goal_), compose(Subs, SubsExpr, Subs_),
        rule_id(Rule, RuleId), atom_number(InfoId,RuleId), atom_concat('R', InfoId, Info)
    )).

% failure_step/4
% failure_step(+Program, +State1, ?State2, ?Info)
%
% This predicate performs an unsuccessful admissible step
% from the state +State1 to the state ?State2 using the
% program +Program. ?Info is an atom containg information
% about the failure.
failure_step(_, state(Goal,Subs), state(Goal_,Subs), 'FS') :-
    select_atom(Goal, Goal_, bot, _).

% interpretive_step/4
% interpretive_step(+Program, +State1, ?State2, ?Info)
%
% This predicate performs an interpretive step from the
% state +State1 to the state ?State2 using the program
% +Program. ?Info is an atom containg information about
% the derivation. This steps only can be performed when
% there is no atoms to perform admissible steps.
interpretive_step(program(_,_,Lattice), state(Goal,Subs), state(Goal_,Subs), 'IS') :-
    member(member(Member), Lattice),
    select_expression(Goal, Goal_, Var, Expr, Member),
    interpret(Expr, Var, Lattice).

% interpret/3
% interpret(+Expression, ?Result, +Lattice)
% 
% This predicate interprets the expression +Expression
% using the lattice +Lattice to evaluate the operations
% in the expression. ?Result is the resulting expression.
interpret(bot, BotMember, Lattice) :-
    !, member(bot(Bot), Lattice),
    call(Bot, BotProlog),
    from_prolog(BotProlog, BotMember).
interpret(top, TopMember, Lattice) :-
    !, member(top(Top), Lattice),
    call(Top, TopProlog),
    from_prolog(TopProlog, TopMember).
interpret(term(Op, Args), Result, Lattice) :-
    Op =.. [_,Name],
    member(Name, Lattice),
    maplist(to_prolog, Args, ArgsProlog),
    append(ArgsProlog, [ResultProlog], ArgsCall),
    Call =.. [Name|ArgsCall],
    call(Call),
    from_prolog(ResultProlog, Result).

% rename/2
% rename(+Expression, ?Renamed)
%
% This predicate renames the expression +Expression, replacing
% the variables of the expression by fresh variables. ?Renamed
% is the expression +Expression with fresh variables.
rename(X, Y) :- rename(X, Y, [], _).
rename(var(X), var(Y), Subs, Subs) :- member(X/Y, Subs), !.
rename(var(X), var(Y), Subs, [X/Y|Subs]) :- 
    !, auto_fresh_variable_id(Id),
    atom_number(Atom, Id),
    atom_concat('V', Atom, Y).
rename(term(Name, Xs), term(Name, Ys), Subs, Subs_) :-
    !, rename(Xs, Ys, Subs, Subs_).
rename([X|Xs], [Y|Ys], Subs, Subs3) :-
    !, rename(X, Y, Subs, Subs2),
    rename(Xs, Ys, Subs2, Subs3).
rename(X, X, Subs, Subs).

% compose/3
% compose(+Substitution1, +Substitution2, ?SubstitutionOut)
%
% This predicate composes both substitutions, +Substitution1
% and +Substitution2 in ?SubstitutionOut.
compose([], Xs, Xs).
compose([X/Y|Xs], Subs, [X/Y_|Ys]) :- apply(Y, Subs, Y_), apply(Xs, Subs, Ys).

% apply/3
% apply(+ExpressionIn, +Substitution, ?ExpressionOut)
%
% This predicate applies the substitution +Substitution to
% the expression +ExpressionIn. ?ExpressionOut is the resulting
% expression.
apply(term(T,Args), Subs, term(T,Args_)) :- !, apply(Args, Subs, Args_).
apply(var(X), X/Y, Y) :- !. 
apply([], _, []) :- !.
apply([H|T], Subs, [H_|T_]) :- !, apply(H, Subs, H_), apply(T, Subs, T_).
apply(Expr, [], Expr) :- !.
apply(Expr, [H|T], Expr_) :- !, apply(Expr, H, ExprH), apply(ExprH, T, Expr_).
apply(Expr, _/_, Expr) :- !.



% RULES MANIPULATION

% rule_id/2
% rule_id(+Rule, ?Id)
%
% This predicate succeeds when ?Id is the identifier
% of the rule +Rule.
rule_id(rule(_,_,Info), Id) :- member(id(Id), Info).



% VARIABLES

% current_fresh_variable_id/1
% current_fresh_variable_id(?Identifier)
%
% This predicate stores the current identifier ?Identifier
% to be used in a fresh variable.
:- dynamic current_fresh_variable_id/1.
?- retractall(current_fresh_variable_id(_)).
current_fresh_variable_id(1).

% auto_fresh_variable_id/1
% auto_fresh_variable_id(?Identifier)
%
% This predicate updates the current variable identifier 
% ?Identifier and returns it.
auto_fresh_variable_id(Id) :-
    current_fresh_variable_id(Id),
    retract(current_fresh_variable_id(_)),
    N is Id+1,
    assertz(current_fresh_variable_id(N)).

% reset_fresh_variable_id/0
% reset_fresh_variable_id
%
% This predicate resets the current ?Identifier identifier
% to the first.
reset_fresh_variable_id :-
    retract(current_fresh_variable_id(_)),
    assertz(current_fresh_variable_id(1)).



% BUILT-IN PREDICATES

% is_builtin_predicate/1
% is_builtin_predicate(?Indicator)
%
% This predicate succeeds when ?Indicator is the
% indicator of a builtin predicate of FASILL. An indicator
% is a term of the form Name/Arity, where Name is an atom
% and Arity is a non-negative integer.
is_builtin_predicate(Name/Arity) :-
    member(Name/Arity, [
        % type testing
        atom/1,
        compound/1,
        number/1,
        integer/1,
        float/1,
        var/1,
        nonvar/1,
        % atom processing
        atom_concat/3
    ]).

% TYPE TESTING

% atom/1
% atom(@term)
eval_builtin_predicate(atom/1, state(_, Subs), selected(ExprVar, top, Atom), state(ExprVar, Subs)) :-
    Atom = term(atom, [term(_, [])]).

% compound/1
% compound(@term)
eval_builtin_predicate(compound/1, state(_, Subs), selected(ExprVar, top, Atom), state(ExprVar, Subs)) :-
    Atom = term(atom, [term(_, [_|_])]).

% var/1
% var(@term)
eval_builtin_predicate(var/1, state(_, Subs), selected(ExprVar, top, Atom), state(ExprVar, Subs)) :-
    Atom = term(number, [var(_)]).

% nonvar/1
% nonvar(@term)
eval_builtin_predicate(nonvar/1, state(_, Subs), selected(ExprVar, top, Atom), state(ExprVar, Subs)) :-
    Atom = term(number, [X]),
    X \= var(_).

% number/1
% number(@term)
eval_builtin_predicate(number/1, state(_, Subs), selected(ExprVar, top, Atom), state(ExprVar, Subs)) :-
    Atom = term(number, [num(_)]).

% float/1
% float(@term)
eval_builtin_predicate(float/1, state(_, Subs), selected(ExprVar, top, Atom), state(ExprVar, Subs)) :-
    Atom = term(float, [num(X)]),
    float(X).

% integer/1
% integer(@term)
eval_builtin_predicate(integer/1, state(_, Subs), selected(ExprVar, top, Atom), state(ExprVar, Subs)) :-
    Atom = term(integer, [num(X)]),
    integer(X).

% ATOM PROCESSING 

% atom_concat/3
% atom_concat(+First, +Second, -Concat).
eval_builtin_predicate(atom_concat/3, state(_, Subs), selected(ExprVar, Var, Atom), state(ExprVar, Subs)) :-
    Atom = term(atom_concat, [X,Y,Z]),
    X = term(AtomX, []),
    Y = term(AtomY, []),
    atom_concat(AtomX, AtomY, AtomZ),
    Var = term(=, [Z, term(AtomZ, [])]).