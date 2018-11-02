:- module(semantics, [
    wmgu/3,
    derivation/3,
    inference/3,
    admissible_step/3,
    interpretive_step/3,
    apply/3,
    compose/3,
    rename/2
]).

:- use_module('environment').
:- use_module('exceptions').
:- use_module('builtin').



% UNIFICATION

% wmgu/3
% wmgu(+ExpressionA, +ExpressionB, ?State)
%
% This predicate returns the weak most general unifier (wmgu)
% ?State of the expressions +ExpressionA and +ExpressionB.
wmgu(ExprA, ExprB, State) :-
    lattice_call_top(Top),
    wmgu(ExprA, ExprB, state(Top,[]), State).
%%% var with expression
wmgu(var(X), Y, state(TD,Subs), State_) :-
    member(X/Z, Subs), !,
    wmgu(Z, Y, state(TD,Subs), State_).
wmgu(var(X), Y, state(TD,Subs), state(TD,[X/Y|Subs])) :- !.
%%% expression with var
wmgu(X, var(Y), State, State_) :- !, wmgu(var(Y), X, State, State_).
%%% num with num
wmgu(num(X), num(X), State, State) :- !.
%%% term with term
wmgu(term(X,Xs), term(X,Ys), State, State_) :- !,
    length(Xs, Length),
    length(Ys, Length),
    wmgu(Xs, Ys, State, State_).
wmgu(term(X,Xs), term(Y,Ys), state(TD, Subs), State) :- !,
    length(Xs, Length),
    length(Ys, Length),
    similarity_between(X, Y, Length, TDxy),
    similarity_tnorm(Tnorm),
    lattice_call_connective(Tnorm, [TD, TDxy], TD2),
    wmgu(Xs, Ys, state(TD2, Subs), State).
%%% arguments
wmgu([], [], State, State) :- !.
wmgu([X|Xs], [Y|Ys], State, State_) :- !,
    wmgu(X, Y, State, StateXY),
    wmgu(Xs, Ys, StateXY, State_).



% DERIVATIONS

% select_atom/4
% select_atom(+Expression, ?ExprVar, ?Var, ?Atom)
%
% This predicate selects an atom ?Atom from the expression
% +Expression, where ?ExprVar is the expression +Expression
% with the variable ?Var instead of the atom ?Atom.
select_atom(term(Term, Args), term(Term, Args_), Var, Atom) :-
    ( (Term =.. [Op,_] ; Term =.. [Op]), member(Op, ['@','&','|']) ;
      member(Term, ['@','&','|']) ), !,
    select_atom(Args, Args_, Var, Atom).
select_atom(term(Term, Args), Var, Var, term(Term, Args)).
select_atom([Term|Args], [Term_|Args], Var, Atom) :- select_atom(Term, Term_, Var, Atom), !.
select_atom([Term|Args], [Term|Args_], Var, Atom) :- select_atom(Args, Args_, Var, Atom).

% select_expression/4
% select_expression(+Expression, ?ExprVar, ?Var, ?Atom)
%
% This predicate selects an interpretable expression ?Atom
% from the expression +Expression, where ?ExprVar is the
% expression +Expression with the variable ?Var instead of
% the atom ?Atom.
select_expression(top, Var, Var, top) :- !.
select_expression(bot, Var, Var, bot) :- !.
select_expression(term(Term, Args), Var, Var, term(Term, Args)) :-
    ( (Term =.. [Op,_] ; Term =.. [Op]), member(Op, ['@','&','|']) ;
      member(Term, ['@','&','|']) ),
    maplist(lattice_call_member, Args), !.
select_expression(term(Term, Args), term(Term, Args_), Var, Expr) :- select_expression(Args, Args_, Var, Expr).
select_expression([Term|Args], [Term_|Args], Var, Atom) :- select_expression(Term, Term_, Var, Atom), !.
select_expression([Term|Args], [Term|Args_], Var, Atom) :- select_expression(Args, Args_, Var, Atom).

% interpretable/1
% interpretable(+Expression)
%
% This predicate succeeds when the expression +Expression
% can be interpreted (i.e., there is no atoms in the expression).
interpretable(Expr) :- \+select_atom(Expr, _, _, _).

% derivation/3
% derivation(+State1, ?State2, ?Info)
%
% This predicate performs a complete derivation from
% an initial state ?State1 to the final state ?State2,
% using the program +Program. ?Info is a list containing
% the information of each step.
derivation(State, State_, [X|Xs]) :-
    inference(State, State1, X),
    derivation(State1, State_, Xs).
derivation(state(Goal,Subs), state(Goal,Subs), []) :-
    lattice_call_member(Goal).

% inference/3
% inference(+State1, ?State2, ?Info)
%
% This predicate performs an inference step from the
% initial state +State1 to the final step ?State2. ?Info
% is an atom containg information about the rule used in
% the derivation.
inference(State, State_, Info) :- admissible_step(State, State_, Info).
inference(state(Goal,Subs), State_, Info) :- interpretable(Goal), interpretive_step(state(Goal,Subs), State_, Info).

% admissible_step/3
% admissible_step(+State1, ?State2, ?Info)
%
% This predicate performs an admissible step from the
% state +State1 to the state ?State2. ?Info is an atom
% containg information about the rule used in the derivation.
:- dynamic(check_success/0).
admissible_step(State1, State2, Info) :-
    assertz(check_success),
    success_step(State1, State2, Info),
    retractall(check_success).
admissible_step(State1, State2, Info) :-
    check_success,
    retractall(check_success),
    failure_step(State1, State2, Info).

% success_step/3
% success_step(+State1, ?State2, ?Info)
%
% This predicate performs a successful admissible step
% from the state +State1 to the state ?State2. ?Info is
% an atom containg information about the rule used in
% the derivation.
success_step(state(Goal,Subs), state(Goal_,Subs_), Info) :-
    select_atom(Goal, ExprVar, Var, Expr),
    Expr = term(Name, Args),
    length(Args, Arity),
    (is_builtin_predicate(Name/Arity) -> (
        eval_builtin_predicate(Name/Arity, state(Goal,Subs), selected(ExprVar, Var, Expr), state(Goal_,Subs_)),
        Info = Name
    ) ; (
        lattice_tnorm(Tnorm),
        program_clause(Name/Arity, Rule),
        rename(Rule, rule(head(Head),Body,_)),
        wmgu(Expr, Head, state(TD,SubsExpr)),
        (Body = empty -> Var = TD ; (Body = body(Body_), Var = term('&'(Tnorm), [TD,Body_]))),
        apply(ExprVar, SubsExpr, Goal_),
        compose(Subs, SubsExpr, Subs_),
        program_rule_id(Rule, RuleId),
        atom_number(InfoId, RuleId),
        atom_concat('R', InfoId, Info)
    )).

% failure_step/3
% failure_step(+State1, ?State2, ?Info)
%
% This predicate performs an unsuccessful admissible step
% from the state +State1 to the state ?State2. ?Info is an
% atom containg information about the failure.
failure_step(state(Goal,Subs), state(Goal_,Subs), 'FS') :-
    select_atom(Goal, Goal_, bot, _).

% interpretive_step/3
% interpretive_step(+State1, ?State2, ?Info)
%
% This predicate performs an interpretive step from the
% state +State1 to the state ?State2 ?Info is an atom
% containg information about the derivation. This steps
% only can be performed when there is no atoms to perform
% admissible steps.
interpretive_step(state(Goal,Subs), state(Goal_,Subs), 'IS') :-
    select_expression(Goal, Goal_, Var, Expr),
    interpret(Expr, Var).

% interpret/2
% interpret(+Expression, ?Result)
% 
% This predicate interprets the expression +Expression
% in the expression. ?Result is the resulting expression.
interpret(bot, Bot) :- !, lattice_call_bot(Bot).
interpret(top, Top) :- !, lattice_call_top(Top).
interpret(term(Op, Args), Result) :- (Op =.. [_,Name] ; Op =.. [Name]), lattice_call_connective(Name, Args, Result).

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



% VARIABLES

% current_fresh_variable_id/1
% current_fresh_variable_id(?Identifier)
%
% This predicate stores the current identifier ?Identifier
% to be used in a fresh variable.
:- dynamic(current_fresh_variable_id/1).
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