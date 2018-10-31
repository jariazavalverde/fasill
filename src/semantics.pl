:- module(semantics, [wmgu/4, derivation/4, inference/4, admissible_step/4, interpretive_step/4, apply/3, compose/3, rename/2]).



% VISIBLE PREDICATES

% to_prolog/2
% to_prolog(+FASILL, ?Prolog)
%
% This function takes the FASILL object +FASILL
% and returns the object ?Prolog in Prolog notation.
to_prolog([], []) :- !.
to_prolog([X|Xs], [Y|Ys]) :-
    !, to_prolog(X,Y),
    to_prolog(Xs,Ys).
to_prolog(num(X), X) :- !.
to_prolog(term(X,Xs), Term) :-
    !, to_prolog(Xs, Ys),
    Term =.. [X|Ys].

% from_prolog/2
% from_prolog(+Prolog, ?FASILL)
%
% This function takes the Prolog object +Prolog
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
% This function returns the weak most general unifier (wmgu)
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
% This function selects an atom ?Atom from the expression
% +Expression, where ?ExprVar is the expression +Expression
% with the variable ?Var instead of the atom ?Atom.
select_atom(term(Term, Args), term(Term, Args_), Var, Atom) :-
    ( Term =.. [Op, _], member(Op, ['@','&','|']) ;
      member(Term, ['@','&','|']) ), !,
    select_atom(Args, Args_, Var, Atom).
select_atom(term(Term, Args), Var, Var, term(Term, Args)).
select_atom([Term|Args], [Term_|Args], Var, Atom) :- select_atom(Term, Term_, Var, Atom), !.
select_atom([Term|Args], [Term|Args_], Var, Atom) :- select_atom(Args, Args_, Var, Atom).

% select_expression/5
% select_expression(+Expr, ?ExprVar, ?Var, ?Atom, +Members)
%
% This function selects an interpretable expression.
select_expression(term(Term, Args), Var, Var, term(Term, Args), Members) :-
    ( Term =.. [Op, _], member(Op, ['@','&','|']) ;
      member(Term, ['@','&','|']) ),
    all_members(Args, Members), !.
select_expression(term(Term, Args), term(Term, Args_), Var, Expr, Members) :- select_expression(Args, Args_, Var, Expr, Members).
select_expression([Term|Args], [Term_|Args], Var, Atom, Members) :- select_expression(Term, Term_, Var, Atom, Members), !.
select_expression([Term|Args], [Term|Args_], Var, Atom, Members) :- select_expression(Args, Args_, Var, Atom, Members).

% all_members/2
%
%
all_members([], _).
all_members([X|Xs], Members) :- call(Members, X), all_members(Xs, Members).

% interpretable/1
% check if expression has no atoms
interpretable(Expr) :- \+select_atom(Expr, _, _, _).

% derivation/4
% perform a complete derivation
derivation(Program, State, State_, [X|Xs]) :-
    inference(Program, State, State1, X),
    derivation(Program, State1, State_, Xs).
derivation(program(_,_,Lattice), state(Goal,Subs), state(Goal,Subs), []) :-
    member(member(Members), Lattice),
    call(Members, Goal).

% inference/4
% inference(+Program, +State, -NewState, -Info)
% perform an inference step
inference(Program, State, State_, Info) :- admissible_step(Program, State, State_, Info), !.
inference(Program, state(Goal,Subs), State_, Info) :- interpretable(Goal), interpretive_step(Program, state(Goal,Subs), State_, Info).

% admissible_step/4
% admissible_step(+Program, +State, -NewState, -Info)
% perform an admissible step
admissible_step(program(Pi,Sim+Tnorm,_), state(Goal,Subs), state(Goal_,Subs_), Info) :-
    select_atom(Goal, ExprVar, Var, Expr),
    member(Rule, Pi),
    rename(Rule, rule(head(Head),Body,_)),
    wmgu(Expr, Head, Sim+Tnorm, state(TD,SubsExpr)),
    (Body = empty -> Var = TD ; (Body = body(Body_), Var = term('&'(Tnorm), [TD,Body_]))),
    apply(ExprVar, SubsExpr, Goal_), compose(Subs, SubsExpr, Subs_),
    rule_id(Rule, RuleId), atom_number(InfoId,RuleId), atom_concat('R', InfoId, Info).

% interpretive_step/4
% interpretive_step(+Program, +State, -NewState, -Info)
% perform an interpretive step
interpretive_step(program(_,_,Lattice), state(Goal,Subs), state(Goal_,Subs), 'IS') :-
    member(member(Member), Lattice),
    select_expression(Goal, Goal_, Var, Expr, Member),
    interpret(Expr, Var, Lattice).

% interpret/3
%
%
interpret(term(Op, Args), Expr_, Lattice) :-
    Op =.. [_, Name],
    member(Name, Lattice),
    append(Args, [Expr_], ArgsCall),
    Call =.. [Name|ArgsCall],
    call(Call).

% rename/2
% rename the variables of a rule or expression
rename(X, X).

% compose/3
% compose two substitutions
compose([], Xs, Xs).
compose([X/Y|Xs], Subs, [X/Y_|Ys]) :- apply(Y, Subs, Y_), apply(Xs, Subs, Ys).

% apply/3
% apply a substitution to an expression
apply(term(T,Args), Subs, term(T,Args_)) :- !, apply(Args, Subs, Args_).
apply(var(X), X/Y, Y) :- !. 
apply([], _, []) :- !.
apply([H|T], Subs, [H_|T_]) :- !, apply(H, Subs, H_), apply(T, Subs, T_).
apply(Expr, [], Expr) :- !.
apply(Expr, [H|T], Expr_) :- !, apply(Expr, H, ExprH), apply(ExprH, T, Expr_).
apply(Expr, _/_, Expr) :- !.



% RULES MANIPULATION

% rule_id/2
% return the identifier of a rule
rule_id(rule(_,_,Info), Id) :- member(id(Id), Info).



% VARIABLES

% current_variable_id/1
% store the current identifier to be used in renaming
:- dynamic current_variable_id/1.
?- retractall(current_variable_id(_)).
current_variable_id(1).

% auto_variable_id/1
% update the current variable identifier and return it
auto_rule_id(Id) :-
    current_variable_id(Y),
    retract(current_variable_id(_)),
    N is Id+1,
    assertz(current_variable_id(N)),
    atom_number(X,Id),
    atom_concat('_',X,Y).

% reset_variable_id/0
% reset the current variable identifier to the first
reset_variable_id :- retract(current_variable_id(_)), assertz(current_variable_id(1)).



% BUILT-IN PREDICATES