/**
  * 
  * FILENAME: tuning.pl
  * DESCRIPTION: This module contains predicates for tuning symbolic FASILL programs.
  * AUTHORS: José Antonio Riaza Valverde
  * UPDATED: 14.11.2018
  * 
  **/



:- module(tuning, [
    tuning_basic/2,
    tuning_symbolic/2,
    tuning_thresholded/2
]).

:- use_module('environment').
:- use_module('semantics').



% tuning_best_substitution/2
% tuning_best_substitution(?Substitution, ?Deviation)
%
% This predicate succeeds when ?Substitution is the best
% substitution found so far and ?Deviation is the deviation
% with respect to the set of test cases.
:- dynamic(tuning_best_substitution/2).



% UTILS

% findall_symbolic_cons/1
% findall_symbolic_cons(?Symbols)
%
% This predicate succeeds when ?Symbols is the set of symbolic
% constants contained in the FASILL rules asserted in the current
% environment.
findall_symbolic_cons(Set) :-
    findall(Body, (fasill_rule(_, body(Body), _)), Rules),
    findall_symbolic_cons(Rules, Symbols),
    list_to_set(Symbols, Set).

% findall_symbolic_cons/2
% findall_symbolic_cons(+Expression, ?Symbols)
%
% This predicate succeeds when ?Symbols is the set of symbolic
% constants contained in +Expression.
findall_symbolic_cons([], []) :- !.
findall_symbolic_cons([H|T], Sym) :- !,
    findall_symbolic_cons(H, SymH),
    findall_symbolic_cons(T, SymT),
    append(SymH, SymT, Sym).
findall_symbolic_cons(term('#'(Name),[]), [sym(td, Name, 0)]) :- !.
findall_symbolic_cons(term(Term, Args), [sym(Type, Name, Arity)|Sym]) :-
    Term =.. [Op,Name],
    member((Op,Type), [('#&',and),('#|',or),('#@',agr),('#?',con)]),
    !, length(Args, Arity),
    findall_symbolic_cons(Args, Sym).
findall_symbolic_cons(term(_, Args), Sym) :- !, findall_symbolic_cons(Args, Sym).
findall_symbolic_cons(_, []).

% symbolic_substitution/2
% symbolic_substitution(+Symbols, -Substitution)
%
% This predicate succeeds when +Symbols is a set of symbolic
% constants and -Substitution is a possible symbolic substitution
% for constants +Symbols. This predicate can be used for generating,
% by reevaluation, all possible symbolic substitutions for the constants.
symbolic_substitution([], []).
symbolic_substitution([H|T], [H/H_|T_]) :-
    symbolic_substitution(H, H_),
    symbolic_substitution(T, T_).
symbolic_substitution(sym(td,_,0), val(td,Value,0)) :-
    lattice_call_members(Members),
    member(Value, Members).
symbolic_substitution(sym(Type,_,Arity), val(Type,Name,Arity)) :-
    Arity > 0,
    Arity_ is Arity + 1,
    atom_concat(Type, '_', Type_),
    current_predicate(environment:Predicate/Arity_),
    atom_concat(Type_, Name, Predicate).

% apply_symbolic_substitution/3
% apply_symbolic_substitution(+ExpressionIn, +Substitution, -ExpressionOut)
%
% This predicate succeeds when +ExpressionOut is the resulting
% expression after applying the symbolic substitution +Substitution
% to the expression +ExpressionIn.
apply_symbolic_substitution(term('#'(Name),[]), Subs, Value) :-
    member(sym(td,Name,0)/val(td,Value,0), Subs), !.
apply_symbolic_substitution(term(Term,Args), Subs, term(Term2,Args_)) :-
    Term =.. [Op, Name],
    length(Args, Length),
    member((Op,Type), [('#&',and),('#|',or),('#@',agr),('#?',con)]),
    member(sym(Type,Name,Length)/val(Type2,Value,Length), Subs),
    member((Op2,Type2), [('&',and),('|',or),('@',agr)]),
    Term2 =.. [Op2, Value],
    apply_symbolic_substitution(Args, Subs, Args_), !.
apply_symbolic_substitution(term(Name,Args), Subs, term(Name,Args_)) :-
    apply_symbolic_substitution(Args, Subs, Args_), !.
apply_symbolic_substitution([H|T], Subs, [H_|T_]) :-
    apply_symbolic_substitution(H, Subs, H_),
    apply_symbolic_substitution(T, Subs, T_), !.
apply_symbolic_substitution(X, _, X).



% TUNING THRESHOLDED TECHNIQUE

% tuning_thresholded/2
% tuning_thresholded(?Substitution, ?Deviation)
%
% This predicate succeeds when ?Substitution is the best
% symbolic substitution for the set of test cases loaded
% into the current environment, with deviation ?Deviation.
tuning_thresholded(Best, Deviation) :-
    retractall(tuning_best_substitution(_,_)),
	findall_symbolic_cons(Sym),
	findall(testcase(TD,SFCA), (
        fasill_testcase(TD, Goal),
        query(Goal, state(SFCA,_))
    ), Tests),
	( symbolic_substitution(Sym, Subs),
	  tuning_thresholded(Tests, Subs, 0.0),
      fail ; true ),
    tuning_best_substitution(Best, Deviation).

% tuning_thresholded/3
% tuning_thresholded(+Tests, +Substitution, ?Error)
%
% This predicate succeeds when ?Substitution is the best
% symbolic substitution for the set of test cases loaded
% into the current environment, with deviation ?Deviation.
% +Tests is the set of test cases with goal partially executed.
tuning_thresholded([], Subs, Error) :- !,
    (tuning_best_substitution(_, Best) -> Best > Error ; true),
	retractall(tuning_best_substitution(_,_)),
	asserta(tuning_best_substitution(Subs, Error)).
tuning_thresholded([testcase(TD,SFCA)|Tests], Subs, Error) :-
    (tuning_best_substitution(_, Best) -> Best > Error ; true),
    apply_symbolic_substitution(SFCA, Subs, FCA),
    query(FCA, state(TD_, _)),
	lattice_call_distance(TD, TD_, num(Distance)),
	Error_ is Error + Distance,
    tuning_thresholded(Tests, Subs, Error_).