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



% TUNING THRESHOLDED TECHNIQUE

% tuning_thresholded/2
% tuning_thresholded(?Substitution, ?Deviation)
%
% This predicate succeeds when ?Substitution is the best
% symbolic substitution for the set of test cases loaded
% into the current environment, with deviation ?Deviation.
tuning_thresholded(Subs, Deviation) :- 
    retractall(tuning_best_substitution(_,_)),
	findall_symbolic_cons(Sym),
	findall(testcase(TD,SFCA), (
        fasill_testcase(TD, Goal),
        query(Goal, SFCA)
    ), Tests),
	( tuning_combination(Sym, Combination),
	  tuning_thresholded(Tests, Combination, 0.0),
      fail ; true ),
    tuning_best_substitution(Subs, Deviation).

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
    query(SFCA, state(TD_, _)),
	lattice_call_distance(TD, TD_, Distance),
	Error_ is Error + Distance,
    tuning_thresholded(Tests, Subs, Error_).