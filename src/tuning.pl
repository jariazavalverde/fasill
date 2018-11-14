/**
  * 
  * FILENAME: tuning.pl
  * DESCRIPTION: This module contains predicates for tunning symbolic FASILL programs.
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



% findall_symbolic_cons/1
% findall_symbolic_cons(?Symbols)
%
% This predicate succeeds when ?Symbols is the set of symbolic
% constants contained in the FASILL rules asserted in the current
% environment.
findall_symbolic_cons(Symbols) :-
    findall(Body, (fasill_rule(_, body(Body), _)), Rules),
    findall_symbolic_cons(Rules, Symbols).

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

% tuning_tau/1
% tuning_tau(?Tau)
%
%
%
:- dynamic(tuning_tau/1).

% tuning_substitution/1
% tuning_substitution(?Substitution)
%
%
%
:- dynamic(tuning_substitution/1).

% tuning_thresholded/2
% tuning_thresholded(?Substitution, ?Error)
%
%
%
tuning_thresholded(Subs, Error) :- 
    retractall(tuning_substitution(_)),
    retractall(tuning_tau(_)),
    asserta(tuning_tau(inf)),
	findall_symbolic_cons(Sym),
	findall(testcase(TD,SFCA), (
        fasill_testcase(TD, Goal),
        query(Goal, SFCA)
    ), Tests),
	( tuning_combination(Sym, Combination),
	  tuning_thresholded(Tests, Combination, 0.0),
      fail ; true ),
    tuning_substitution(Subs),
    tuning_tau(Error).

% tuning_thresholded/3
% tuning_thresholded(+Tests, +Substitution, ?Error)
%
%
%
tuning_thresholded([], Subs, Error) :- !,
	tuning_tau(Tau),
	(Tau = inf, ! ; Error < Tau),
	retractall(tuning_tau(_)),
	retractall(tuning_sub(_)),
	assertz(tuning_tau(Error)),
	assertz(tuning_substitution(Subs)).
tuning_thresholded([testcase(TD,SFCA)|Tests], Subs, Error) :-
	tuning_tau(Tau),
    (Tau = inf, ! ; Error < Tau),
    query(SFCA, state(TD_, _)),
	lattice_call_distance(TD, TD_, Difference),
	Error_ is Error + Difference,
    tuning_thresholded(Tests, Subs, Error_).