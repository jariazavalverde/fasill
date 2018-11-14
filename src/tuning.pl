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
	findall_symbolic_constants(Sym),
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