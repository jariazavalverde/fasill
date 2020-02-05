/**
  * 
  * FILENAME: test/experiments/queens.pl
  * DESCRIPTION: This file performs statistics with the problem of n queens.
  * AUTHORS: José Antonio Riaza Valverde
  * UPDATED: 05.02.2020
  * 
  **/

:- use_module('../../src/semantics').
:- use_module('../../src/environment').



test_queens(X, Runtime, Inferences) :-
    lattice_consult('../../sample/lat/bool.lat.pl'),
    program_consult('../../sample/program/queens.fpl'),
    statistics(runtime, [_,_]),
    statistics(inferences, I0),
    once(query(term('queens', [num(X)]), _)),
    statistics(inferences, If),
    statistics(runtime, [_,Runtime]),
    Inferences is If-I0.