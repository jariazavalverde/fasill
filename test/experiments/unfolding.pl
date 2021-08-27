/**
  * 
  * FILENAME: test/experiments/unfolding.pl
  * DESCRIPTION: This file performs statistics about unfolding.
  * AUTHORS: José Antonio Riaza Valverde
  * UPDATED: 13.03.2021
  * 
  **/

:- use_module('../../src/resolution').
:- use_module('../../src/environment').



gen_list(0, term('[]',[])).
gen_list(N, term('.', [num(1),T])) :- succ(M, N), gen_list(M, T).

test_permutation(Size, Level, Runtime, Inferences) :-
    lattice_consult('../../sample/lat/unit.lat.pl'),
    program_consult('../../sample/program/unfolding.fpl'),
    atom_number(Atom, Level),
    atom_concat('permutation', Atom, Name),
    gen_list(Size, List),
    statistics(runtime, [_,_]),
    statistics(inferences, I0),
    (query(term(Name, [List, var('X')]), Answer), fail ; true),
    statistics(inferences, If),
    statistics(runtime, [_,Runtime]),
    Inferences is If-I0.