/**
  * 
  * FILENAME: test/experiments/rdf.pl
  * DESCRIPTION: This file performs statistics with the FSA-SPARQL application.
  * AUTHORS: José Antonio Riaza Valverde
  * UPDATED: 10.02.2020
  * 
  **/

:- use_module('../../src/resolution').
:- use_module('../../src/environment').



test_fsa(X, Runtime, Inferences) :-
    lattice_consult('../../sample/lat/fsa.lat.pl'),
    program_consult('../../sample/program/fsa.fpl'),
    assert_fsa(X),
    statistics(runtime, [_,_]),
    statistics(inferences, I0),
    once(query(term(test, []), _)),
    statistics(inferences, If),
    statistics(runtime, [_,Runtime]),
    Inferences is If-I0.

assert_fsa(1) :- !.
assert_fsa(N) :-
  succ(M, N),
  asserta(environment:fasill_rule(head(term(rdf, [
    term('http://www.movies.org#Oceans_eleven', []),
    term('http://www.fuzzy.org#type', []),
    term('http://www.movies.org#ocean_thriller', [])
  ])), empty, [id(fsa-N),syntax(fasill)])),
  assert_fsa(M).