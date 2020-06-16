/**
  * 
  * FILENAME: test/experiments/tnorms.pl
  * DESCRIPTION: This file performs statistics of the different t-norms of a lattice.
  * AUTHORS: José Antonio Riaza Valverde
  * UPDATED: 24.05.2020
  * 
  **/

:- use_module('../../src/semantics').
:- use_module('../../src/environment').



% TESTS

% test_tnorms/6
% test_tnorms(+Size, +Repeat, ?Tnorm, ?Min, ?Aver, ?Max)
%
% This predicate performs a test of the t-norms of unit lattice
% +Repeat times, with an arbitrary program p :- p1, ..., p+Size, returning
% the minimum ?Min, average ?Aver and maximum ?Max runtime and number
% of inferences with t-norm ?Tnorm.
test_tnorms(Size, Repeat, Tnorm, min(time(MinT), inferences(MinI)),
average(time(AverT), inferences(AverI)), max(time(MaxT), inferences(MaxI))) :-
    ( environment:lattice_consult('../../lattices/bool.lat.pl'), Gen = random_bool
    ; environment:lattice_consult('../../lattices/unit.lat.pl'), Gen = random_unit),
    environment:current_predicate(Name/3),
    atom_concat(and_, Tnorm, Name),
    test_tnorms(Gen, Tnorm, Size, Repeat, [], [], Times, Inferences),
    max_list(Times, MaxT), max_list(Inferences, MaxI),
    min_list(Times, MinT), min_list(Inferences, MinI),
    sum_list(Times, TotalT), sum_list(Inferences, TotalI),
    AverT is TotalT/Repeat, AverI is TotalI/Repeat.

test_tnorms(_, _, _, 0, Ts, Is, Ts, Is) :- !.
test_tnorms(Gen, Tnorm, Size, N, Ts, Is, Times, Inferences) :-
    succ(M, N),
    arbitrary_program(Gen, Size, '&'(Tnorm), Rules),
    environment:retractall(fasill_rule(_,_,_)),
    environment:maplist(assertz, Rules),
    statistics(runtime, [_,_]),
    statistics(inferences, I0),
    once(query(term(p,[]), Answer)),
    statistics(inferences, If),
    statistics(runtime, [_,T]),
    I is If-I0,
    (T >= 0 -> N_ = M, Ts_ = [T|Ts], Is_ = [I|Is] ; N_ = N, Ts_ = Ts, Is_ = Is),
    test_tnorms(Gen, Tnorm, Size, N_, Ts_, Is_, Times, Inferences).



% GENERATION OF PROGRAMS

random_unit(num(X)) :- random(X).
random_bool(num(X)) :- random_member(X, [0, 1]).

% arbitrary_program/4
% arbitrary_program(+Generator, +Size, +Tnorm, ?Program)
%
% This predicate returns an arbitrary FASILL program ?Program with
% +Size facts using the +Tnorm t-norm.
arbitrary_program(Gen, Size, Tnorm, [fasill_rule(head(term(p, [])), body(Body), [id(p)])|Facts]) :-
    (environment:fasill_predicate(p/0) -> true ; environment:assertz(fasill_predicate(p/0))),
    findall(X, between(0, Size, X), L),
    maplist(arbitrary_fact(Gen), L, Facts),
    arbitrary_body(Size, Tnorm, Body).

% arbitrary_body/3
% arbitrary_body(+Size, +Tnorm, ?Body)
%
% This predicate returns the body +Body of an arbitrary FASILL program
% with +Size facts using the +Tnorm t-norm.
arbitrary_body(0, _, term(p0, [])).
arbitrary_body(N, Tnorm, term(Tnorm, [Body, term(P,[])])) :-
    succ(M, N),
    atom_number(A, N),
    atom_concat(p, A, P),
    arbitrary_body(M, Tnorm, Body).

% arbitrary_fact/3
% arbitrary_fact(+Generator, +Index, ?Fact)
%
% This predicate returns an arbitrary FASILL fact ?Fact
% with indicator p+Index/0.
arbitrary_fact(Gen, N, fasill_rule(head(term(P,[])), body(TD), [id(N)])) :-
    atom_number(A, N),
    atom_concat(p, A, P),
    (environment:fasill_predicate(P/0) -> true ; environment:assertz(fasill_predicate(P/0))),
    call(Gen, TD).