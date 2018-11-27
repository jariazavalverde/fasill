/**
  * 
  * FILENAME: tuning_smt.pl
  * DESCRIPTION: This module contains predicates for tuning symbolic FASILL programs with the Z3 SMT solver.
  * AUTHORS: José Antonio Riaza Valverde
  * UPDATED: 27.11.2018
  * 
  **/



:- module(tuning_smt, [
    tuning_smt/2
]).

:- use_module('environment').
:- use_module('semantics').



% tuning_smt/2
% tuning_smt(?Substitution, ?Deviation)
%
% This predicate succeeds when ?Substitution is the best
% symbolic substitution for the set of test cases loaded
% into the current environment, with deviation ?Deviation.
tuning_smt(Best, Deviation) :-
    tuning_smt_minimize(Minimize),
    CheckSat = [reserved('check-sat')],
    GetModel = [reserved('get-model')].

% tuning_smt_minimize/1
% tuning_smt(?Minimize)
%
% This predicate succeeds when ?Minimize is the command
% to minimize the set of tests cases w.r.t. the expected
% truth degrees.
tuning_smt_minimize([Assert, Minimize]) :-
    findall([symbol('lattice!distance'), TD_, SMT], (
        fasill_testcase(TD, Goal),
        query(Goal, state(SFCA,_)),
        sfca_to_smtlib(TD, TD_),
        sfca_to_smtlib(SFCA, SMT)
    ), Distances),
    Assert = [reserved(assert), [symbol(=), symbol('deviation!'), [symbol(+), Distances]]],
    Minimize = [reserved(minimize), symbol('deviation!')].

% testcase_to_smtlib/2
% testcase_to_smtlib(+SFCA, ?SMTLIB)
%
% This predicate succeeds when +SFCA is a valid FASILL term
% representing a symbolic fuzzy computed answer and ?SMTLIB
% is the corresponding answer in SMT-LIB format.
sfca_to_smtlib(num(X), numeral(X)) :- number(X), !.
sfca_to_smtlib(num(X), decimal(X)) :- float(X), !.
sfca_to_smtlib(term('#'(X),[]), Y) :- atom_concat('sym!td!0!', X, Y).
sfca_to_smtlib(term(X,Xs), [symbol(Con2),symbol(Name4)|Xs2]) :-
    X =.. [Op,Name],
    member((Op,Pre), [('#&','and!'), ('#|','or!'), ('#@','agr!')]), !,
    length(Xs, Length),
    atom_number(Atom, Length),
    atom_concat(Pre, Atom, Con),
    atom_concat('call!', Con, Con2),
    atom_concat('sym!', Con, Name2),
    atom_concat(Name2, '!', Name3),
    atom_concat(Name3, Name, Name4),
    maplist(sfca_to_smtlib, Xs, Xs2).
sfca_to_smtlib(term(X,Xs), [symbol(Con)|Xs2]) :-
    X =.. [Op,Name],
    member((Op,Pre), [
      ('&','lattice!and!'), ('|','lattice!or!'), ('@','lattice!agr!'), ('#','sym!td!')
    ]), !,
    atom_concat(Pre, Name, Fun),
    length(Xs, Length),
    atom_number(Atom, Length),
    atom_concat(Fun, '!', Fun_),
    atom_concat(Fun_, Atom, Con),
    maplist(sfca_to_smtlib, Xs, Xs2).
sfca_to_smtlib(term(X,[]), symbol(X)).