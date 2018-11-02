:- use_module('../../src/environment').
:- use_module('../../src/semantics').



% test_builtin/4
% test_builtin(+Identifier, +Lattice, +Goal, +ShouldBe)
%
% This predicate succeeds when +Goal is the set of
% fuzzy computed answers +ShouldBe using the lattice
% +Lattice. +Lattice is an atom representing the name
% of the file that contains the lattice.
test_builtin(ID, Lattice, Goal, ShouldBe) :-
    (   lattice_consult(Lattice),
        findall(State, derivation(state(Goal, []), State, _), Result) ;
        Result = fail), !,
    (ShouldBe \= Result -> throw(test_error(test_builtin/ID, expected(ShouldBe), result(Result))) ; true).