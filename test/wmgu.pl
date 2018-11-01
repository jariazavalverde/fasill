:- use_module('../src/environment').
:- use_module('../src/semantics').



% test_wmgu/5
% test_wmgu(+Sim, +ID, +TermA, +TermB, +ShouldBe)
%
% This predicate succeeds when terms +TermA and +TermB
% weakly unifies with truth degree +ShouldBe using the
% similarity relation +Sim. +Sim is an atom representing
% the name of the file that contains the similarity equations.
test_wmgu(ID, Lattice, Sim, X, Y, ShouldBe) :-
    (   lattice_consult(Lattice),
        similarity_consult(Sim),
        wmgu(X, Y, state(TD, _)
    ), Result = TD ; Result = fail), !,
    (ShouldBe \= Result -> throw(test_error(test_wmgu/ID, expected(ShouldBe), result(Result))) ; true).

% (real, good_hotel) metro ~ bus = 0.5
?- test_wmgu(1,
    '../sample/lat/real.lat.pl',
    '../sample/sim/good_hotel.sim.pl',
    term(metro,[]),
    term(bus,[]),
    num(0.5)
).

% (real, good_hotel) elegant(metro) ~ vanguardist(bus) = 0.5
?- test_wmgu(1,
    '../sample/lat/real.lat.pl',
    '../sample/sim/good_hotel.sim.pl',
    term(elegant,[term(metro,[])]),
    term(vanguardist,[term(bus,[])]),
    num(0.5)
).