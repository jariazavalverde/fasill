:- use_module('../src/parser').
:- use_module('../src/semantics').


% PARSER

parser_case_1(
    "p(X) <- @very(q(X)) with 0.7.
     q(X) <- r(X) with 0.9.
     r(a). r(b)."
).



% SEMANTICS

% Programs
program_empty(program([], sim_case_1+and_prod, Lattice)) :- lattice_real(Lattice).

program_case_1(
    program([
        rule(head(term(p, [var('Y')])), body(term(q, [var('Y')])), [id(1),syntax(fasill)]),
        rule(head(term(q, [term(b, [])])), empty, [id(2),syntax(fasill)])
    ],
    sim_case_1+and_prod,
    Lattice)
) :- lattice_real(Lattice).

% Lattice
lattice_real([
    member(member_real),
    leq(leq_real),
    top(top_real),
    bot(bot_real),
    and_godel, and_luka, and_prod,
    or_godel, or_luka, or_prod,
    agr_aver, agr_very
]).

% Membering and Ordering relations
member_real(X) :- number(X), X >= 0, X =< 1.
leq_real(X,Y) :- X =< Y.
bot_real(0.0).
top_real(1.0).

% T-norms
and_prod(X,Y,Z) :- Z is X*Y.
and_godel(X,Y,Z) :- Z is min(X,Y).
and_luka(X,Y,Z) :- Z is max(0, X+Y-1).

% T-conorms
or_prod(X,Y,Z) :- Z is X+Y-X*Y.
or_luka(X,Y,Z) :- Z is min(1,X+Y).
or_godel(X,Y,Z) :- Z is max(X,Y).

% Aggregators
agr_aver(X,Y,Z) :- Z is (X+Y)/2.
agr_very(X,Y) :- Y is X*X.

% Similarity relations
%%% sim_case_1
sim_case_1(X, X, _, num(1.0)). % Identity
sim_case_1(p, q, 1, num(0.5)). % p/1 ~ q/1 = 0.5
sim_case_1(a, b, 0, num(0.3)). % a/0 ~ b/0 = 0.3

% Test weak unification
test_wmgu(ID, X, Y, Sim, ShouldBe) :-
    (wmgu(X, Y, Sim, state(TD, _)), Result = td(TD) ; Result = fail), !,
    (ShouldBe \= Result -> throw(test_error(test_wmgu/ID, expected(ShouldBe), result(Result))) ; true).

    % (sim_case_1) a &prod b = 0.3
    ?- test_wmgu(1, term(a,[]), term(b,[]), sim_case_1+and_prod, td(num(0.3))).
    % (sim_case_1) p(a) &prod q(b) = 0.15
    ?- test_wmgu(2, term(p,[term(a, [])]), term(q,[term(b, [])]), sim_case_1+and_prod, td(num(0.15))).
    % (sim_case_1) p(X) &prod q(Y) = 0.5
    ?- test_wmgu(3, term(p,[var('X')]), term(q,[var('Y')]), sim_case_1+and_prod, td(num(0.5))).
    % (sim_case_1) p(p(a)) &prod q(q(b)) = 0.15
    ?- test_wmgu(4, term(p,[term(p, [term(a, [])])]), term(q,[term(q, [term(b, [])])]), sim_case_1+and_prod, td(num(0.075))).
    % (sim_case_1) p(1,a) &prod p(X,b) = 0.3
    ?- test_wmgu(5, term(p, [num(1),term(a,[])]), term(p,[var('X'),term(b,[])]), sim_case_1+and_prod, td(num(0.3))).
    % (sim_case_1) p(X,X) &prod p(a,c) = 0.3
    ?- test_wmgu(6, term(p, [var('X'),var('X')]), term(p,[term(a, []),term(c,[])]), sim_case_1+and_prod, fail).

% Test admissible steps
test_admissible_step(ID, Program, State, ShouldBe) :-
    (admissible_step(Program, State, Result, _), ! ; Result = fail),
    (ShouldBe \= Result -> throw(test_error(test_admissible_step/ID, expected(ShouldBe), result(Result))) ; true).

    % (program_case_1) <p(X),{}> \rightarrow_{AS} <1.0 &prod q(Y),{X/Y}>
    ?- program_case_1(Program), test_admissible_step(1, Program,
        state(term(p,[var('X')]),[]),
        state(term(&(and_prod),[num(1.0),term(q,[var('Y')])]),['X'/var('Y')])
    ).
    % (program_case_1) <0.5 &godel p(X),{}> \rightarrow_{AS} <0.5 &godel (1.0 &prod q(Y)),{X/Y}>
    ?- program_case_1(Program), test_admissible_step(2, Program,
        state(term(&(and_godel), [num(0.5), term(p,[var('X')])]),[]),
        state(term(&(and_godel), [num(0.5), term(&(and_prod),[num(1.0),term(q,[var('Y')])])]),['X'/var('Y')])
    ).
    % (builtin) <atom_concat(ab, cd, X),{}> \rightarrow_{AS} <X = abcd,{}>
    ?- program_empty(Program), test_admissible_step(3, Program,
        state(term(atom_concat, [term(ab, []), term(cd, []), var('X')]),[]),
        state(term(=, [var('X'), term(abcd, [])]),[])
    ).