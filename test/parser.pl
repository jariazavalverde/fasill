:- use_module('../src/parser').



% test_parser/3
% test_parser(+Identifier, +Program, +ShouldBe)
%
% This predicate succeeds when the file +Program is parsed
% to +ShouldBe. +Program is an atom representing the name
% of the file that contains the program.
test_parser(ID, Path, ShouldBe) :-
    (file_consult(Path, Program), Result = Program ; Result = fail), !,
    (ShouldBe \= Result -> throw(test_error(test_parser/ID, expected(ShouldBe), result(Result))) ; true).

% (good_hotel)
:- test_parser(
    1,
    '../sample/program/good_hotel.fpl',
    [
        fasill_rule(head(term(vanguardist, [term(hydropolis, [])])), body(num(0.9)), [id(1), syntax(fasill)]),
        fasill_rule(head(term(elegant, [term(ritz, [])])), body(num(0.8)), [id(2), syntax(fasill)]),
        fasill_rule(head(term(close, [term(hydropolis, []), term(taxi, [])])), body(num(0.7)), [id(3), syntax(fasill)]),
        fasill_rule(head(term(good_hotel, [var('X')])), body(term(@aver, [term(elegant, [var('X')]), term(@very, [term(close, [var('X'), term(metro, [])])])])), [id(4), syntax(fasill)])
    ]
).