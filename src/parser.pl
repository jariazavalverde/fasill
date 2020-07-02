/**
  * 
  * FILENAME: parser.pl
  * DESCRIPTION: This module contains predicates for parsing FASILL programs.
  * AUTHORS: José Antonio Riaza Valverde
  * UPDATED: 15.06.2020
  * 
  **/



:- module(parser, [
    stream_to_list/2,
    escape_atom/2,
    file_program/2,
    file_query/2,
    file_similarity/2,
    file_testcases/2,
    parse_program/2,
    parse_query/2,
    parse_similarity/2,
    parse_testcases/2
]).

:- use_module('environment').
:- use_module('directives').
:- use_module('exceptions').



% UTILS

% stream_to_list/2
% stream_to_list(+Stream, ?List)
%
% This predicate succeeds when ?List is the lists
% of characters reads from the stream +Stream.
stream_to_list(Stream, []) :-
    at_end_of_stream(Stream), !.
stream_to_list(Stream, [Char|Input]) :-
    get_code(Stream, Code),
    char_code(Char, Code),
    stream_to_list(Stream, Input).

% escape_atom/2
% escape_atom(+Atom, ?Escape)
%
% This predicate succeeds when ?Escape is
% the escape sequence of the atom +Atom.
escape_atom(Atom, Atom) :-
    atom_chars(Atom, Chars),
    Chars \= [],
    string_lower_identifier(_, pos(1,0), _, Chars, []), !.
escape_atom(Atom, Escape) :-
    atom_concat('\'', Atom, Atom1),
    atom_concat(Atom1, '\'', Escape).



% FILE OPERATIONS

% file_program/2
% file_program(+Path, ?Program)
%
% This predicate succeeds when file +Path exists and
% it can be parsed as a FASILL program ?Program.
file_program(Path, Program) :-
    open(Path, read, Stream),
    stream_to_list(Stream, Input),
    close(Stream),
    parse_program(Input, Program).

% file_query/2
% file_query(+Path, ?Goal)
%
% This predicate succeeds when file +Path exists and
% it can be parsed as a FASILL goal ?Goal.
file_query(Path, Query) :-
    open(Path, read, Stream),
    stream_to_list(Stream, Input),
    close(Stream),
    parse_query(Input, Query).

% file_similarity/2
% file_similarity(+Path, ?Similarity)
%
% This predicate succeeds when file +Path exists and
% it can be parsed as a FASILL similarity scheme
% ?Similarity.
file_similarity(Path, Similarity) :-
    open(Path, read, Stream),
    stream_to_list(Stream, Input),
    close(Stream),
    parse_similarity(Input, Similarity).

% file_testcases/2
% file_testcases(+Path, ?Testcases)
%
% This predicate succeeds when file +Path exists and
% it can be parsed as a FASILL set of testcases ?Testcases.
file_testcases(Path, Testcases) :-
    open(Path, read, Stream),
    stream_to_list(Stream, Input),
    close(Stream),
    parse_testcases(Input, Testcases).



% PARSE OPERATIONS

% parse_program/2
% parse_program(+Chars, ?Program)
%
% This predicate parses a FASILL program ?Program
% from a list of characters +Chars.
parse_program(Input, Program) :-
    once(tokenizer(Tokens, pos(1,0), _, Input, [])),
    once(grammar_program(Program, _, Tokens, Rest)),
    (Rest == [token(_, _, _, pos(L,C), _)|_] -> syntax_error(L, C, 'unexpected token', Error), throw_exception(Error) ; true).

% parse_query/2
% parse_query(+Chars, ?Goal)
%
% This predicate parses a FASILL goal ?Goal
% from a list of characters +Chars.
parse_query(Input, Program) :-
    once(tokenizer(Tokens, pos(1,0), _, Input, [])),
    once(grammar_query(Program, _, Tokens, Rest)),
    (Rest == [token(_, _, _, pos(L,C), _)|_] -> syntax_error(L, C, 'unexpected token', Error), throw_exception(Error) ; true).

% parse_similarity/2
% parse_similarity(+Chars, ?Program)
%
% This predicate parses a FASILL similarity scheeme ?Scheme
% from a list of characters +Chars.
parse_similarity(Input, Scheme) :-
    once(tokenizer(Tokens, pos(1,0), _, Input, [])),
    once(grammar_similarity(Scheme, _, Tokens, Rest)),
    (Rest == [token(_, _, _, pos(L,C), _)|_] -> syntax_error(L, C, 'unexpected token', Error), throw_exception(Error) ; true).

% parse_testcases/2
% parse_testcases(+Chars, ?Testcases)
%
% This predicate parses a set of testcases ?Testcases
% from a list of characters +Chars.
parse_testcases(Input, Testcases) :-
    once(tokenizer(Tokens, pos(1,0), _, Input, [])),
    once(grammar_testcases(Testcases, _, Tokens, Rest)),
    (Rest == [token(_, _, _, pos(L,C), _)|_] -> syntax_error(L, C, 'unexpected token', Error), throw_exception(Error) ; true).



% INITIAL OPERATOR TABLE

% current_op/4
% Initial operator table.
:- dynamic current_op/4.
current_op(1300, xfx, '#<-',  yes).
current_op(1300, xfx, ':-',   no).
current_op(1300, xfx, '<-',   no).
current_op(1300, xfx, '->',   no).
current_op(1300, xfx, '<-',   yes).
current_op(1300, fx,  '<-',   no).
current_op(1300, fx,  ':-',   no).
current_op(1200, xfx, 'with', no).
current_op(1100, xfy, '#|',   yes).
current_op(1100, xfy, '|',    yes).
current_op(1100, xfy, '|',    no).
current_op(1100, xfy, ';',    no).
current_op(1000, xfy, '#&',   yes).
current_op(1000, xfy, '&',    yes).
current_op(1000, xfy, '&',    no).
current_op(1000, xfy, ',',    no).
current_op(700,  xfx, 'is',   no).
current_op(700,  xfx, '=',    no).
current_op(700,  xfx, '~',    no).
current_op(700,  xfx, '\\=',  no).
current_op(700,  xfx, '\\~',  no).
current_op(700,  xfx, '==',   no).
current_op(700,  xfx, '\\==', no).
current_op(700,  xfx, '@<',   no).
current_op(700,  xfx, '@>',   no).
current_op(700,  xfx, '@=<',  no).
current_op(700,  xfx, '@>=',  no).
current_op(700,  xfx, '<',    no).
current_op(700,  xfx, '>',    no).
current_op(700,  xfx, '=<',   no).
current_op(700,  xfx, '>=',   no).
current_op(700,  xfx, '=..',  no).
current_op(700,  xfx, '=:=',  no).
current_op(700,  xfx, '=\\=', no).
current_op(500,  yfx, '+',    no).
current_op(500,  yfx, '-',    no).
current_op(400,  yfx, '*',    no).
current_op(400,  yfx, '/',    no).
current_op(400,  yfx, '//',   no).
current_op(400,  yfx, 'rem',  no).
current_op(400,  yfx, 'mod',  no).
current_op(200,  xfx, '**',   no).
current_op(200,  xfy, '^',    no).
current_op(200,  xfy, '^^',   no).
current_op(200,  fy,  '+',    no).
current_op(200,  fy,  '-',    no).
current_op(200,  fx,  ':',    no).

% next_priority/2
% Gives the next priority to derivate an expression.
next_priority(1300, 1200).
next_priority(1200, 1100).
next_priority(1100, 1000).
next_priority(1000, 700).
next_priority(999, 700).
next_priority(700, 500).
next_priority(500, 400).
next_priority(400, 200).
next_priority(200, 0).

% max_priority/1
% Gives the higher priority to derivate an expression.
max_priority(0) :- environment:current_fasill_flag(operators, term(false,[])), !.
max_priority(1300).



% GRAMMAR

% current_rule_id/1
% store the current identifier to be used in a rule
:- dynamic current_rule_id/1.
?- retractall(current_rule_id(_)).
current_rule_id(1).

% reset_rule_id/0
% reset the current rule identifier to the first
reset_rule_id :- retract(current_rule_id(_)), assertz(current_rule_id(1)).

% auto_rule_id/1
% update the current rule identifier and return it
auto_rule_id(Id) :- current_rule_id(Id), retract(current_rule_id(_)), succ(Id, N), assertz(current_rule_id(N)).

% grammar_program/4
% Parses a fuzzy logic program.
grammar_program([H|T], P) --> grammar_rule(H, _), !, grammar_program(T, P).
grammar_program([], _) --> [].

% grammar_query/4
% Parses a fuzzy logic goal.
grammar_query(T, P) -->
    ({max_priority(MP)}, grammar_expression(MP, T, pos(L,C)), ! ; {syntax_error(1, 0, 'expression expected', Error), throw_exception(Error)}),
    (grammar_dot(P), ! ; {syntax_error(L, C, 'point or operator expected', Error), throw_exception(Error)}).

% parse_rule/4
% Parses a MALP or FASILL rule.
grammar_rule(fasill_rule(head(Head), Body, [id(IdAtom),Info]), P) -->
    {max_priority(MP)}, grammar_expression(MP, T, pos(L,C)), (grammar_dot(P), ! ; {syntax_error(L, C, 'point or operator expected', Error), throw_exception(Error)}),
    {(
       % rule
       T = term(with, [Head, TD]), Body = body(TD), Info = syntax(malp) ;
       T = term('<-', [Head, term(with, [BodyWith,TD])]), Body = body(term('&', [TD,BodyWith])), Info = syntax(malp) ;
       T = term('<-'(Implication), [Head, term(with, [BodyWith,TD])]), Body = body(term('&'(Implication), [TD,BodyWith])), Info = syntax(malp) ;
       T = term('<-', [Head,Body_]), Body = body(Body_), Info = syntax(fasill) ;
       T = term('<-'(_), [Head,Body_]), Body = body(Body_), Info = syntax(malp) ;
       T = term('#<-'(Implication), [Head, term(with, [BodyWith,TD])]), Body = body(term('#&'(Implication), [TD,BodyWith])), Info = syntax(smalp) ;
       T = term('#<-'(_), [Head,Body_]), Body = body(Body_), Info = syntax(smalp) ;
       T = term(':-', [Head, Body_]), Body = body(Body_), Info = syntax(prolog) ;
       % directive
       T = term(':-', [Directive]), eval_directive(Directive), T = Head, Body = empty, Info = directive ;
       T = term('<-', [Directive]), eval_directive(Directive), T = Head, Body = empty, Info = directive ;
       % fact
       T = Head, Body = empty, Info = syntax(fasill)
    )}, !, {auto_rule_id(Id), atom_number(IdAtom, Id)}.

% grammar_similarity/4
% Parses a FASILL similarity scheme.
grammar_similarity([H|T], P) --> grammar_similarity_equation(H, _), !, grammar_similarity(T, P).
grammar_similarity([], _) --> [].

% grammar_similarity_equation/4
% Parses a FASILL similarity equation.
%%% tnorm/tconorm
grammar_similarity_equation(Eq, P) -->
    [token(atom, '~', ['~'], pos(L0,C0), _)], !,
    (
        [token(atom, 'tnorm', [t,n,o,r,m], pos(L1,C1), _)], {Type = tnorm, Label = '&'}, ! ;
        [token(atom, 'tconorm', [t,c,o,n,o,r,m], pos(L1,C1), _)], {Type = tconorm, Label = '|'}, ! ;
        {syntax_error(L0, C0, 'tnorm or tconorm expected', Error), throw_exception(Error)}),
    ([token(atom, '=', ['='], pos(L3,C3), _)], ! ; {syntax_error(L1, C1, 'equal symbol expected', Error), throw_exception(Error)}),
    ([token(atom, '#', ['#'], pos(L4,C4), _)], {atom_concat('#', Label, Label2)}, ! ; {Label = Label2, L4 = L3, C4 = C3}),
    ([token(atom, Norm, _, pos(L5,C5), _)], ! ; {syntax_error(L4, C4, 'atom expected', Error), throw_exception(Error)}),
    (grammar_dot(P), ! ; {syntax_error(L5, C5, 'point or operator expected', Error), throw_exception(Error)}),
    {atom_concat('fasill_similarity_', Type, Pred), Con =.. [Label2, Norm], Eq =.. [Pred, Con]}, !.
%%% similarity equation
grammar_similarity_equation(fasill_similarity(Q/N, R/M, TD, Sym), P) -->
    [token(atom, Q, _, pos(L0,C0), _)],
    ([token(atom, '/', ['/'], pos(L1,C1), _)] ->
        ([token(number, N, _, pos(L2,C2), _)], ! ; {syntax_error(L1, C1, 'arity expected after / symbol', Error), throw_exception(Error)});
        {N = 0, L2 = L0, C2 = C0}
    ),
    ([token(atom, '~', ['~'], pos(L3,C3), _)], ! ; {syntax_error(L2, C2, '~ symbol expected', Error), throw_exception(Error)}),
    ([token(atom, R, _, pos(L4,C4), _)], ! ; {syntax_error(L3, C3, 'atom expected', Error), throw_exception(Error)}),
    ([token(atom, '/', ['/'], pos(L5,C5), _)] ->
        ([token(number, M, _, pos(L6,C6), _)], ! ; {syntax_error(L5, C5, 'arity expected after / symbol', Error), throw_exception(Error)});
        {M = 0, L6 = L4, C6 = C4}
    ),
    {(integer(N), N >= 0) -> true ; syntax_error(L1, C1, 'arity must be a non-negative integer', Error), throw_exception(Error)},
    {(integer(M), M >= 0) -> true ; syntax_error(L5, C5, 'arity must be a non-negative integer', Error), throw_exception(Error)},
    ([token(atom, '=', ['='], pos(L7,C7), _)], ! ; {syntax_error(L6, C6, 'equal symbol expected', Error), throw_exception(Error)}),
    ({max_priority(MP)}, grammar_expression(MP, TD, pos(L8,C8)), {TD = term('#'(_), []) -> Sym = yes ; Sym = no}, ! ; {syntax_error(L7, C7, 'point or operator expected', Error), throw_exception(Error)}),
    (grammar_dot(P), ! ; {syntax_error(L8, C8, 'point or operator expected', Error), throw_exception(Error)}).

% grammar_testcases/4
% Parses a FASILL set of testcases.
grammar_testcases([H|T], P) --> grammar_testcase(H, _), !, grammar_testcases(T, P).
grammar_testcases([], _) --> [].

% grammar_testcase/4
% Parses a FASILL testcase.
grammar_testcase(Test, P) -->
    {max_priority(MP)}, grammar_expression(MP, T, pos(L,C)),
    (grammar_dot(P), ! ; {syntax_error(L, C, 'point or operator expected', Error), throw_exception(Error)}),
    ({T = term('->', [TD, Goal]) -> Test = fasill_testcase(TD, Goal) ; Test = fasill_testcase_precondition(T)}).

% grammar_operator/7
% Parses an operator T with Priority, Specifier and Name.
%%% labeled
grammar_operator(Priority, Specifier, Op, yes, P) -->
    [token(atom, T, [C1|_], _, false), token(atom, Label, [C2|_], P, _)],
    {C1 \= '\'', C2 \= '\'', Op =.. [T,Label],
    current_op(Priority, Specifier, T, yes)}.
%%% unlabeled
grammar_operator(Priority, Specifier, T, no, P) -->
    [token(atom, T, [C|_], P, _)],
    {C \= '\'', current_op(Priority, Specifier, T, no)}.

% grammar_expression/5
% Parses an expression with level between 0 and 1300.
%%% level 0
grammar_expression(0, X, P) --> grammar_expression_zero(X, P).
%%% level n, n > 0
%%%%%% fx, fy
grammar_expression(Priority, Q, P) -->
    {Priority > 0, member(F, [fx, fy])},
    grammar_operator(Priority, F, Op, _, pos(L,C)),
    ({F = fy} -> {Next = Priority} ; {next_priority(Priority, Next)}),
    (grammar_expression(Next, T, P), ! ; {syntax_error(L, C, 'expression expected', Error), throw_exception(Error)}),
    {(Op = '-', T = num(X)) -> (Y is -X, Q = num(Y)) ; (Q = term(Op, [T]))}.
%%%%%% xfx, xfy, yfx
grammar_expression(Priority, T, P1) -->
    {Priority > 0, next_priority(Priority, Next)},
    grammar_expression(Next, Left, Pe),
    (   {member((Specifier,PriorityRight), [(xfx,Next), (yfx,Next), (xfy,Priority)])},
        grammar_operator(Priority, Specifier, Op, _, pos(L,C)),
        (grammar_expression(PriorityRight, Right, P0), ! ; {syntax_error(L, C, 'expression expected', Error), throw_exception(Error)}),
        ({Specifier = yfx} -> grammar_expression2(Priority, term(Op, [Left,Right]), T, P0, P1) ; {T = term(Op, [Left,Right]), P1 = P0}), !
    ; {T = Left, P1 = Pe} ).
%%%%%% yfx
grammar_expression2(Priority, Left, T, P0, P1) -->
    {Priority > 0, next_priority(Priority, Next)},
    grammar_operator(Priority, yfx, Op, _, pos(L,C)),
    (grammar_expression(Next, Right, P0), ! ; {syntax_error(L, C, 'expression expected', Error), throw_exception(Error)}),
    grammar_expression2(Priority, term(Op, [Left,Right]), T, P0, P1).
grammar_expression2(_, T, T, P, P) --> [].

grammar_expression_zero(num(T), P) --> [token(number, T, _, P, _)], !.
%grammar_expression_zero(T) --> token_string(T), !.
grammar_expression_zero(var(T), P) --> [token(variable, T, _, P, _)], !.
grammar_expression_zero(T, P) -->
    [token(lparen, _, _, _, _)], !,
    {max_priority(MP)}, grammar_expression(MP, T, pos(L,C)),
    ([token(rparen, _, _, P, _)], ! ; {syntax_error(L, C, 'operator or right parenthesis expected', Error), throw_exception(Error)}).
grammar_expression_zero(T, P) --> grammar_list(T, P), !.
grammar_expression_zero(T, P) --> grammar_brace(T, P), !.
grammar_expression_zero(T, P) --> grammar_symbolic_constant(T, P), !.
grammar_expression_zero(T, P) --> grammar_connective(T, P), !.
grammar_expression_zero(T, P) --> grammar_term(T, P), !.

% grammar_symbolic_constant/4
% Parses a symbolic constant.
grammar_symbolic_constant(term('#'(Name), []), P) -->
    [token(atom, '#', ['#'], _, false)],
    [token(atom, Name, [C|_], P, _)].

% grammar_term/4
% Parses a (possible compound) term.
grammar_term(term(Name, []), P) --> [token(atom, Name, _, P, _)], \+[token(lparen, _, _, _, _)], !.
grammar_term(term(Name, []), P) --> [token(atom, Name, _, P, true)], !.
grammar_term(term(Name, [X|Xs]), P1) -->
    [token(atom, Name, _, _, false), token(lparen, _, _, pos(L,C), _)], !,
    (grammar_expression(999, X, P0), ! ; {syntax_error(L, C, 'expression expected', Error), throw_exception(Error)}),
    grammar_term_args(Xs, P0, P1).
grammar_term_args([X|Xs], _, P1) -->
    [token(atom, ',', [Char|_], pos(L,C), _)], {Char \= '\''}, !,
    (grammar_expression(999, X, P0), ! ; {syntax_error(L, C, 'expression expected', Error), throw_exception(Error)}),
    grammar_term_args(Xs, P0, P1).
grammar_term_args([], pos(L,C), P1) -->
    ([token(rparen, _, _, P1, _)], ! ; {syntax_error(L, C, 'operator or right parenthesis expected', Error), throw_exception(Error)}).

% grammar_connective/4
% Parses a prefix connective.
grammar_connective(term(Con, [X|Xs]), P1) -->
    [token(atom, Type, [C1|_], _, false)], {C1 \= '\''},
    {member(Type, ['@','&','|','#@','#&','#|', '#?'])},
    [token(atom, Name, [C2|_], _, false)], {C2 \= '\''},
    [token(lparen, _, _, _, _)],
    grammar_expression(999, X, P0),
    grammar_term_args(Xs, P0, P1),
    {Con =.. [Type,Name]}.

% grammar_list/4
% Parses a (possible empty) list.
grammar_list(T, P1) -->
    [token(lbracket, _, _, P0, _)],
    grammar_list_first(T, P0, P1).
grammar_list_first(term('.', [X,Xs]), _, P1) -->
    grammar_expression(999, X, P0), !,
    grammar_list_args(Xs, P0, P1).
grammar_list_first(term('[]', []), pos(L,C), P) -->
    [token(rbracket, _, _, P, _)], ! ; {syntax_error(L, C, 'operator or right bracket expected', Error), throw_exception(Error)}.
grammar_list_args(term('.', [X,Xs]), _, P1) -->
    [token(atom, ',', [Char|_], pos(L,C), _)], {Char \= '\''}, !,
    (grammar_expression(999, X, P0), ! ; {syntax_error(L, C, 'expression expected', Error), throw_exception(Error)}),
    grammar_list_args(Xs, P0, P1).
grammar_list_args(T, _, P) -->
    [token(atom, '|', [Char|_], pos(L1,C1), _)], {Char \= '\''}, !,
    (grammar_expression(999, T, pos(L2,C2)), ! ; {syntax_error(L1, C1, 'expression expected', Error), throw_exception(Error)}),
    ([token(rbracket, _, _, P, _)], ! ; {syntax_error(L2, C2, 'operator or right bracket expected', Error), throw_exception(Error)}).
grammar_list_args(term('[]', []), pos(L,C), P) -->
    [token(rbracket, _, _, P, _)], ! ; {syntax_error(L, C, 'operator or right bracket expected', Error), throw_exception(Error)}.

% grammar_brace/4
% Parses a braced expression.
grammar_brace(term('{}', [T]), P) -->
    [token(lbrace, _, _, _, _)],
    {max_priority(MP)}, grammar_expression(MP, T, pos(L,C)), !,
    ([token(rbrace, _, _, P, _)], ! ; {syntax_error(L, C, 'expression or right brace expected', Error), throw_exception(Error)}).
grammar_brace(term('{}', []), P) -->
    [token(lbrace, _, _, pos(L,C), _)],
    ([token(rbrace, _, _, P, _)], ! ; {syntax_error(L, C, 'expression or right brace expected', Error), throw_exception(Error)}).

% grammar_dot/3
% Parses a dot.
grammar_dot(P) --> [token(atom, '.', ['.'], P, _)].

% grammar_comma/3
% Parses a comma.
grammar_comma(P) --> [token(atom, ',', [','], P, _)].



% COMBINATORS

% 0 or more times.
many(R, [X|Xs], P0, P2) --> call(R, X, P0, P1), !, many(R, Xs, P1, P2).
many(_, [], P, P) --> [].

% 1 or more times.
some(R, Xs, P0, P1) --> many(R, Xs, P0, P1), {Xs \= []}.



% CHARS

% Character.
char_eq('\n', pos(L0,_), pos(L1,0)) --> ['\n'], !, {succ(L0, L1)}.
char_eq(X, pos(L,C0), pos(L,C1)) --> [X], {succ(C0, C1)}.

% Binary character.
char_binary('0', pos(L,C0), pos(L,C1)) --> ['0'], {succ(C0, C1)}.
char_binary('1', pos(L,C0), pos(L,C1)) --> ['1'], {succ(C0, C1)}.

% Octal character.
char_octal(X, pos(L,C0), pos(L,C1)) --> [X], {char_code(X, C), C >= 48, C =< 55, succ(C0, C1)}.

% Hexadecimal character.
char_hexadecimal(X, pos(L,C0), pos(L,C1)) --> [X],
    {member(X, ['0','1','2','3','4','5','6','7','8','9','a','b','c','d','e','f','A','B','C','D','E','F']),
    succ(C0, C1)}.

% Numeral character.
char_number(X, pos(L,C0), pos(L,C1)) --> [X], {char_code(X, C), C >= 48, C =< 57, succ(C0, C1)}.

% Lowercase character.
char_lower(X, pos(L,C0), pos(L,C1)) --> [X], {char_code(X,C), C >= 97, C =< 122, succ(C0, C1)}.

% Uppercase character.
char_upper(X, pos(L,C0), pos(L,C1)) --> [X], {char_code(X,C), C >= 65, C =< 90, succ(C0, C1)}.

% Graphic character.
char_graphic(X, P0, P1) --> char_eq(X, P0, P1), {member(X, ['.','|','=',';','#','$','&','@','*','+','-','/',':','<','>','?','^','~','\\'])}.

% Identifier character.
char_identifier(X, P0, P1) --> char_lower(X, P0, P1).
char_identifier(X, P0, P1) --> char_upper(X, P0, P1).
char_identifier(X, P0, P1) --> char_number(X, P0, P1).
char_identifier('_', pos(L,C0), pos(L,C1)) --> ['_'], {succ(C0, C1)}.

% Blank character.
char_blank(pos(L,C0), pos(L,C1)) --> [' '], {succ(C0, C1)}.
char_blank(pos(L0,_), pos(L1,0)) --> ['\n'], {succ(L0, L1)}.
char_blank(pos(L,C0), pos(L,C1)) --> ['\t'], {succ(C0, C1)}.



% STRINGS

% String.
string_eq([X|Xs], P0, P2) --> char_eq(X, P0, P1), string_eq(Xs, P1, P2).
string_eq([], P, P) --> [].

% Numeral string.
string_number(Z, P0, P2) -->
    some(char_number, X, P0, P1),
    string_number_decimal(Y, P1, P2), !,
    {append(X, Y, Z)}.
string_number_decimal(N, pos(L,C0), P2) -->
    ['.'], {succ(C0, C1)},
    some(char_number, X, pos(L,C1), P1), !,
    token_number_exponent(Y, P1, P2),
    {append(['.'|X], Y, N)}.
string_number_decimal(X, P0, P1) -->
    token_number_exponent(X, P0, P1).
token_number_exponent([e,S|X], pos(L,C0), P1) -->
    [e,S], {member(S, ['-','+']), C1 is C0+2}, !,
    some(char_number, X, pos(L,C1), P1).
token_number_exponent([e|X], pos(L,C0), P1) -->
    [e], {succ(C0, C1)},
    some(char_number, X, pos(L,C1), P1).
token_number_exponent([], P, P) --> [].

% String lower identifier.
string_lower_identifier([X|Xs], P0, P2) -->
    char_lower(X, P0, P1),
    many(char_identifier, Xs, P1, P2).

% String upper identifier.
string_lower_identifier([X|Xs], P0, P2) -->
    char_upper(X, P0, P1),
    many(char_identifier, Xs, P1, P2).

% String single quoted.
string_single_quoted(['\''|Xs], pos(L,C), P2) -->
    ['\'','\''], {C1 is C+2, P1 = pos(L,C1)},
    string_single_quoted(Xs, P1, P2).
string_single_quoted(['\''|Xs], pos(L,C), P2) -->
    ['\\','\''], {C1 is C+2, P1 = pos(L,C1)},
    string_single_quoted(Xs, P1, P2).
string_single_quoted([X|Xs], pos(L,C), P2) -->
    [X], {X \= '\'', (X == '\n' -> succ(L,L1), P1 = pos(L1,0) ; succ(C,C1), P1 = pos(L,C1))}, !,
    string_single_quoted(Xs, P1, P2).
string_single_quoted([], P, P) --> [].

% Blank strings.
string_blank(pos(L,C), P3) -->
    ['%'], {succ(C,C1), P1 = pos(L,C1)},
    string_blank_line(P1, P2),
    string_blank(P2, P3).
string_blank(pos(L,C), P4) -->
    ['/','%'], {C1 is C+2, P1 = pos(L,C1)},
    string_blank_multiline(P1, P2),
    string_eq(['*','/'], P2, P3),
    string_blank(P3, P4).
string_blank(P0, P2) -->
    char_blank(P0, P1), !,
    string_blank(P1, P2).
string_blank(P, P) --> [].

% Comment (line).
string_blank_line(P0, P2) --> char_eq(X, P0, P1), {X \= '\n'}, !, string_blank_line(P1, P2).
string_blank_line(P0, P1) --> char_eq('\n', P0, P1), !.
string_blank_line(P, P) --> [].

% Comment (multiline).
string_blank_multiline(P0, P2) --> char_eq(X, P0, P1), {X \= '*'}, !, string_blank_multiline(P1, P2).
string_blank_multiline(P0, P3) --> char_eq('*', P0, P1), char_eq(X, P1, P2), {X \= '/'}, !, string_blank_multiline(P2, P3).
string_blank_multiline(P, P) --> [].



% TOKENS

% Tokenize a sequence of characters.
tokenizer(Ts, P0, P2) --> string_blank(P0, P1), many(token_blanks, Ts, P1, P2).

% Tokens with blanks.
token_blanks(Tb, P0, P2) -->
    token(T, P0, P1),
    string_blank(P1, P2),
    {T =.. [token,A,B,C,D],
    (P1 == P2 -> Tb =.. [token,A,B,C,D,false]; Tb =.. [token,A,B,C,D,true])}.

% Tokens.
token(T, P0, P1) --> token_variable(T, P0, P1), !.
token(T, P0, P1) --> token_number(T, P0, P1), !.
token(T, P0, P1) --> token_atom(T, P0, P1), !.
token(T, P0, P1) --> token_symbol(T, P0, P1), !.
token(X, pos(L,C), P1) -->
    char_eq(X, pos(L,C), P1),
    {atom_concat('unexpected input ', X, Msg),
    syntax_error(L, C, Msg, Error),
    throw_exception(Error)}.

% Variable.
token_variable(token(variable, V, ['_'|Xs], P2), P0, P2) -->
    char_eq('_', P0, P1),
    many(char_identifier, Xs, P1, P2),
    {atom_chars(V, ['_'|Xs])}.
token_variable(token(variable, V, [X|Xs], P2), P0, P2) -->
    char_upper(X, P0, P1),
    many(char_identifier, Xs, P1, P2),
    {atom_chars(V, [X|Xs])}.

% Binary number.
token_number(token(number, N, ['0','b'|H], P2), pos(L,C), P2) -->
    ['0','b'], {C1 is C+2, P1 = pos(L,C1)},
    some(char_binary, H, P1, P2),
    {atom_chars(C, ['0','b'|H]), atom_number(C, N)}.

% Octal number.
token_number(token(number, N, ['0','o'|H], P2), pos(L,C), P2) -->
    ['0','o'], {C1 is C+2, P1 = pos(L,C1)},
    some(char_octal, H, P1, P2),
    {atom_chars(C, ['0','o'|H]), atom_number(C, N)}.

% Hexadecimal number.
token_number(token(number, N, ['0','x'|H], P2), pos(L,C), P2) -->
    ['0','x'], {C1 is C+2, P1 = pos(L,C1)},
    some(char_hexadecimal, H, P1, P2),
    {atom_chars(C, ['0','x'|H]), atom_number(C, N)}.

% Integer and decimal number.
token_number(token(number, N, C, P1), P0, P1) --> 
    string_number(S, P0, P1),
    {atom_chars(C, S), atom_number(C, N)}.

% Atom cut !.
token_atom(token(atom, '!', ['!'], pos(L,C1)), pos(L,C), pos(L,C1)) -->
    ['!'], {succ(C,C1)}.

% Atom comma ,.
token_atom(token(atom, ',', [','], pos(L,C1)), pos(L,C), pos(L,C1)) -->
    [','], {succ(C,C1)}.

% Graphic atom.
token_atom(token(atom, A, T, P1), P0, P1) -->
    some(char_graphic, T, P0, P1),
    {atom_chars(A, T)}.

% Quoted atom.
token_atom(token(atom, A, ['\''|Xs], P3), P0, P3) -->
    char_eq('\'', P0, P1),
    string_single_quoted(T, P1, P2),
    char_eq('\'', P2, P3),
    {append(T, '\'', Xs), atom_chars(A, T)}.

% Regular atom.
token_atom(token(atom, A, T, P1), P0, P1) -->
    string_lower_identifier(T, P0, P1),
    {atom_chars(A, T)}.

% Proper symbols.
token_symbol(token(lbrace, '{', ['{'], pos(L,C1)), pos(L,C), pos(L,C1)) --> ['{'], {succ(C,C1)}.
token_symbol(token(rbrace, '}', ['}'], pos(L,C1)), pos(L,C), pos(L,C1)) --> ['}'], {succ(C,C1)}.
token_symbol(token(lparen, '(', ['('], pos(L,C1)), pos(L,C), pos(L,C1)) --> ['('], {succ(C,C1)}.
token_symbol(token(rparen, ')', [')'], pos(L,C1)), pos(L,C), pos(L,C1)) --> [')'], {succ(C,C1)}.
token_symbol(token(lbracket, '[', ['['], pos(L,C1)), pos(L,C), pos(L,C1)) --> ['['], {succ(C,C1)}.
token_symbol(token(rbracket, ']', [']'], pos(L,C1)), pos(L,C), pos(L,C1)) --> [']'], {succ(C,C1)}.