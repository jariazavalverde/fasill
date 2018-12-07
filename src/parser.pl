/**
  * 
  * FILENAME: parser.pl
  * DESCRIPTION: This module contains predicates for parsing FASILL programs.
  * AUTHORS: José Antonio Riaza Valverde
  * UPDATED: 07.12.2018
  * 
  **/



:- module(parser, [
    stream_to_list/2,
    escape_atom/2,
    file_program/2,
    file_query/2,
    file_testcases/2,
    parse_program/2,
    parse_query/2,
    parse_testcases/2
]).

:- use_module('environment').



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
    token_minus_identifier(_, Chars, []), !.
escape_atom(Atom, Escape) :-
    atom_concat('''', Atom, Atom1),
    atom_concat(Atom1, '''', Escape).


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



% CHARS OPERATIONS

% parse_program/2
% parse_program(+Chars, ?Program)
%
% This predicate parses a FASILL program ?Program
% from a list of characters +Chars.
parse_program(Input, Program) :-
    reset_rule_id,
    once(parse_program(Program, Input, [])).

% parse_query/2
% parse_query(+Chars, ?Program)
%
% This predicate parses a FASILL goal ?Goal
% from a list of characters +Chars.
parse_query(Input, Goal) :-
    reset_rule_id,
    once(parse_expr(1300, Goal, Input, ['.'])).

% parse_testcases/2
% parse_testcases(+Chars, ?Testcases)
%
% This predicate parses a set of testcases ?Testcases
% from a list of characters +Chars.
parse_testcases(Input, Testcases) :-
    parse_testcases(Testcases, Input, []).



% INITIAL OPERATOR TABLE

% current_op/4
% initial operator table
:- dynamic current_op/4.
current_op(1300, xfx, '#<',   yes).
current_op(1300, xfx, ':-',   no).
current_op(1300, xfx, '<-',   no).
current_op(1300, xfx, '->',   no).
current_op(1300, xfx, '<',    yes).
current_op(1200, xfx, 'with', no).
current_op(1100, xfy, '#|',   yes).
current_op(1100, xfy, '|',    yes).
current_op(1100, xfy, '|',    no).
current_op(1100, xfy, ';',    no).
current_op(1050, xfy, '#&',   yes).
current_op(1050, xfy, '&',    yes).
current_op(1050, xfy, '&',    no).
current_op(1050, xfy, ',',    no).
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



% GRAMMAR

% current_rule_id/1
% store the current identifier to be used in a rule
:- dynamic current_rule_id/1.
?- retractall(current_rule_id(_)).
current_rule_id(1).

% auto_rule_id/1
% update the current rule identifier and return it
auto_rule_id(Id) :- current_rule_id(Id), retract(current_rule_id(_)), N is Id+1, assertz(current_rule_id(N)).

% reset_rule_id/0
% reset the current rule identifier to the first
reset_rule_id :- retract(current_rule_id(_)), assertz(current_rule_id(1)).

% parse_program/3
% parse a fuzzy logic program
parse_program([H|T]) --> parse_rule(H), !, parse_program(T), blanks.
parse_program([]) --> [].

% parse_rule/3
% parse a malp or fasill rule
parse_rule(fasill_rule(head(Head), Body, [id(IdAtom),Info])) -->
    parse_expr(1300, T), dot,
    {( T = term(with, [Head, TD]), Body = body(TD), Info = syntax(malp) ;
       T = term('<-', [Head, term(with, [BodyWith,TD])]), Body = body(term('&', [TD,BodyWith])), Info = syntax(malp) ;
       T = term('<'(Implication), [Head, term(with, [BodyWith,TD])]), Body = body(term('&'(Implication), [TD,BodyWith])), Info = syntax(malp) ;
       T = term('<-', [Head,Body_]), Body = body(Body_), Info = syntax(fasill) ;
       T = term('<'(_), [Head,Body_]), Body = body(Body_), Info = syntax(malp) ;
       T = term('#<'(Implication), [Head, term(with, [BodyWith,TD])]), Body = body(term('#&'(Implication), [TD,BodyWith])), Info = syntax(smalp) ;
       T = term('#<'(_), [Head,Body_]), Body = body(Body_), Info = syntax(smalp) ;
       T = term(':-', [Head, Body_]), Body = body(Body_), Info = syntax(prolog) ;
       T = Head, Body = empty, Info = syntax(fasill)
    )}, !, {auto_rule_id(Id), atom_number(IdAtom, Id)}.

% parse_testcases/3
% parse_testcases(?Testcase, +Chars, ?Rest)
%
% This predicate parses the set of testcases ?Testcases
% from the input +Chars, leaving the characters ?Rest.
parse_testcases([H|T]) --> parse_testcase(H), !, parse_testcases(T), blanks.
parse_testcases([]) --> [].

% parse_testcase/3
% parse_testcase(?Testcase, +Chars, ?Rest)
%
% This predicate parses the testcase ?Testcase from
% the input +Chars, leaving the characters ?Rest.
parse_testcase(fasill_testcase(TD, Goal)) -->
    {current_fasill_flag(symbolic, Flag),
    set_fasill_flag(symbolic, false)},
    ( parse_expr(1300, Expr), dot,
      {Expr = term('->', [TD, Goal]),
        set_fasill_flag(symbolic, Flag)}, !
    ; {set_fasill_flag(symbolic, Flag), fail} ).

% parse_operator/6
% parse an operator T with Priority, Specifier and Name 
parse_operator(Priority, Specifier, T, Name) -->
    blanks, token_atom(Op), {current_op(Priority, Specifier, Op, Name)},
    ({Name = yes}, token_minus_identifier(Identifier), {T =.. [Op, Identifier]} ; 
        {current_op(Priority, Specifier, Op, no), T = Op}), !.

% next_priority/2
% give the next priority to derivate an expression
next_priority(1300, 1200).
next_priority(1200, 1100).
next_priority(1100, 1050).
next_priority(999, 700).
next_priority(1050, 700).
next_priority(700, 500).
next_priority(500, 400).
next_priority(400, 200).
next_priority(200, 0).

% parse_expr/4
% parse an expression with level between 0 and 1300
%%% level 0
parse_expr(0, X) --> blanks, parse_expr_zero(X).
%%% level n, n > 0
%%%%%% fx, fy
parse_expr(Priority, term(Op, [T])) --> {Priority > 0}, parse_operator(Priority, fy, Op, _), parse_expr(Priority, T).
parse_expr(Priority, term(Op, [T])) --> {Priority > 0}, parse_operator(Priority, fx, Op, _), {next_priority(Priority, Next)}, parse_expr(Next, T).
%%%%%% xfx, xfy, yfx
parse_expr(Priority, T) -->
    {Priority > 0, next_priority(Priority, Next)},
    parse_expr(Next, Left),
    (   {(Specifier = xfx, PriorityRight = Next ; Specifier = yfx, PriorityRight = Next ; Specifier = xfy, PriorityRight = Priority)},
        parse_operator(Priority, Specifier, Op, _),
        parse_expr(PriorityRight, Right),
        ({Specifier = yfx} -> parse_expr2(Priority, term(Op, [Left,Right]), T) ; {T = term(Op, [Left,Right])}), !
    ; {T = Left} ).
%%%%%% yfx
parse_expr2(Priority, Left, T) -->
    {Priority > 0, next_priority(Priority, Next)},
    parse_operator(Priority, yfx, Op, _),
    parse_expr(Next, Right),
    parse_expr2(Priority, term(Op, [Left,Right]), T).
parse_expr2(_, T, T) --> [].

parse_expr_zero(num(T)) --> token_number(T), !.
parse_expr_zero(str(T)) --> token_string(T), !.
parse_expr_zero(var(T)) --> token_variable(T), !.
parse_expr_zero(T) --> lparen, !, parse_expr(1300, T), rparen.
parse_expr_zero(T) --> parse_list(T), !.
parse_expr_zero(T) --> parse_brace(T), !.
parse_expr_zero(T) --> parse_agr(T), !.
parse_expr_zero(T) --> parse_term(T), !.

% parse_term/3
% parse a (possible compound) term
parse_term(term(Name, Args)) --> token_atom(Name), parse_term2(Args).
parse_term2([H|T]) --> lparen, !, parse_expr(999, H), parse_term3(T).
parse_term2([]) --> [].
parse_term3([H|T]) --> comma, !, parse_expr(999, H), parse_term3(T).
parse_term3([]) --> rparen.

% parse_agr/3
% parse an aggregator
parse_agr(term('#@'(Name), [H|T])) --> ['#','@'], token_atom(Name), lparen, parse_expr(999, H), parse_term3(T).
parse_agr(term('@'(Name), [H|T])) --> ['@'], token_atom(Name), lparen, parse_expr(999, H), parse_term3(T).

% parse_list/3
% parse a list
parse_list(T) --> lbracket, parse_list2(T).
parse_list2(term('[]', [])) --> rbracket.
parse_list2(term('.', [H,T])) --> parse_expr(999, H), parse_list3(T).
parse_list3(term('.', [H,T])) --> comma, parse_expr(999, H), parse_list3(T).
parse_list3(T) --> bar, parse_expr(999, T), rbracket.
parse_list3(term('[]', [])) --> rbracket.

% parse_brace/3
% parse a brace
parse_brace(term('{}', [T])) --> lbrace, parse_expr(999, T), blanks, rbrace, !.
parse_brace(term('{}', [])) --> lbrace, blanks, rbrace.



% TOKENS

% Identifiers
token_identifier(T) --> identifier(L), {atom_chars(T,L)}.
token_minus_identifier(T) --> minus(X), identifier(Xs), {atom_chars(T,[X|Xs])}.

identifier([H|T]) --> letter(H), !, identifier(T).
identifier([]) --> [].

minus(X) --> [X], {char_code(X,C), C >= 97, C =< 122}.
mayus(X) --> [X], {char_code(X,C), C >= 65, C =< 90}.
letter(X) --> minus(X).
letter(X) --> mayus(X).
letter(X) --> number(X).
letter('_') --> ['_'].

% Graphics
token_graphics(T) --> graphic(H), graphics(G), {atom_chars(T,[H|G])}.

graphics([H|T]) --> graphic(H), !, graphics(T).
graphics([]) --> [].
graphic(X) --> [X], {member(X,['.','|',',','=',';','#','$','&','*','+','-','/',':','<','>','?','^','~','\\'])}.

% Variables
token_variable(T) --> mayus(X), identifier(Xs), {atom_chars(T,[X|Xs])}.
token_variable(T) --> ['_'], identifier(Xs), {atom_chars(T,['_'|Xs])}.

% Numbers
token_number(N) --> ['0','x'], hexadecimals(H), {atom_chars(C,['0','x'|H]), atom_number(C,N)}.
token_number(N) --> ['0','b'], binaries(B), {atom_chars(C,['0','b'|B]), atom_number(C,N)}.
token_number(N) --> ['0','o'], octals(O), {atom_chars(C,['0','o'|O]), atom_number(C,N)}.
token_number(N) --> numbers(X), token_number2(Y), !, {append(X,Y,Z)}, {atom_chars(T,Z), atom_number(T,N)}.
token_number2(N) --> ['.'], numbers(X), !, token_number3(Y), {append(['.'|X],Y,N)}.
token_number2([]) --> [].
token_number3([e|X]) --> [e], numbers(X), !.
token_number3([e,'-'|X]) --> [e,'-'],!, numbers(X), !.
token_number3([]) --> [].

binary('0') --> ['0'].
binary('1') --> ['1'].
binaries([N|M]) --> binary(N), !, binaries(M).
binaries([]) --> [].

octal(X) --> [X], {char_code(X,C), C >= 48, C =< 55}.
octals([N|M]) --> octal(N), !, octals(M).
octals([]) --> [].

hexadecimal(X) --> [X], {member(X,['0','1','2','3','4','5','6','7','8','9','a','b','c','d','e','f','A','B','C','D','E','F'])}.
hexadecimals([N|M]) --> hexadecimal(N), !, hexadecimals(M).
hexadecimals([]) --> [].

number(X) --> [X], {char_code(X,C), C >= 48, C =< 57}.
numbers([N|M]) --> number(N), numbers(M), !.
numbers([N]) --> number(N).

% Strings
token_string(T) --> double_quote, double_quote_content(T), double_quote.
double_quote --> ['"'].
double_quote_content([X|Xs]) --> [X], {X \= '"'}, !, double_quote_content(Xs).
double_quote_content(['"'|Xs]) --> ['"','"'], !, double_quote_content(Xs).
double_quote_content(['"'|Xs]) --> ['\\','"'], !, double_quote_content(Xs).
double_quote_content(['\\'|Xs]) --> ['\\','\\'], !, double_quote_content(Xs).
double_quote_content([]) --> [].

% Atoms
token_atom('!') --> ['!'].
token_atom('#'(T)) --> ['#'], token_minus_identifier(T).
token_atom(T) --> quoted(Xs), {atom_chars(T,Xs)}.
token_atom(T) --> token_graphics(T).
token_atom(T) --> token_minus_identifier(T).

quoted(X) --> quote, quote_content(X), quote.
quote --> [''''].
quote_content([X|Xs]) --> [X], {X \= ''''}, !, quote_content(Xs).
quote_content([''''|Xs]) --> ['''',''''], !, quote_content(Xs).
quote_content([''''|Xs]) --> ['\\',''''], !, quote_content(Xs).
quote_content(['\\'|Xs]) --> ['\\','\\'], !, quote_content(Xs).
quote_content([]) --> [].

% Proper symbols
lbrace --> ['{'].
rbrace --> ['}'].
lparen --> ['('].
rparen --> blanks, [')'].
lbracket --> ['['].
rbracket --> blanks, [']'].
bar --> blanks, ['|'].
comma --> blanks, [','].
dot --> blanks, ['.'].

% Blanks
blanks --> blank, !, blanks.
blanks --> [].
blank --> [' '].
blank --> ['\n'].
blank --> ['\t'].