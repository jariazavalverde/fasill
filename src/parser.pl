/**
  * 
  * FILENAME: parser.pl
  * DESCRIPTION: This module contains predicates for parsing FASILL programs.
  * AUTHORS: José Antonio Riaza Valverde
  * UPDATED: 18.02.2020
  * 
  **/



:- module(parser, [
    stream_to_list/2,
    escape_atom/2,
    file_program/2,
    file_similarity/2,
    file_query/2,
    file_testcases/2,
    parse_program/2,
    parse_similarity/2,
    parse_query/2,
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
    reset_line,
    reset_column,
    catch(
        once(parse_program(Program, Input, [])),
        Exception,
        (current_line(L), current_column(C), syntax_error(L, C, Exception, Error), throw_exception(Error))
    ).

% parse_similarity/2
% parse_similarity(+Chars, ?Similarity)
%
% This predicate parses a FASILL similarity scheme
% ?Similarity from a list of characters +Chars.
parse_similarity(Input, Program) :-
    reset_line,
    reset_column,
    catch(
        once(parse_similarity(Program, Input, [])),
        Exception,
        (current_line(L), current_column(C), syntax_error(L, C, Exception, Error), throw_exception(Error))
    ).

% parse_query/2
% parse_query(+Chars, ?Program)
%
% This predicate parses a FASILL goal ?Goal
% from a list of characters +Chars.
parse_query(Input, Goal) :-
    parse_query(Input, Goal, 1, 1).
parse_query(Input, Goal2, Line, Column) :-
    retract(current_line(_)),
    retract(current_column(_)),
    asserta(current_line(Line)),
    asserta(current_column(Column)),
    catch(
        once((blanks(Input, Input2), parse_expr(1300, Goal, Input2, R1), (dot(R1, R2), ! ; throw('point or operator expected')))),
        Exception,
        (current_line(L), current_column(C), syntax_error(L, C, Exception, Error), throw_exception(Error))
    ),
    current_line(L), current_column(C),
    (R2 = [] -> Goal2 = Goal ; (Goal2 = Goal ; parse_query(R2, Goal2, L, C))).

% parse_testcases/2
% parse_testcases(+Chars, ?Testcases)
%
% This predicate parses a set of testcases ?Testcases
% from a list of characters +Chars.
parse_testcases(Input, Testcases) :-
    reset_line,
    reset_column,
    catch(
        once(parse_testcases(Testcases, Input, [])),
        Exception,
        (current_line(L), current_column(C), syntax_error(L, C, Exception, Error), throw_exception(Error))
    ).



% INITIAL OPERATOR TABLE

% current_op/4
% initial operator table
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



% GRAMMAR

% current_line/1
% store the current line to be analyzed
:- dynamic current_line/1.
?- retractall(current_line(_)).
current_line(1).

% current_column/1
% store the current column to be analyzed
:- dynamic current_column/1.
?- retractall(current_column(_)).
current_column(1).

% current_rule_id/1
% store the current identifier to be used in a rule
:- dynamic current_rule_id/1.
?- retractall(current_rule_id(_)).
current_rule_id(1).

% auto_line/0
% update the current line
auto_line :- current_line(M), retract(current_line(_)), succ(M, N), assertz(current_line(N)), reset_column.

% auto_column/0
% update the current column
auto_column :- current_column(M), retract(current_column(_)), succ(M, N), assertz(current_column(N)).

% auto_column/1
% update the current column
auto_column(X) :- current_column(M), retract(current_column(_)), N is M+X, assertz(current_column(N)).

% auto_rule_id/1
% update the current rule identifier and return it
auto_rule_id(Id) :- current_rule_id(Id), retract(current_rule_id(_)), succ(Id, N), assertz(current_rule_id(N)).

% reset_line/0
% reset the current line to be analyzed to the first
reset_line :- retract(current_line(_)), assertz(current_line(1)).

% reset_column/0
% reset the current column to be analyzed to the first
reset_column :- retract(current_column(_)), assertz(current_column(1)).

% reset_rule_id/0
% reset the current rule identifier to the first
reset_rule_id :- retract(current_rule_id(_)), assertz(current_rule_id(1)).

% parse_program/3
% parse a fuzzy logic program
parse_program(Program) --> blanks, parse_program2(Program).
parse_program2([H|T]) --> blanks, parse_rule(H), !, parse_program2(T).
parse_program2([]) --> [].

% parse_rule/3
% parse a malp or fasill rule
parse_rule(fasill_rule(head(Head), Body, [id(IdAtom),Info])) -->
    parse_expr(1300, T), (dot, ! ; {throw('point or operator expected')}),
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

% parse_similarity/3
% parse a fasill similarity scheme
parse_similarity([H|T]) --> blanks, parse_similarity_equation(H), !, parse_similarity(T).
parse_similarity([]) --> [].

% parse_similarity_equation/3
% parse a fasill similarity equation
parse_similarity_equation(Eq) -->
    ['~'], !, {auto_column}, blanks,
    (
        [t,n,o,r,m], {Type = tnorm, Label = '&', auto_column(5)}, ! ;
        [t,c,o,n,o,r,m], {Type = tconorm, Label = '|', auto_column(7)}, ! ;
        {throw('tnorm or tconorm expected')}),
    blanks, (['='], {auto_column}, ! ; {throw('equal expected')}),
    blanks, (['#'], !, {auto_column(1), atom_concat('#', Label, Label2)} ; {Label = Label2}),
    blanks, (token_atom(Norm), ! ; {throw('atom expected')}),
    blanks, (dot, ! ; {throw('point or operator expected')}),
    {atom_concat('fasill_similarity_', Type, Pred), Con =.. [Label2, Norm], Eq =.. [Pred, Con]}, !.
parse_similarity_equation(fasill_similarity(P/N, Q/N, TD, Sym)) -->
    token_atom(P), blanks,
    (['/'], {auto_column}, !, blanks, (token_number(N), ! ; {throw('arity expected after /')}) ; {N = 0}), blanks,
    (['~'], {auto_column}, ! ; {throw('~ expected')}), blanks,
    (token_atom(Q), ! ; {throw('atom expected')}), blanks,
    (['/'], {auto_column}, !, blanks, (token_number(M), ! ; {throw('arity expected after /')}) ; {M = 0}), blanks,
    {N = M -> true ; throw('arities should be equal')},
    {(integer(N), N >= 0) -> true ; throw('arities should be non-negative integers')},
    (['='], {auto_column}, ! ; {throw('equal expected')}), blanks,
    parse_expr(1300, TD), {TD = term('#'(_), []) -> Sym = yes ; Sym = no}, blanks,
    (dot, ! ; {throw('point or operator expected')}).

% parse_testcases/3
% parse_testcases(?Testcase, +Chars, ?Rest)
%
% This predicate parses the set of testcases ?Testcases
% from the input +Chars, leaving the characters ?Rest.
parse_testcases(T) --> blanks, parse_testcases2(T).
parse_testcases2([H|T]) --> parse_testcase(H), !, parse_testcases2(T).
parse_testcases2([]) --> [].

% parse_testcase/3
% parse_testcase(?Testcase, +Chars, ?Rest)
%
% This predicate parses the testcase ?Testcase from
% the input +Chars, leaving the characters ?Rest.
parse_testcase(Test) -->
    ( parse_expr(1300, Expr), (dot, ! ; {throw('point or operator expected')}),
      {Expr = term('->', [TD, Goal]), Test = fasill_testcase(TD, Goal), !
    ; Test = fasill_testcase_precondition(Expr)} ).

% parse_operator/6
% parse an operator T with Priority, Specifier and Name 
parse_operator(Priority, Specifier, T, yes) -->
    {current_line(L), current_column(C)},
    token_atom(Op), ((
        {current_op(Priority, Specifier, Op, yes)},
        token_minus_identifier(Identifier)
    ) -> {T =.. [Op, Identifier]} ; {
        retract(current_line(_)), retract(current_column(_)),
        asserta(current_line(L)), asserta(current_column(C)), fail
    }), blanks, !.
parse_operator(Priority, Specifier, Op, no) -->
    {current_line(L), current_column(C)},
    token_atom(Op), {current_op(Priority, Specifier, Op, no) -> true ; (
        retract(current_line(_)), retract(current_column(_)),
        asserta(current_line(L)), asserta(current_column(C)), fail)},
    ({Specifier \= fx, Specifier \= fy}; \+['(']),
    blanks, !.

% next_priority/2
% give the next priority to derivate an expression
next_priority(1300, 1200).
next_priority(1200, 1100).
next_priority(1100, 1000).
next_priority(1000, 700).
next_priority(999, 700).
next_priority(700, 500).
next_priority(500, 400).
next_priority(400, 200).
next_priority(200, 0).

% parse_expr/4
% parse an expression with level between 0 and 1300
%%% level 0
parse_expr(0, X) --> parse_expr_zero(X).
%%% level n, n > 0
%%%%%% fx, fy
parse_expr(Priority, Q) -->
    {Priority > 0, member(F, [fx, fy])},
    parse_operator(Priority, F, Op, _),
    ({F = fy} -> {Next = Priority} ; {next_priority(Priority, Next)}),
    (parse_expr(Next, T), ! ; {throw('expression expected')}),
    {(Op = '-', T = num(X)) -> (Y is X*(-1), Q = num(Y)) ; (Q = term(Op, [T]))}.
%%%%%% xfx, xfy, yfx
parse_expr(Priority, T) -->
    {Priority > 0, next_priority(Priority, Next)},
    parse_expr(Next, Left),
    (   {member(Specifier, [xfx, yfx, xfy])}, parse_operator(Priority, Specifier, Op, _),
        {(Specifier = xfx, PriorityRight = Next ; Specifier = yfx, PriorityRight = Next ; Specifier = xfy, PriorityRight = Priority)},
        (parse_expr(PriorityRight, Right), ! ; {throw('expression expected')}),
        ({Specifier = yfx} -> parse_expr2(Priority, term(Op, [Left,Right]), T) ; {T = term(Op, [Left,Right])}), !
    ; {T = Left} ).
%%%%%% yfx
parse_expr2(Priority, Left, T) -->
    {Priority > 0, next_priority(Priority, Next)},
    parse_operator(Priority, yfx, Op, _),
    (parse_expr(Next, Right), ! ; {throw('expression expected')}),
    parse_expr2(Priority, term(Op, [Left,Right]), T).
parse_expr2(_, T, T) --> [].

parse_expr_zero(num(T)) --> token_number(T), blanks, !.
parse_expr_zero(T) --> token_string(T), blanks, !.
parse_expr_zero(var(T)) --> token_variable(T), blanks, !.
parse_expr_zero(T) --> lparen, !, parse_expr(1300, T), (rparen, ! ; {throw('operator or right parenthesis expected')}), !.
parse_expr_zero(T) --> parse_list(T), blanks, !.
parse_expr_zero(T) --> parse_brace(T), blanks, !.
parse_expr_zero(T) --> parse_con(T), blanks, !.
parse_expr_zero(T) --> parse_term(T), blanks, !.
%parse_expr_zero(_) --> [X], {atom_concat('invalid input ', X, Msg), throw(Msg)}.

% parse_term/3
% parse a (possible compound) term
parse_term(term(Name, Args)) --> token_atom(Name), parse_term2(Args).
parse_term2([H|T]) --> lparen, !, (parse_expr(999, H), ! ; {throw('expression expected')}), parse_term3(T).
parse_term2([]) --> blanks.
parse_term3([H|T]) --> comma, !, (parse_expr(999, H), ! ; {throw('expression expected')}), parse_term3(T).
parse_term3([]) --> (rparen, ! ; {throw('operator or right parenthesis expected')}), blanks.

% parse_con/3
% parse a prefix connective
parse_con(term(Con, [H|T])) --> ['#',X],
    {member(X, ['@','&','|']), auto_column(2)},
    token_atom(Name),
    lparen, parse_expr(999, H), parse_term3(T),
    {atom_concat('#', X, Y),
    Con =.. [Y,Name]}.
parse_con(term(Con, [H|T])) --> [X],
    {member(X, ['@','&','|']), auto_column},
    token_atom(Name),
    lparen, parse_expr(999, H), parse_term3(T),
    {Con =.. [X,Name]}.

% parse_list/3
% parse a list
parse_list(T) --> lbracket, parse_list2(T).
parse_list2(term('.', [H,T])) --> parse_expr(999, H), !, parse_list3(T).
parse_list2(term('[]', [])) --> (rbracket, ! ; {throw('operator or right bracket expected')}).
parse_list3(term('.', [H,T])) --> comma, !, (parse_expr(999, H), ! ; {throw('expression expected')}), parse_list3(T).
parse_list3(T) --> bar, !, (parse_expr(999, T), ! ; {throw('expression expected')}), (rbracket, ! ; {throw('operator or right bracket expected')}).
parse_list3(term('[]', [])) --> (rbracket, ! ; {throw('operator or right bracket expected')}).

% parse_brace/3
% parse a brace
parse_brace(term('{}', [T])) --> lbrace, parse_expr(999, T), !, (rbrace, ! ; {throw('operator or right brace expected')}).
parse_brace(term('{}', [])) --> lbrace, (rbrace, ! ; {throw('expression or right brace expected')}).



% TOKENS

% Identifiers
token_identifier(T) --> identifier(L), {atom_chars(T,L)}.
token_minus_identifier(T) --> minus(X), identifier(Xs), {atom_chars(T,[X|Xs])}.

identifier([H|T]) --> letter(H), !, identifier(T).
identifier([]) --> [].

minus(X) --> [X], {char_code(X,C), C >= 97, C =< 122, auto_column}.
mayus(X) --> [X], {char_code(X,C), C >= 65, C =< 90, auto_column}.
letter(X) --> minus(X).
letter(X) --> mayus(X).
letter(X) --> number(X).
letter('_') --> ['_'], {auto_column}.

% Graphics
token_graphics(T) --> graphic(H), graphics(G), {atom_chars(T,[H|G])}.

graphics([H|T]) --> graphic(H), !, graphics(T).
graphics([]) --> [].
graphic(X) --> [X], {member(X,['.','|',',','=',';','#','$','&','*','+','-','/',':','<','>','?','^','~','\\']), auto_column}.

% Variables
token_variable(T) --> mayus(X), identifier(Xs), {atom_chars(T,[X|Xs])}.
token_variable(T) --> ['_'], {auto_column}, identifier(Xs), {atom_chars(T,['_'|Xs])}.

% Numbers
token_number(N) --> ['0','x'], {auto_column(2)}, hexadecimals(H),
    {(H \= [], ! ; throw('invalid hexadecimal number')), atom_chars(C,['0','x'|H]), atom_number(C,N)}.
token_number(N) --> ['0','b'], {auto_column(2)}, binaries(B),
    {(B \= [], ! ; throw('invalid binary number')), atom_chars(C,['0','b'|B]), atom_number(C,N)}.
token_number(N) --> ['0','o'], {auto_column(2)}, octals(O),
    {(O \= [], ! ; throw('invalid octal number')), atom_chars(C,['0','o'|O]), atom_number(C,N)}.
token_number(N) --> numbers(X), {X \= []}, token_number2(Y), !, {append(X,Y,Z)}, {atom_chars(T,Z), atom_number(T,N)}.
token_number2(N) --> ['.'], {auto_column}, numbers(X), {X \= []}, !, token_number3(Y), {append(['.'|X],Y,N)}.
token_number2(X) --> token_number3(X).
token_number3([e,S|X]) --> [e,S], {member(S, ['-','+']), auto_column(2)}, !,
    (numbers(X), {X \= []}, ! ; {throw('invalid number')}), !.
token_number3([e|X]) --> [e], {auto_column},
    (numbers(X), {X \= []}, ! ; {throw('invalid number')}), !.
token_number3([]) --> [].

binary('0') --> ['0'], {auto_column}.
binary('1') --> ['1'], {auto_column}.
binaries([N|M]) --> binary(N), !, binaries(M).
binaries([]) --> [].

octal(X) --> [X], {char_code(X,C), C >= 48, C =< 55, auto_column}.
octals([N|M]) --> octal(N), !, octals(M).
octals([]) --> [].

hexadecimal(X) --> [X], {member(X,['0','1','2','3','4','5','6','7','8','9','a','b','c','d','e','f','A','B','C','D','E','F']), auto_column}.
hexadecimals([N|M]) --> hexadecimal(N), !, hexadecimals(M).
hexadecimals([]) --> [].

number(X) --> [X], {char_code(X,C), C >= 48, C =< 57, auto_column}.
numbers([N|M]) --> number(N), !, numbers(M).
numbers([]) --> [].

% Strings
token_string(T) --> double_quote, double_quote_content(T), (double_quote, ! ; {throw('double quote expected')}), blanks.
double_quote --> ['"'], {auto_column}.
double_quote_content(term('.',[num(10),Xs])) --> ['\n'], !, {auto_line}, double_quote_content(Xs).
double_quote_content(term('.',[num(C), Xs])) --> [X], {X \= '"'}, {auto_column, char_code(X, C)}, !, double_quote_content(Xs).
double_quote_content(term('.',[num(34),Xs])) --> ['"','"'], !, {auto_column(2)}, double_quote_content(Xs).
double_quote_content(term('.',[num(34),Xs])) --> ['\\','"'], !, {auto_column(2)}, double_quote_content(Xs).
double_quote_content(term(',',[num(92),Xs])) --> ['\\','\\'], !, {auto_column(2)}, double_quote_content(Xs).
double_quote_content(term('[]',[])) --> [].

% Atoms
token_atom('!') --> ['!'], {auto_column}.
token_atom('#'(T)) --> ['#'], {auto_column}, token_minus_identifier(T).
token_atom(T) --> quoted(Xs), {atom_chars(T,Xs)}.
token_atom(T) --> token_graphics(T).
token_atom(T) --> token_minus_identifier(T).

quoted(X) --> quote, quote_content(X), (quote, ! ; {throw('single quote expected')}), blanks.
quote --> [''''], {auto_column}.
quote_content(['\n'|Xs]) --> ['\n'], !, {auto_line}, quote_content(Xs).
quote_content([X|Xs]) --> [X], {X \= ''''}, !, {auto_column}, quote_content(Xs).
quote_content([''''|Xs]) --> ['''',''''], !, {auto_column(2)}, quote_content(Xs).
quote_content([''''|Xs]) --> ['\\',''''], !, {auto_column(2)}, quote_content(Xs).
quote_content(['\\'|Xs]) --> ['\\','\\'], !, {auto_column(2)}, quote_content(Xs).
quote_content([]) --> [].

% Proper symbols
lbrace --> ['{'], {auto_column}, blanks.
rbrace --> ['}'], {auto_column}, blanks.
lparen --> ['('], {auto_column}, blanks.
rparen --> [')'], {auto_column}, blanks.
lbracket --> ['['], {auto_column}, blanks.
rbracket --> [']'], {auto_column}, blanks.
bar --> ['|'], {auto_column}, blanks.
comma --> [','], {auto_column}, blanks.
dot --> ['.'], {auto_column}, blanks.

% Blanks
blanks --> blank, !, blanks.
blanks --> [].
blank --> [' '], {auto_column}.
blank --> ['\n'], {auto_line}.
blank --> ['\t'], {auto_column}.
blank --> ['%'], singleline_comment, ['\n'], {auto_line}.
blank --> ['/','*'], multiline_comment, ['*','/'].
singleline_comment --> [X], {X \= '\n'}, !, singleline_comment.
singleline_comment --> [].
multiline_comment --> ['\n'], !, {auto_line}, multiline_comment.
multiline_comment --> [X], {X \= '*'}, !, multiline_comment.
multiline_comment --> ['*',X], {X \= '/'}, !, multiline_comment.
multiline_comment --> [].