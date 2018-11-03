:- module(parser, [
    file_consult/2,
    parse_consult/2,
    parse_query/2
]).



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

% file_consult/2
% consult a program
file_consult(Path, Program) :-
    open(Path, read, Stream),
    stream_to_list(Stream, Input),
    close(Stream),
    parse_consult(Input, Program).

% parse_consult/2
% consult a program
parse_consult(Input, Program) :-
    reset_rule_id,
    parse_program(Program, Input, []).

% parse_query/2
% query a goal
parse_query(Input, Goal) :-
    reset_rule_id,
    parse_expr(1300, Goal, Input, ['.']).



% INITIAL OPERATOR TABLE

% current_op/4
% initial operator table
:- dynamic current_op/4.
current_op(1300, xfx, '<-',   no).
current_op(1300, xfx, '<',    yes).
current_op(1200, xfx, 'with', yes).
current_op(1100, xfy, '|',    yes).
current_op(1050, xfy, '&',    yes).
current_op(700,  xfx, '=',    no).
current_op(700,  xfx, '\\=',  no).
current_op(500,  yfx, '+',    no).
current_op(500,  yfx, '-',    no).
current_op(400,  yfx, '*',    no).
current_op(400,  yfx, '/',    no).
current_op(400,  yfx, '//',   no).
current_op(400,  yfx, 'rem',  no).
current_op(400,  yfx, 'mod',  no).
current_op(200,  fy,  '+',    no).
current_op(200,  fy,  '-',    no).



% PARSER

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
parse_rule(rule(head(Head), Body, [id(Id)|Info])) -->
    parse_expr(1300, T),
    {( T = term('<-', [Head, term(with, [BodyWith,TD])]), Body = body(term('&', [TD,BodyWith])), Info = [syntax(malp)] ;
       T = term('<'(Implication), [Head, term(with, [BodyWith,TD])]), Body = body(term('&'(Implication), [TD,BodyWith])), Info = [syntax(malp)] ;
       T = term('<-', [Head,Body_]), Body = body(Body_), Info = [syntax(fasill)] ;
       T = term('<'(_), [Head,Body_]), Body = body(Body_), Info = [syntax(malp)] ;
       T = Head, Body = empty, Info = [syntax(fasill)]
    )}, dot, !, {auto_rule_id(Id)}.

% parse_operator/6
% parse an operator T with Priority, Specifier and Name 
parse_operator(Priority, Specifier, T, Name) -->
    blanks, {current_op(Priority, Specifier, Op, Name), atom_chars(Op, Chars)}, Chars,
    ({Name = yes}, token_minus_identifier(Identifier), {T =.. [Op, Identifier]} ; {T = Op}).

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
parse_expr(0, num(T)) --> blanks, token_number(T).
parse_expr(0, str(T)) --> blanks, token_string(T).
parse_expr(0, var(T)) --> blanks, token_variable(T).
parse_expr(0, T) --> blanks, lparen, parse_expr(1300, T), rparen.
parse_expr(0, T) --> blanks, parse_list(T).
parse_expr(0, T) --> blanks, parse_term(T).
parse_expr(0, T) --> blanks, parse_agr(T).
%%% level n, n > 0
%%%%%% next level
parse_expr(Priority, T) --> {Priority > 0, next_priority(Priority, Next)}, parse_expr(Next, T).
%%%%%% fy, fy
parse_expr(Priority, term(Op, [T])) --> {Priority > 0}, parse_operator(Priority, fy, Op, _), parse_expr(Priority, T).
parse_expr(Priority, term(Op, [T])) --> {Priority > 0}, parse_operator(Priority, fx, Op, _), {next_priority(Priority, Next)}, parse_expr(Next, T).
%%%%%% xfx, xfy, yfx
parse_expr(Priority, T) -->
    {Priority > 0, next_priority(Priority, Next)},
    parse_expr(Next, Left),
    {(Specifier = xfx, PriorityRight = Next ; Specifier = yfx, PriorityRight = Next ; Specifier = xfy, PriorityRight = Priority)},
    parse_operator(Priority, Specifier, Op, _),
    parse_expr(PriorityRight, Right),
    ({Specifier = yfx} -> parse_expr2(Priority, term(Op, [Left,Right]), T) ; {T = term(Op, [Left,Right])}).
%%%%%% yfx
parse_expr2(Priority, Left, T) -->
    {Priority > 0, next_priority(Priority, Next)},
    parse_operator(Priority, yfx, Op, _),
    parse_expr(Next, Right),
    parse_expr2(Priority, term(Op, [Left,Right]), T).
parse_expr2(_, T, T) --> [].

% parse_term/3
% parse a (possible compound) term
parse_term(term(Name, Args)) --> token_atom(Name), parse_term2(Args).
parse_term2([H|T]) --> lparen, !, parse_expr(999, H), parse_term3(T).
parse_term2([]) --> [].
parse_term3([H|T]) --> comma, !, parse_expr(999, H), parse_term3(T).
parse_term3([]) --> rparen.

% parse_agr/3
% parse an aggregator
parse_agr(term('@'(Name), [H|T])) --> ['@'], token_atom(Name), lparen, parse_expr(999, H), parse_term3(T).

% parse_list/3
% parse a list
parse_list(T) --> lbracket, parse_list2(T).
parse_list2(term('[]', [])) --> rbracket.
parse_list2(term('.', [H,T])) --> parse_expr(999, H), parse_list3(T).
parse_list3(term('.', [H,T])) --> comma, parse_expr(999, H), parse_list3(T).
parse_list3(T) --> bar, parse_expr(999, T), rbracket.
parse_list3(term('[]', [])) --> rbracket.



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
token_graphics(T) --> graphics(G), {atom_chars(T,G)}.

graphics([H|T]) --> graphic(H), !, graphics(T).
graphics([]) --> [].
graphic(X) --> [X], {member(X,['#','$','&','*','+','-','/',':','<','?','@','^','~','\\'])}.

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
double_quote_content(X) --> [X], {X \= '"'}.
double_quote_content(['"']) --> ['"','"'].
double_quote_content(['"']) --> ['\\','"'].

% Atoms
token_atom(T) --> quoted(Xs), {atom_chars(T,Xs)}.
token_atom(T) --> token_graphics(T).
token_atom(T) --> token_minus_identifier(T).

quoted(X) --> quote, quote_content(X), quote.
quote --> [''''].
quote_content([X|Xs]) --> [X], {X \= ''''}, quote_content(Xs).
quote_content(['''']) --> ['''',''''].
quote_content(['''']) --> ['\\',''''].

% Proper symbols
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
blank --> ['\\','\n'].
blank --> ['\n'].
blank --> ['\t'].