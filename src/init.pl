/**
  * 
  * FILENAME: init.pl
  * DESCRIPTION: This file initialize the FASILL environment.
  * AUTHORS: José Antonio Riaza Valverde
  * UPDATED: 29.11.2018
  * 
  **/



:- use_module('parser').
:- use_module('builtin').
:- use_module('semantics').
:- use_module('environment').
:- use_module('exceptions').
:- use_module('unfolding').
:- use_module('tuning').



% print_term/1
% print_term(+Term)
%
% This predicate succeeds when @Term is a valid FASILL
% term, printing the term in the standard output.
print_term([]) :- !.
print_term(top) :- write(top).
print_term(bot) :- write(bot).
print_term(num(X)) :- ansi_format([bold,fg(cyan)], X, []).
print_term(var(X)) :- ansi_format([bold,fg(green)], X, []).
print_term(X/Y) :- ansi_format([bold,fg(green)], X, []), ansi_format([bold,fg(yellow)], '/', []), print_term(Y).
print_term(term('#'(Name),[])) :- !, write('#'), write(Name).
print_term(term('#@'(Name),Args)) :- !, write('#@'), write(Name), write('('), print_term(Args), write(')').
print_term(term('#&'(Name),[X,Y])) :- !, write('('), print_term(X), write(' #&'), write(Name), write(' '), print_term(Y), write(')'). 
print_term(term('#|'(Name),[X,Y])) :- !, write('('), print_term(X), write(' #|'), write(Name), write(' '), print_term(Y), write(')'). 
print_term(term('&'(Name),[X,Y])) :- !, write('('), print_term(X), write(' &'), write(Name), write(' '), print_term(Y), write(')'). 
print_term(term('|'(Name),[X,Y])) :- !, write('('), print_term(X), write(' |'), write(Name), write(' '), print_term(Y), write(')'). 
print_term(term('.',[X,Y])) :- !, print_term_list(list(term('.',[X,Y]))). 
print_term(term(X,[])) :- escape_atom(X, X_), ansi_format([bold,fg(blue)], X_, []).
print_term(term(X,Y)) :- Y \= [],
    escape_atom(X, X_),
    ansi_format([bold,fg(blue)], X_, []),
    ansi_format([bold,fg(yellow)], '(', []),
    print_term(Y),
    ansi_format([bold,fg(yellow)], ')', []).
print_term(exception(X)) :- ansi_format([bold,fg(red)], 'uncaught exception in derivation: ', []), print_term(X).
print_term(state(Goal,Subs)) :-
    ansi_format([bold,fg(yellow)], '< ', []),
    print_term(Goal),
    ansi_format([bold,fg(yellow)], ', {', []),
    print_term(Subs),
    ansi_format([bold,fg(yellow)], '} > ', []).
print_term([X|Y]) :-
    Y \= [],
    print_term(X),
    ansi_format([bold,fg(yellow)], ', ', []),
    print_term(Y).
print_term([X]) :-
    print_term(X).

print_term_list(term('[]',[])) :- !.
print_term_list(term([],[])) :- !.
print_term_list(term('.',[X,Y])) :- !,
    ansi_format([bold,fg(yellow)], ', ', []), print_term(X), print_term_list(Y).
print_term_list(list(term('.',[X,Y]))) :- !,
    ansi_format([bold,fg(yellow)], '[', []), print_term(X), print_term_list(Y), ansi_format([bold,fg(yellow)], ']', []).
print_term_list(X) :- ansi_format([bold,fg(yellow)], '|', []), print_term(X).



% main/0
% main
%
% This predicate runs the interactive mode of the FASILL
% interpreter.
main :-
    prompt1('fasill> '),
    read_line_to_codes(user_input, Codes),
    ( Codes = end_of_file, ! ;
      atom_codes(Atom, Codes),
      atom_chars(Atom, Chars),
      parse_query(Chars, Goal),
      query(Goal, SFCA),
      once(print_term(SFCA)),
      display(' '),
      get_single_char(Code),
      char_code(Char, Code),
      display(Char),
      % (command ;) -> next answer
      Code = 59, nl, fail ; true
    ),
    nl,
    main.



?- main.