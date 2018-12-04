/**
  * 
  * FILENAME: init.pl
  * DESCRIPTION: This file initialize the FASILL environment.
  * AUTHORS: José Antonio Riaza Valverde
  * UPDATED: 01.12.2018
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
print_term(exception(X)) :- ansi_format([bold,fg(red)], 'uncaught exception: ', []), print_term(X).
print_term(state(Goal,Subs)) :-
    ansi_format([bold,fg(yellow)], '< ', []),
    print_term(Goal),
    ansi_format([bold,fg(yellow)], ', {', []),
    print_term(Subs),
    ansi_format([bold,fg(yellow)], '} >', []).
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
% This predicate runs the FASILL interpreter.
main :-
    run_command(term(lattice,[term(library, [term(real, [])])])),
    current_prolog_flag(argv, Args),
    ( member('-halt', Args) -> true ;
        tty_clear,
        writeln('FASILL (pre-alfa): http://dectau.uclm.es/fasill/'),
        writeln('Copyright (C) 2018 José Antonio Riaza Valverde'),
        writeln('Released under the BSD-3 Clause license') ),
    run_arguments(Args),
    interactive_mode.

% interactive_mode/0
% interactive_mode
%
% This predicate runs the interactive mode of the FASILL
% interpreter.
interactive_mode :-
    prompt1('fasill> '),
    read_line_to_codes(user_input, Codes),
    ( Codes = end_of_file, ! ;
      atom_codes(Atom, Codes),
      atom_chars(Atom, Chars),
      parse_query(Chars, Goal),
      ( Goal = term(':',[X]) -> run_command(X) ; (
        query(Goal, SFCA),
        once(print_term(SFCA)),
        write(' '),
        get_single_char(Code),
        ( Code = 59 -> writeln(';'), fail ; writeln('.') )
      ; nl ) )
    ), !, interactive_mode.
interactive_mode :- interactive_mode.

% run_arguments/1
% run_arguments(+Arguments)
%
% This predicate runs the list of arguments +Arguments.
run_arguments([]) :- !.
% -lat $lattice
run_arguments(['-lat',Lat|Args]) :- !,
    run_command(term(lattice,[term(library, [term(Lat, [])])])), !,
    run_arguments(Args).
% -goal $goal
run_arguments(['-goal',Atom|Args]) :- !,
    atom_chars(Atom, Chars),
    parse_query(Chars, Goal),
    ( Goal = term(':',[X]) -> run_command(X) ; (
      query(Goal, SFCA),
      once(print_term(SFCA)),
      writeln(' ;'),
      fail ; nl ) ),
    run_arguments(Args).
% -halt
run_arguments(['-halt'|_]) :- !,
    halt.
% unknown command
run_arguments(X) :-
    write('unknown command: '),
    writeln(X),
    halt.

% run_command/1
% run_command(+Command)
%
% This predicate runs the command +Command.
%% Exit
run_command(term(exit,[])) :- !,
    halt.
%% Help
run_command(term(help,[])) :- !,
    ansi_format([bold,fg(white)], ':exit', []), writeln('          exit FASILL.'),
    ansi_format([bold,fg(white)], ':help', []), writeln('          print this message.'),
    ansi_format([bold,fg(white)], ':lattice(Path)', []), writeln(' change lattice from file Path.'),
    ansi_format([bold,fg(white)], ':license', []), writeln('       print license message.'),
    nl.
%% Load lattice from file
run_command(term(lattice,[term(Path, [])])) :- !,
    ( exists_file(Path) ->
      lattice_consult(Path) ;
      existence_error(source_sink, Path, top_level/0, Error),
      print_term(exception(Error)), nl, nl ).
%% Load library lattice
run_command(term(lattice,[term(library, [term(Lat, [])])])) :- !,
    prolog_load_context(directory, Dir_),
    atom_concat(Dir_, '/../lattices/', Dir),
    atom_concat(Dir, Lat, Path_),
    atom_concat(Path_, '.lat.pl', Path),
    run_command(term(lattice,[term(Path, [])])).
%% Show license
run_command(term(license,[])) :- !,
    prolog_load_context(directory, Dir),
    atom_concat(Dir, '/../LICENSE', Path),
    open(Path, read, Stream),
    stream_to_list(Stream, Chars),
    close(Stream),
    atom_chars(Atom, Chars),
    writeln(Atom).
%% Otherwise
run_command(term(Name,Args)) :-
    length(Args, Arity),
    existence_error(command, Name/Arity, top_level/0, Error),
    print_term(exception(Error)), nl, nl.



?- main.