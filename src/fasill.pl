/*  Part of FASILL

    Author:        José Antonio Riaza Valverde
    E-mail:        riaza.valverde@gmail.com
    WWW:           https://dectau.uclm.es/fasill
    Copyright (c)  2018 - 2021, José Antonio Riaza Valverde
    All rights reserved.

    Redistribution and use in source and binary forms, with or without
    modification, are permitted provided that the following conditions are met:

    * Redistributions of source code must retain the above copyright notice, 
      this list of conditions and the following disclaimer.

    * Redistributions in binary form must reproduce the above copyright notice,
      this list of conditions and the following disclaimer in the documentation
      and/or other materials provided with the distribution.

    * Neither the name of the copyright holder nor the names of its
      contributors may be used to endorse or promote products derived from
      this software without specific prior written permission.

    THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
    AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
    IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE 
    ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE 
    LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR 
    CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF 
    SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS 
    INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN 
    CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
    ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
    POSSIBILITY OF SUCH DAMAGE.
*/

:- module(fasill, [
	main/1,
	initialize/1,
	interactive_mode/0
]).

:- use_module(parser).
:- use_module(resolution).
:- use_module(environment).
:- use_module(exceptions).
:- use_module(term).

/** <module> FASILL
    This library provides predicates for running the FASILL interpreter.

    FASILL reads the input until the first break line, analyzes the term and
    runs the goal. After the first answer, you can press the key (`;`) to find 
    the next answer, or any other to end the search. 

    A command is a FASILL term preceded by the character (:).

    * `:exit` - exit FASILL.
    * `:help` - print this message.
    * `:lattice(Path)` - change lattice from file Path.
    * `:license` - print license message.
    * `:listing` - list the loaded rules.

    By default, FASILL incorporates a set of predefined lattices, and loads the
    lattice $([0,1], \leq)$ into the environment. You can change the current
    lattice with the command `:lattice(Path)`. If `Path` is a term of the form
    `library(Name)` instead of a file path, FASILL finds in its predefined
    lattices:

    * `:lattice(library(unit))` - reals in the unit interval with logics of
      product, Gödel and Łukasiewicz.
    
    * `:lattice(library(bool))` - boolean values with classical operators.

    You can directly run FASILL with a different lattice with the option
    `fasill -lat <lattice>`.
*/

%!  fasill_installation_path(?Path)
%
%   This predicate succeeds when Path is the installation path of FASILL.

:- dynamic fasill_installation_path/1.
:-
	prolog_load_context(directory, Dir),
	directory_file_path(Dir, '..', FASILL),
	asserta(fasill_installation_path(FASILL)).

%!  main(+Arguments)
%
%   This predicate runs the FASILL interpreter.

main(Args) :-
	initialize(Args),
	interactive_mode.

%!  initialize(+Arguments)
%
%   This predicate initializes the FASILL interpreter.

initialize(Args) :-
	(member('-halt', Args) ->
		true ;
		writeln('FASILL (pre-alfa): http://dectau.uclm.es/fasill/'),
		writeln('Copyright (C) 2018-2021 José Antonio Riaza Valverde'),
		writeln('DEC-TAU research group, University of Castilla-La Mancha (UCLM)'),
		writeln('Released under the BSD-3 Clause license'),
		nl),
	run_command(term(':', [term(lattice,[term(library, [term(unit, [])])])])),
	run_arguments(Args).

%!  interactive_mode
%
%   This predicate runs the interactive mode of the FASILL interpreter.

interactive_mode :-
	write('fasill> '),
	read_line_to_codes(user_input, Codes),
	(	Codes = end_of_file, ! ;
		atom_codes(Atom, Codes),
		atom_chars(Atom, Chars),
		catch(parse_query(Chars, Goal), Error, (
			write('uncaught exception in goal: '),
			term:fasill_print_term(Error),
			nl, nl,
			fail)),
		run_command(Goal)
	), !,
	interactive_mode.
interactive_mode :-
	interactive_mode.

%!  run_arguments(+Arguments)
%
%   This predicate runs the list of arguments Arguments.

run_arguments([]) :-
	!.
% -lat $lattice
run_arguments(['-lat',Lat|Args]) :-
	!,
	run_command(term(':', [term(lattice,[term(library, [term(Lat, [])])])])),
	!,
	run_arguments(Args).
% -goal $goal
run_arguments(['-goal',Atom|Args]) :- !,
	atom_chars(Atom, Chars),
	parse_query(Chars, Goal),
	run_command(Goal),
	run_arguments(Args).
% -halt
run_arguments(['-halt'|_]) :-
	halt.
% unknown command
run_arguments(X) :-
    write('unknown command: '),
    writeln(X),
    halt.

%!  run_command(+Command)
%
%   This predicate runs the command Command.

% Exit
run_command(term(':', [term(exit,[])])) :-
	halt.
% Help
run_command(term(':', [term(help,[])])) :-
	!,
	writeln(':exit          exit FASILL.'),
	writeln(':help          print this message.'),
	writeln(':lattice(Path) change lattice from file Path.'),
	writeln(':license       print license message.'),
	nl.
% Load lattice from file
run_command(term(':', [term(lattice,[term(Path, [])])])) :-
	!,
	exists_file(Path) ->
		environment:lattice_consult(Path) ;
		exceptions:existence_error(source_sink, Path, top_level/0, Error),
		term:fasill_print_term(Error),
		nl, nl.
% Load library lattice
run_command(term(':', [term(lattice,[term(library, [term(Lat, [])])])])) :-
	!,
	fasill_installation_path(Dir),
	directory_file_path(Dir, lattices, DirLat),
	atom_concat(Lat, '.lat.pl', File),
	directory_file_path(DirLat, File, Path),
	run_command(term(':', [term(lattice,[term(Path, [])])])).
% Show license
run_command(term(':', [term(license,[])])) :-
	!,
	fasill_installation_path(Dir),
	atom_concat(Dir, 'LICENSE', Path),
	open(Path, read, Stream),
	stream_to_list(Stream, Chars),
	close(Stream),
	atom_chars(Atom, Chars),
	writeln(Atom).
% Listing rules
run_command(term(':', [term(listing,[])])) :-
	!,
	environment:fasill_rule(Head, Body, Info),
	member(id(Id), Info),
	write(Id),
	write(' '),
	environment:fasill_print_rule(fasill_rule(Head, Body, Info)),
	nl,
	fail ; nl.
% Unknown command
run_command(term(':', [term(Name,Args)])) :-
	length(Args, Arity),
	exceptions:existence_error(command, Name/Arity, top_level/0, Error),
	term:fasill_print_term(Error),
	nl, nl.
% Query goal
run_command(Goal) :-
	catch((
		resolution:query(Goal, SFCA),
		resolution:fasill_print_fca(SFCA),
		(SFCA \= exception(_) ->
			true ;
			nl, fail),
		write(' '),
		get_single_char(Code),
		(Code = 59 ->
			writeln(';'),
			fail ;
			writeln('.'))),
		Error, write(Error)),
	nl, !.
run_command(_) :-
	nl.