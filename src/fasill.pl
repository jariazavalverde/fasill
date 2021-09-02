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
    fasill/0,
    fasill/1
]).

:- use_module(fasill_parser).
:- use_module(fasill_inference).
:- use_module(fasill_environment).
:- use_module(fasill_exceptions).
:- use_module(fasill_term).
:- use_module(fasill_unfolding).

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
    
    * `:unfold(Id)` - unfold the rule with identifier Id.

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

%!  fasill
%
%   This predicate runs the FASILL interpreter with default options.

fasill :-
    fasill([]).

%!  fasill(+Options)
%
%   This predicate runs the FASILL interpreter with a list of options Options.

fasill(Options) :-
    (member('-quiet', Options) ->
        true ;
        writeln('FASILL (pre-alfa): http://dectau.uclm.es/fasill/'),
        writeln('Copyright (C) 2018-2021 José Antonio Riaza Valverde'),
        writeln('DEC-TAU research group, University of Castilla-La Mancha (UCLM)'),
        writeln('Released under the BSD-3 Clause license'),
        nl),
    run_fasill_command(term(':', [term(lattice,[term(library, [term(unit, [])])])])),
    run_fasill_arguments(Options),
    fasill_loop.

%!  fasill_loop
%
%   This predicate runs the interactive mode of the FASILL interpreter.

fasill_loop :-
    write('fasill> '),
    read_line_to_codes(user_input, Codes),
    (   Codes = end_of_file, ! ;
        atom_codes(Atom, Codes),
        atom_chars(Atom, Chars),
        catch(parse_query(Chars, Goal), Error, (
            write('uncaught exception in goal: '),
            fasill_term:fasill_print_term(Error),
            nl, nl,
            fail)),
        run_fasill_command(Goal)
    ), !,
    fasill_loop.
fasill_loop :-
    fasill_loop.

%!  run_fasill_arguments(+Options)
%
%   This predicate runs the list of FASILL arguments Options.

% Empty arguments
run_fasill_arguments([]) :-
    !.
% -lat $lattice
run_fasill_arguments(['-lat',Lat|Args]) :-
    !,
    run_fasill_command(term(':', [term(lattice,[term(library, [term(Lat, [])])])])),
    run_fasill_arguments(Args).
% -goal $goal
run_fasill_arguments(['-goal',Atom|Args]) :-
    !,
    atom_chars(Atom, Chars),
    parse_query(Chars, Goal),
    run_fasill_command(Goal),
    run_fasill_arguments(Args).
% -quiet
run_fasill_arguments(['-quiet'|Args]) :-
    !,
    run_fasill_arguments(Args).
% -halt
run_fasill_arguments(['-halt'|_]) :-
    halt.
% unknown command
run_fasill_arguments(X) :-
    write('unknown command: '),
    writeln(X),
    halt.

%!  run_fasill_command(+Command)
%
%   This predicate runs the FASILL command Command.

% Exit
run_fasill_command(term(':', [term(exit,[])])) :-
    halt.
% Help
run_fasill_command(term(':', [term(help,[])])) :-
    !,
    writeln(':exit          exit FASILL.'),
    writeln(':help          print this message.'),
    writeln(':lattice(Path) change lattice from file Path.'),
    writeln(':license       print license message.'),
    nl.
% Load lattice from file
run_fasill_command(term(':', [term(lattice,[term(Path, [])])])) :-
    !,
    exists_file(Path) ->
        fasill_environment:lattice_consult(Path) ;
        fasill_exceptions:existence_error(source_sink, Path, top_level/0, Error),
        fasill_term:fasill_print_term(Error),
        nl, nl.
% Load library lattice
run_fasill_command(term(':', [term(lattice,[term(library, [term(Lat, [])])])])) :-
    !,
    fasill_installation_path(Dir),
    directory_file_path(Dir, lattices, DirLat),
    atom_concat(Lat, '.lat.pl', File),
    directory_file_path(DirLat, File, Path),
    run_fasill_command(term(':', [term(lattice,[term(Path, [])])])).
% Show license
run_fasill_command(term(':', [term(license,[])])) :-
    !,
    fasill_installation_path(Dir),
    atom_concat(Dir, 'LICENSE', Path),
    open(Path, read, Stream),
    stream_to_list(Stream, Chars),
    close(Stream),
    atom_chars(Atom, Chars),
    writeln(Atom).
% Listing rules
run_fasill_command(term(':', [term(listing,[])])) :-
    !,
    (fasill_environment:fasill_rule(Head, Body, Info),
    member(id(Id), Info),
    write('('),
    write(Id),
    write(') '),
    fasill_environment:fasill_print_rule(fasill_rule(Head, Body, Info)),
    nl,
    fail ; nl).
% Unfold rule
run_fasill_command(term(':', [term(unfold, [Id])])) :-
    !,
    run_fasill_command(term(unfold, [Id])).
% Unknown command
run_fasill_command(term(':', [term(Name,Args)])) :-
    length(Args, Arity),
    fasill_exceptions:existence_error(command, Name/Arity, top_level/0, Error),
    fasill_term:fasill_print_term(Error),
    nl, nl.
% Query goal
run_fasill_command(Goal) :-
    catch((
        fasill_inference:query(Goal, SFCA),
        fasill_inference:fasill_print_fca(SFCA),
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
run_fasill_command(_) :-
    nl.