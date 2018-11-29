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



main :-
    prompt1('fasill> '),
    current_stream(_, read, Stream),
    read_line_to_codes(Stream, Codes),
    ( Codes = end_of_file, ! ;
      atom_codes(Atom, Codes),
      atom_chars(Atom, Chars),
      parse_query(Chars, Goal),
      query(Goal, SFCA),
      fasill_show(SFCA, Show),
      display(Show), display(' '),
      read_line_to_codes(Stream, Codes),
      % (command ;) -> next answer
      (Codes = [59], nl, fail ; true)
    ),
    nl,
    main.



?- main.