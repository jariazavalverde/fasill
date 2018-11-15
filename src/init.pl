/**
  * 
  * FILENAME: init.pl
  * DESCRIPTION: This file initialize the FASILL environment.
  * AUTHORS: José Antonio Riaza Valverde
  * UPDATED: 14.11.2018
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
    current_stream(_, read, Stream),
    read_stream_to_codes(Stream, Chars),
    main.



?- main.