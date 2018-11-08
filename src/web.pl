:- module(web, [
    web_run/5
]).

:- use_module('environment').
:- use_module('parser').



web_write([]).
web_write(num(X)) :- write(X).
web_write(var(X)) :- write(X).
web_write(X/Y) :- write(X), write('/'), web_write(Y).
web_write(term('.',[X,Y])) :- !, web_write_list(list(term('.',[X,Y]))). 
web_write(term(X,[])) :- write(X).
web_write(term(X,Y)) :- Y \= [], write(X), write('('), web_write(Y), write(')').
web_write(exception(X)) :- write('uncaught exception in derivation: '), web_write(X).
web_write(state(Goal,Subs)) :-
    write('<'),
    web_write(Goal),
    write(', {'),
    web_write(Subs),
    write('}>').
web_write([X|Y]) :-
    Y \= [],
    web_write(X),
    write(','),
    web_write(Y).
web_write([X]) :-
    web_write(X).

web_write_list(term('[]',[])) :- !.
web_write_list(term([],[])) :- !.
web_write_list(term('.',[X,Y])) :- !,
    write(','), web_write(X), web_write_list(Y).
web_write_list(list(term('.',[X,Y]))) :- !,
    write('['), web_write(X), web_write_list(Y), write(']').
web_write_list(X) :- write('|'), web_write(X).

% web_run/5
% web_run(+Program, +Lattice, +Sim, +Goal, +Limit)
% 
% This predicate loads the program <+Program, +Lattice, +Sim>
% into the environemnt and runs the goal +Goal, with a limit
% of derivations +Limit, and writes in the standard output
% the resulting derivations.
web_run(Program, Lattice, Sim, Goal, Limit) :-
    lattice_consult(Lattice),
    program_consult(Program),
    catch(similarity_consult(Sim), Error, (write('uncaught exception in similarities: '), web_write(Error), nl)),
    set_max_inferences(Limit),
    ( query_consult(Goal, State),
      web_write(State), nl, fail ; true ).