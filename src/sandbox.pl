/**
  * 
  * FILENAME: sandbox.pl
  * DESCRIPTION: This module contains predicates for the web interface.
  * AUTHORS: José Antonio Riaza Valverde
  * UPDATED: 11.11.2018
  * 
  **/



:- module(sandbox, [
    sandbox_run/5,
    sandbox_listing/1,
    sandbox_unfold/4
]).

:- use_module('environment').
:- use_module('parser').
:- use_module('unfolding').



sandbox_write([]).
sandbox_write(level(0)).
sandbox_write(level(N)) :- N > 0, write('  '), M is N-1, sandbox_write(level(M)).
sandbox_write(trace(Level, Info, State)) :- sandbox_write(level(Level)), write(Info), write(' '), sandbox_write(State).
sandbox_write(rule(head(Head), empty)) :- !, sandbox_write(Head), write('.').
sandbox_write(rule(head(Head), body(Body))) :- !, sandbox_write(Head), write(' <- '), sandbox_write(Body), write('.').
sandbox_write(fasill_rule(head(Head), empty, [id(Id)|_])) :- !,
    write(Id), write(' '),
    sandbox_write(Head), write('.').
sandbox_write(fasill_rule(head(Head), body(Body), [id(Id)|_])) :- !,
    write(Id), write(' '),
    sandbox_write(Head), write(' <- '),
    sandbox_write(Body), write('.').
sandbox_write(top) :- write(top).
sandbox_write(bot) :- write(bot).
sandbox_write(num(X)) :- write(X).
sandbox_write(var(X)) :- write(X).
sandbox_write(X/Y) :- write(X), write('/'), sandbox_write(Y).
sandbox_write(term('#&'(Name),[X,Y])) :- !, write('('), sandbox_write(X), write(' #&'), write(Name), write(' '), sandbox_write(Y), write(')'). 
sandbox_write(term('#|'(Name),[X,Y])) :- !, write('('), sandbox_write(X), write(' #|'), write(Name), write(' '), sandbox_write(Y), write(')'). 
sandbox_write(term('&'(Name),[X,Y])) :- !, write('('), sandbox_write(X), write(' &'), write(Name), write(' '), sandbox_write(Y), write(')'). 
sandbox_write(term('|'(Name),[X,Y])) :- !, write('('), sandbox_write(X), write(' |'), write(Name), write(' '), sandbox_write(Y), write(')'). 
sandbox_write(term('.',[X,Y])) :- !, sandbox_write_list(list(term('.',[X,Y]))). 
sandbox_write(term(X,[])) :- write(X).
sandbox_write(term(X,Y)) :- Y \= [], write(X), write('('), sandbox_write(Y), write(')').
sandbox_write(exception(X)) :- write('uncaught exception in derivation: '), sandbox_write(X).
sandbox_write(state(Goal,Subs)) :-
    write('<'),
    sandbox_write(Goal),
    write(', {'),
    sandbox_write(Subs),
    write('}>').
sandbox_write([X|Y]) :-
    Y \= [],
    sandbox_write(X),
    write(','),
    sandbox_write(Y).
sandbox_write([X]) :-
    sandbox_write(X).

sandbox_write_list(term('[]',[])) :- !.
sandbox_write_list(term([],[])) :- !.
sandbox_write_list(term('.',[X,Y])) :- !,
    write(','), sandbox_write(X), sandbox_write_list(Y).
sandbox_write_list(list(term('.',[X,Y]))) :- !,
    write('['), sandbox_write(X), sandbox_write_list(Y), write(']').
sandbox_write_list(X) :- write('|'), sandbox_write(X).

% sandbox_run/5
% sandbox_run(+Program, +Lattice, +Sim, +Goal, +Limit)
% 
% This predicate loads the program <+Program, +Lattice, +Sim>
% into the environemnt and runs the goal +Goal, with a limit
% of derivations +Limit, and writes in the standard output
% the resulting derivations.
sandbox_run(Program, Lattice, Sim, Goal, Limit) :-
    set_fasill_flag(trace, true),
    set_fasill_flag(max_inferences, num(Limit)),
    lattice_consult(Lattice),
    program_consult(Program),
    catch(similarity_consult(Sim), Error, (write('uncaught exception in similarities: '), sandbox_write(Error), nl)),
    ( query_consult(Goal, State),
      sandbox_write(State), nl, fail ; true ), nl,
    ( semantics:trace_derivation(Trace),
      sandbox_write(Trace), nl, fail ; true).

% sandbox_listing/1
% sandbox_listing(+Program)
% 
% This predicate loads the program +Program
% into the environemnt and, and writes in the
% standard output the loaded rules.
sandbox_listing(Program) :-
    program_consult(Program),
    ( fasill_rule(Head, Body, Info),
      sandbox_write(fasill_rule(Head, Body, Info)),
      nl, fail ; true).

% sandbox_unfold/4
% sandbox_unfold(+Program, +Lattice, +Sim, +Rule)
% 
% This predicate loads the program <+Program, +Lattice, +Sim>
% into the environemnt and runs the unfolding of the rule +Rule.
sandbox_unfold(Program, Lattice, Sim, Rule) :-
    lattice_consult(Lattice),
    program_consult(Program),
    catch(similarity_consult(Sim), Error, (write('uncaught exception in similarities: '), sandbox_write(Error), nl)),
    unfold_by_id(Rule),
    ( fasill_rule(Head, Body, _),
      sandbox_write(rule(Head, Body)),
      nl, fail ; true).