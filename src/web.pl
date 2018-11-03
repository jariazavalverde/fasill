:- module(web, [
    web_run/5
]).

:- use_module('environment').
:- use_module('semantics').
:- use_module('parser').



% web_run/5
% web_run(+Program, +Lattice, +Sim, +Goal, +Limit)
% 
% This predicate loads the program <+Program, +Lattice, +Sim>
% into the environemnt and runs the goal +Goal, with a limit
% of derivations +Limit, and writes in the standard output
% the resulting derivations.
web_run(Program, Lattice, Sim, GoalAtom, Limit) :-
    lattice_consult(Lattice),
    program_consult(Program),
    similarity_consult(Sim),
    set_max_inferences(Limit),
    atom_chars(GoalAtom, Chars),
    parse_query(Chars, Goal),
    derivation(state(Goal,[]), State, _),
    writeln(State).