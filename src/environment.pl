:- module(environment, [
    program_clause/2,
    program_rule_id/2,
    lattice_tnorm/1,
    lattice_call_bot/1,
    lattice_call_top/1,
    lattice_call_member/1,
    lattice_call_connective/3,
    similarity_tnorm/1,
    similarity_between/4
]).

:- dynamic(
    fasill_rule/3,
    fasill_lattice_tnorm/1,
    fasill_similarity_tnorm/1,
    fasill_similarity_between/4
).



% OBJECTS CONVERSION

% to_prolog/2
% to_prolog(+FASILL, ?Prolog)
%
% This predicate takes the FASILL object +FASILL
% and returns the object ?Prolog in Prolog notation.
to_prolog([], []) :- !.
to_prolog([X|Xs], [Y|Ys]) :-
    !, to_prolog(X,Y),
    to_prolog(Xs,Ys).
to_prolog(num(X), X) :- !.
to_prolog(term(X,Xs), Term) :-
    atom(X),
    !, to_prolog(Xs, Ys),
    Term =.. [X|Ys].

% from_prolog/2
% from_prolog(+Prolog, ?FASILL)
%
% This predicate takes the Prolog object +Prolog
% and returns the object ?FASILL in FASILL notation.
from_prolog([], term([], [])) :- !.
from_prolog([X|Xs], term('.', [Y,Ys])) :-
    !, from_prolog(X,Y),
    from_prolog(Xs,Ys).
from_prolog(X, num(X)) :- number(X), !.
from_prolog(X, term(X, [])) :- atom(X), !.
from_prolog(X, term(H,Args)) :-
    compound(X), !,
    X =.. [H|T],
    maplist(from_prolog, T, Args).



% RULES MANIPULATION

% program_clause/2
% program_clause(?Indicator, ?Rule)
%
%
program_clause(Name/Arity, rule(term(Name, Arity, Args), Body, Info)) :-
    fasill_rule(term(Name, Arity, Args), Body, Info).

% program_rule_id/2
% program_rule_id(+Rule, ?Id)
%
% This predicate succeeds when ?Id is the identifier
% of the rule +Rule.
program_rule_id(rule(_,_,Info), Id) :- member(id(Id), Info).



% LATTICES

% lattice_tnorm/1
% lattice_tnorm(?Tnorm)
%
% This predicate succeeds when ?Tnorm is the current
% t-norm asserted in the environment.
lattice_tnorm(Tnorm) :- lattice:tnorm(Tnorm).

% lattice_call_bot/1
% lattice_call_bot(-Bot)
%
% This predicate succeeds when -Bot is the
% bottom member of the lattice loaded into
% the environment.
lattice_call_bot(Bot) :-
    lattice:bot(Prolog),
    from_prolog(Prolog, Bot).

% lattice_call_top/1
% lattice_call_top(-Bot)
%
% This predicate succeeds when -Bot is the
% bottom member of the lattice loaded into
% the environment.
lattice_call_top(Top) :-
    lattice:top(Prolog),
    from_prolog(Prolog, Top).

% lattice_call_member/1
% lattice_call_member(+Memeber)
%
% This predicate succeeds when +Member is a member
% of the lattice loaded into the environment.
lattice_call_member(Member) :-
    to_prolog(Member, Prolog),
    lattice:member(Prolog).

% lattice_call_connective/3
% lattice_call_connective(+Name, +Arguments, ?Result)
%
% This predicate succeeds when ?Result is the result
% of evaluate the connective ?Name with the arguments
% +Arguments of the lattice loaded into the environment.
lattice_call_connective(Name, Args, Result) :-
    maplist(to_prolog, Args, Args_),
    call(lattice:Name, Args_, Prolog),
    from_prolog(Prolog, Result).



% SIMILARITY RELATIONS

% similarity_tnorm/1
% similarity_tnorm(?Tnorm)
%
% This predicate succeeds when ?Tnorm is the current
% t-norm asserted in the environment.
similarity_tnorm(Tnorm) :- fasill_similarity_tnorm(Tnorm).

% similarity_between/4
% similarity_between(?AtomA, ?AtomB, ?Length, ?TD)
%
% This predicate succeeds when ?AtomA/?Length is similar
% to ?AtomB/?Length with truth degree ?TD, using the current
% similarity relation in the environment.
similarity_between(AtomA, AtomB, Length, TD) :-
    fasill_similarity_between(AtomA, AtomB, Length, Prolog),
    from_prolog(Prolog, TD).