/**
  * 
  * FILENAME: unfolding.pl
  * DESCRIPTION: This module contains predicates for unfolding FASILL programs.
  * AUTHORS: José Antonio Riaza Valverde
  * UPDATED: 04.02.2020
  * 
  **/



:- module(unfolding, [
    unfold/1,
    unfold/2,
    unfold_by_id/1,
    unfold_by_id/2
]).

:- use_module('environment').
:- use_module('semantics').



% unfold/1
% unfold(+Rule)
%
% This predicate succeeds unfolding the FASILL
% rule +Rule. This predicate has the side effect
% of retracting the rule +Rule and asserting the
% new unfolded rules.
unfold(R1) :-
    findall(R, unfold(R1, R), Rules),
    Rules \= [],
    once(retract(R1)),
    ( member(Rule, Rules),
      assertz(Rule),
      fail ; true ),
    sort_rules_by_id.

% unfold/2
% unfold(+Rule, ?Unfolded)
%
% This predicate succeeds when +Rule is a FASILL rule
% and ?Unfolded is an unfolded rule of +Rule.
:- dynamic(unfolding_id/1).
unfold(R1, R2) :-
    retractall(unfolding_id(_)),
    assertz(unfolding_id(1)),
    R1 = fasill_rule(head(Head), body(Body), [id(Id)|_]),
    get_variables(Body, Vars),
    inference(unfolding/0, state(Body, Vars), state(Expr, Subs), _),
    apply(Subs, Head, Head_),
    ( unfolding_id(R),
      atom_number(Atom, R),
      atom_concat(Id, '-', Id_),
      atom_concat(Id_, Atom, Id2),
      retractall(unfolding_id(_)),
      N is R+1,
      assertz(unfolding_id(N)) ),
    R2 = fasill_rule(head(Head_), body(Expr), [id(Id2),syntax(fasill)]).

% unfold_by_id/1
% unfold_by_id(?Id)
%
% This predicate succeeds unfolding the FASILL
% rule Rule with identifier ?Id. This predicate
% has the side effect of retracting the rule +Rule
% and asserting the new unfolded rules.
unfold_by_id(Id) :-
    fasill_rule(Head, Body, Info),
    member(id(Id), Info), !,
    unfold(fasill_rule(Head, Body, Info)).

% unfold_by_id/2
% unfold_by_id(?Id, ?Unfolded)
%
% This predicate succeeds when ?Id is the identifier
% of a FASILL rule Rule and ?Unfolded is an unfolded
% rule of Rule.
unfold_by_id(Id, Rule) :-
    fasill_rule(Head, Body, Info),
    member(id(Id), Info), !,
    unfold(fasill_rule(Head, Body, Info), Rule).