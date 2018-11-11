/**
  * 
  * FILENAME: unfolding.pl
  * DESCRIPTION: This module contains predicates for unfolding FASILL programs.
  * AUTHORS: José Antonio Riaza Valverde
  * UPDATED: 11.11.2018
  * 
  **/



:- module(unfolding, [
    unfold/2,
    unfold_by_id/2
]).

:- use_module('environment').
:- use_module('semantics').



% unfold/2
% unfold(+Rule, ?Unfolded)
%
% This predicate succeeds when +Rule is a FASILL rule
% and ?Unfolded is an unfolded rule of +Rule.
unfold(R1, R2) :-
    R1 = fasill_rule(head(Head), body(Body), _),
    ( select_atom(Body, Body_, BodyTD, Atom) ->
        fasill_rule(head(Headi), Bodyi, _),
        (Bodyi = empty -> BodyTD = TD ; BodyTD = term('&', [TD, Bodyi])),
        wmgu(Atom, Headi, state(TD, Subs)),
        apply(Head, Subs, HeadSubs),
        apply(Body_, Subs, BodySubs),
        R2 = fasill_rule(head(HeadSubs), body(BodySubs), [])
    ;
        interpretive_step(unfolding/0, state(Body, _), state(Body_, _), _),
        R2 = fasill_rule(head(Head), body(Body_), [])
    ).

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