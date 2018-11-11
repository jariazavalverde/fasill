/**
  * 
  * FILENAME: unfolding.pl
  * DESCRIPTION: This module contains predicates for unfolding FASILL programs.
  * AUTHORS: José Antonio Riaza Valverde
  * UPDATED: 11.11.2018
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
      fail ; true ).

% unfold/2
% unfold(+Rule, ?Unfolded)
%
% This predicate succeeds when +Rule is a FASILL rule
% and ?Unfolded is an unfolded rule of +Rule.
unfold(R1, R2) :-
    R1 = fasill_rule(head(Head), body(Body), [id(Id)|_]),
    ( select_atom(Body, Body_, BodyTD, Atom) ->
        fasill_rule(head(Headi), Bodyi, [id(Idi)|_]),
        (Bodyi = empty -> BodyTD = TD ; BodyTD = term('&', [TD, Bodyi])),
        wmgu(Atom, Headi, state(TD, Subs)),
        apply(Head, Subs, HeadSubs),
        apply(Body_, Subs, BodySubs),
        atom_concat(Id, '-AS', Id_),
        atom_concat(Id_, Idi, IdAS),
        R2 = fasill_rule(head(HeadSubs), body(BodySubs), [id(IdAS),syntax(fasill)])
    ;
        ( interpretive_step(unfolding/0, state(Body, _), state(Body_, _), _) ->
            atom_concat(Id, '-IS', IdIS),
            R2 = fasill_rule(head(Head), body(Body_), [id(IdIS),syntax(fasill)])
        ;
            failure_step(state(Body, _), state(Body_, _), _),
            atom_concat(Id, '-FS', IdFS),
            R2 = fasill_rule(head(Head), body(Body_), [id(IdFS),syntax(fasill)])
        )
    ).

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