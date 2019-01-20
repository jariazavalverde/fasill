/**
  * 
  * FILENAME: unfolding.pl
  * DESCRIPTION: This module contains predicates for unfolding FASILL programs.
  * AUTHORS: José Antonio Riaza Valverde
  * UPDATED: 15.11.2018
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
    apply(Head, Subs, Head_),
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

% sort_rules_by_id/0
% sort_rules_by_id
%
% This predicate retracts all the rules from the current
% environment and asserts them ordered by the identifier.
sort_rules_by_id :-
    findall(fasill_rule(X,Y,Z), fasill_rule(X,Y,Z), Rules),
    predsort(compare_rule_id, Rules, Sorted),
    retractall(fasill_rule(_,_,_)),
    ( member(Rule, Sorted),
      assertz(Rule),
      fail ; true ).

% compare_rule_id/3
% compare_rule_id(?Delta, +Rule1, +Rule2)
%
% This predicate succeeds when ?Delta is the ordering relation
% (<, > or =) for rules +Rule1 and +Rule2, compared by their
% identifiers.
compare_rule_id(Delta, X, Y) :-
    X = fasill_rule(_,_,[id(IdX)|_]),
    Y = fasill_rule(_,_,[id(IdY)|_]),
    atomic_list_concat(Xs, '-', IdX),
    atomic_list_concat(Ys, '-', IdY),
    maplist(atom_number, Xs, Xs_),
    maplist(atom_number, Ys, Ys_),
    compare(Delta, Xs_, Ys_).