/**
  * 
  * FILENAME: linearization.pl
  * DESCRIPTION: This module contains predicates for linearizing FASILL programs.
  * AUTHORS: José Antonio Riaza Valverde
  * UPDATED: 05.03.2019
  * 
  **/



:- module(linearization, [
    linearize_head_rule/1,
    linearize_head_rule/2,
    linearize_head_rule_by_id/1,
    linearize_head_rule_by_id/2,
    linearize_head_program/0,
    extend_rule/1,
    extend_rule/2,
    extend_rule_by_id/1,
    extend_rule_by_id/2,
    extend_program/0
]).

:- use_module('environment').



%% UTILS

% linearize_rename/3
% linearize_rename(+Expression, ?Renamed, ?Substitution)
%
% This predicate renames the expression +Expression, replacing
% the variables of the expression by fresh variables. ?Renamed
% is the expression +Expression with fresh variables.
linearize_rename(X, Y, Subs) :-
    max_variable(X, 'V', N),
    succ(N, M),
    count_variables(X, Vars),
    linearize_rename(X, Y, Vars, M, _, [], Subs).
linearize_rename(var(X), var(Y), Vars, N, M, Subs, [Y/var(X)|Subs]) :-
    X \== '_',
    member(X-C, Vars),
    C > 1, !,
    succ(N, M),
    atom_number(Atom, N),
    atom_concat('V', Atom, Y).
linearize_rename(term(Name, Xs), term(Name, Ys), Vars, N, M, Subs, Subs_) :-
    !, linearize_rename(Xs, Ys, Vars, N, M, Subs, Subs_).
linearize_rename([], [], _, N, N, Subs, Subs) :- !.
linearize_rename([X|Xs], [Y|Ys], Vars, N, S, Subs, Subs3) :-
    !, linearize_rename(X, Y, Vars, N, M, Subs, Subs2),
    linearize_rename(Xs, Ys, Vars, M, S, Subs2, Subs3).
linearize_rename(X, X, _, N, N, Subs, Subs).

% linearize_substitution/2
% linearize_substitution(?Substitution, ?Body)
%
% This predicate succeeds when ?Substitution is a FASILL
% substitution of variables and ?Body is the linearized
% body of the substitution.
linearize_substitution([], empty).
linearize_substitution([X/Y], term(~,[var(X), Y])).
linearize_substitution([X/Y|Subs], term('&', [term('~',[var(X), Y]), LinSubs])) :-
    linearize_substitution(Subs, LinSubs).

extend_term(Term1, Term2, TD) :-
    current_fasill_flag(lambda_unification, Lambda_),
    (Lambda_ == bot -> lattice_call_bot(Lambda) ;
        (Lambda_ == top -> lattice_call_top(Lambda) ; Lambda = Lambda_)
    ),
    lattice_call_top(Top),
    extend_term(Term1, Term2, Lambda, Top, TD).
extend_term(var(X), var(X), _, TD, TD).
extend_term(num(X), num(X), _, TD, TD).
extend_term(term(X, Xs), term(Y, Ys), Lambda, CurrentTD, TD) :-
    length(Xs, Arity),
    (X = Y , lattice_call_top(Sim) ; similarity_between(X, Y, Arity, Sim) , X \== Y),
    similarity_tnorm(Tnorm),
    lattice_call_connective('&'(Tnorm), [CurrentTD, Sim], TDnorm),
    lattice_call_leq(Lambda, TDnorm),
    extend_term(Xs, Ys, Lambda, TDnorm, TD).
extend_term([], [], _, TD, TD).
extend_term([X|Xs], [Y|Ys], Lambda, TD1, TD3) :-
    extend_term(X, Y, Lambda, TD1, TD2),
    extend_term(Xs, Ys, Lambda, TD2, TD3).



%% LINEARIZE HEAD RULES

% linearize_head_rule/1
% linearize_head_rule(+Rule)
%
% This predicate succeeds linearizing the FASILL
% rule +Rule. This predicate has the side effect
% of retracting the rule +Rule and asserting the
% new linearized rule.
linearize_head_rule(R1) :-
    linearize_head_rule(R1, R2),
    once(retract(R1)),
    assertz(R2),
    sort_rules_by_id.

% linearize_head_rule/2
% linearize_head_rule(+Rule, ?Linearized)
%
% This predicate succeeds when +Rule is a FASILL rule
% and ?Linearized is a linearized rule of +Rule.
linearize_head_rule(R1, R2) :-
    R1 = fasill_rule(head(Head), Body, [id(Id)|Info]),
    linearize_rename(Head, Head2, Subs),
    reverse(Subs, Subs_),
    linearize_substitution(Subs_, LinBody),
    (Body == empty ->
        (LinBody == empty -> Body2 = empty ; Body2 = body(LinBody)) ;
        (LinBody == empty -> Body2 = Body ; Body = body(Body_), Body2 = body(term('&', [LinBody, Body_])))
    ),
    atom_concat(Id, 'L', IdL),
    R2 = fasill_rule(head(Head2), Body2, [id(IdL)|Info]).

% linearize_head_rule_by_id/1
% linearize_head_rule_by_id(?Id)
%
% This predicate succeeds linearizing the FASILL
% rule with identifier ?Id. This predicate
% has the side effect of retracting the rule
% and asserting the new linearized rule.
linearize_head_rule_by_id(Id) :-
    fasill_rule(Head, Body, Info),
    member(id(Id), Info), !,
    linearize_head_rule(fasill_rule(Head, Body, Info)).

% linearize_head_rule_by_id/2
% linearize_head_rule_by_id(?Id, ?Linearized)
%
% This predicate succeeds when ?Id is the identifier
% of a FASILL rule and ?Linearized is a linearized
% rule.
linearize_head_rule_by_id(Id, Rule) :-
    fasill_rule(Head, Body, Info),
    member(id(Id), Info), !,
    linearize_head_rule(fasill_rule(Head, Body, Info), Rule).

% linearize_head_program/0
% linearize_head_program
%
% This predicate succeeds linearizing the FASILL
% rules of the current program. This predicate
% has the side effect of retracting the rules
% and asserting the new linearized rules.
linearize_head_program :-
    fasill_rule(Head, Body, Info),
    linearize_head_rule(fasill_rule(Head, Body, Info)),
    fail ; true.



%% EXTEND RULES

% extend_rule/1
% extend_rule(+Rule)
%
% This predicate succeeds extending the FASILL
% rule +Rule. This predicate has the side effect
% of retracting the rule +Rule and asserting the
% new extended rules.
extend_rule(R1) :-
    retract(R1),
    ( extend_rule(R1, R2),
      assertz(R2),
      fail ; true ),
    sort_rules_by_id.

% extend_rule/2
% extend_rule(+Rule, ?Extended)
%
% This predicate succeeds when +Rule is a FASILL rule
% and ?Extended is an extended rule of +Rule.
extend_rule(R1, R2) :-
    linearize_head_rule(R1, Rl),
    Rl = fasill_rule(head(HeadL), Body, [id(Id)|Info]),
    extend_term(HeadL, HeadE, TD),
    atom_concat(Id, ex, IdEx),
    (Body == empty -> BodyE = body(TD) ; Body = body(Body_), BodyE = body(term('&', [TD, Body_]))),
    R2 = fasill_rule(head(HeadE), BodyE, [id(IdEx)|Info]).

% extend_rule_by_id/1
% extend_rule_by_id(?Id)
%
% This predicate succeeds extending the FASILL
% rule with identifier ?Id. This predicate
% has the side effect of retracting the rule
% and asserting the new extended rules.
extend_rule_by_id(Id) :-
    fasill_rule(Head, Body, Info),
    member(id(Id), Info), !,
    extend_rule(fasill_rule(Head, Body, Info)).

% extend_rule_by_id/2
% extend_rule_by_id(?Id, ?Extended)
%
% This predicate succeeds when ?Id is the identifier
% of a FASILL rule and ?Extended is a extended rule.
extend_rule_by_id(Id, Rule) :-
    fasill_rule(Head, Body, Info),
    member(id(Id), Info), !,
    extend_rule(fasill_rule(Head, Body, Info), Rule).

% extend_program/0
% extend_program
%
% This predicate succeeds extending the FASILL
% rules of the current program. This predicate
% has the side effect of retracting the rules
% and asserting the new extended rules.
extend_program :-
    linearize_head_program,
    fasill_rule(Head, Body, Info),
    extend_rule(fasill_rule(Head, Body, Info)),
    fail ; true.