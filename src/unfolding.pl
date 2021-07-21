/**
  * 
  * FILENAME: unfolding.pl
  * DESCRIPTION: This module contains predicates for unfolding FASILL programs.
  * AUTHORS: José Antonio Riaza Valverde
  * UPDATED: 21.07.2021
  * 
  **/



:- module(unfolding, [
	% classic unfolding
	classic_unfold/1,
	classic_unfold/2,
	classic_unfold_by_id/1,
	classic_unfold_by_id/2,
	% guards-based unfolding
	guards_unfold/1,
	guards_unfold/2,
	guards_unfold_by_id/1,
	guards_unfold_by_id/2,
	% similarity-based unfolding
	unfold/1,
	unfold/2,
	unfold_by_id/1,
	unfold_by_id/2
]).

:- use_module('environment').
:- use_module('semantics').



% CLASSIC UNFOLDING

% classic_unfold_by_id/1
% classic_unfold_by_id(?Id)
%
% This predicate succeeds unfolding the FASILL
% rule Rule with identifier ?Id. This predicate
% has the side effect of retracting the rule +Rule
% and asserting the new unfolded rules.
classic_unfold_by_id(Id) :-
	fasill_rule(Head, Body, Info),
	member(id(Id), Info), !,
	classic_unfold(fasill_rule(Head, Body, Info)).

% classic_unfold_by_id/2
% classic_unfold_by_id(?Id, ?Unfolded)
%
% This predicate succeeds when ?Id is the identifier
% of a FASILL rule Rule and ?Unfolded is an unfolded
% rule of Rule.
classic_unfold_by_id(Id, Rule) :-
	fasill_rule(Head, Body, Info),
	member(id(Id), Info), !,
	classic_unfold(fasill_rule(Head, Body, Info), Rule).

% classic_unfold/1
% classic_unfold(+Rule)
%
% This predicate succeeds unfolding the FASILL
% rule +Rule. This predicate has the side effect
% of retracting the rule +Rule and asserting the
% new unfolded rules.
classic_unfold(R1) :-
	findall(R, classic_unfold(R1, R), Rules),
	Rules \= [],
	once(retract(R1)),
	( member(Rule, Rules),
	  assertz(Rule),
	  fail ; true ),
	sort_rules_by_id.

% classic_unfold/2
% classic_unfold(+Rule, ?Unfolded)
%
% This predicate succeeds when +Rule is a FASILL rule
% and ?Unfolded is an unfolded rule of +Rule.
:- dynamic(unfolding_id/1).
classic_unfold(R1, R2) :-
	retractall(unfolding_id(_)),
	assertz(unfolding_id(1)),
	R1 = fasill_rule(head(Head), body(Body), [id(Id)|Info]),
	HeadR = Head, BodyR = Body,
	get_variables(BodyR, Vars),
	inference(unfolding/0, state(BodyR, Vars), state(Expr, Subs), _),
	BodyR \= Expr,
	apply(Subs, HeadR, Head_),
	( unfolding_id(R),
	  atom_number(Atom, R),
	  atom_concat(Id, '-', Id_),
	  atom_concat(Id_, Atom, Id2),
	  retractall(unfolding_id(_)),
	  succ(R, N),
	  assertz(unfolding_id(N)) ),
	R2 = fasill_rule(head(Head_), body(Expr), [id(Id2)|Info]).



% GUARDS ON-BASED UNFOLDING

% guards_unfold_by_id/1
% guards_unfold_by_id(?Id)
%
% This predicate succeeds unfolding the FASILL
% rule Rule with identifier ?Id. This predicate
% has the side effect of retracting the rule +Rule
% and asserting the new unfolded rules.
guards_unfold_by_id(Id) :-
	fasill_rule(Head, Body, Info),
	member(id(Id), Info), !,
	guards_unfold(fasill_rule(Head, Body, Info)).

% guards_unfold_by_id/2
% guards_unfold_by_id(?Id, ?Unfolded)
%
% This predicate succeeds when ?Id is the identifier
% of a FASILL rule Rule and ?Unfolded is an unfolded
% rule of Rule.
guards_unfold_by_id(Id, Rule) :-
	fasill_rule(Head, Body, Info),
	member(id(Id), Info), !,
	guards_unfold(fasill_rule(Head, Body, Info), Rule).

% guards_unfold/1
% guards_unfold(+Rule)
%
% This predicate succeeds unfolding the FASILL
% rule +Rule. This predicate has the side effect
% of retracting the rule +Rule and asserting the
% new unfolded rules.
guards_unfold(R1) :-
	findall(R, guards_unfold(R1, R), Rules),
	Rules \= [],
	once(retract(R1)),
	( member(Rule, Rules),
	  assertz(Rule),
	  fail ; true ),
	sort_rules_by_id.

% guards_unfold/2
% guards_unfold(+Rule, ?Unfolded)
%
% This predicate succeeds when +Rule is a FASILL rule
% and ?Unfolded is an unfolded rule of +Rule.
guards_unfold(R1, R2) :-
	R1 = fasill_rule(head(Head), body(Body), Info),
	get_variables(Body, Vars),
	select_atom(Body, Expr, Replace, _Selected), !,
	similarity_tnorm(Tnorm),
	semantics:auto_fresh_variable_id(VarId),
	Var = var('$'(VarId)),
	findall(
		Eq,
		( inference(unfolding/0, state(Body, Vars), state(Expr, Sub), _),
		  exclude_trivial_vars(Sub, SubVars),
		  substitution_to_list(SubVars, GuardList),
		  crisp_substitution(Sub, CrispSub),
		  make_guard(GuardList, G1, G2),
		  Guard = term('~', [term(g, G1), term(g, G2)]),
	      ReplaceVar = term(Tnorm, [Var, Replace]),
	  	  select_atom(Body, ExprVar, ReplaceVar, _),
		  apply(CrispSub, ExprVar, ExprVarSub),
		  Eq = term('->', [Guard, ExprVarSub])
		), Eqs, [FS]
	),
	failure_step(state(Body, Vars), state(Expr, _), _),
	(short_interpretive_step(unfolding/0, state(Expr, Vars), state(Expr2, _), _) -> true ; Expr2 = Expr),
	(simplification_step(unfolding/0, state(Expr2, Vars), state(Expr3, _), _) -> true ; Expr3 = Expr2),
	fasill_term_variables(Head, FSVars),
	rename(FSVars, [FSVars, Expr3], [FSVarsR, ExprR]),
	FS = term('->', [term('^~', [term(g, FSVars), term(g, FSVarsR)]), ExprR]),
	(is_safe_unfolding(Eqs, FS) ->
		classic_unfold(R1, R2)
	;
		vector_guards(Eqs, Guards),
		BodyG = term(guards, [term(on, [Guards, Var])]),
		R2 = fasill_rule(head(Head), body(BodyG), Info)
	).
guards_unfold(R1, R2) :-
	classic_unfold(R1, R2).

% is_safe_unfolding/2
% is_safe_unfolding(+Guards, +FailureGuard)
%
% Check if it is safe to perform a classic unfolding.
is_safe_unfolding(Eqs, _) :-
	forall(member(Eq, Eqs), is_empty_guard(Eq)).
is_safe_unfolding(Eqs, term('->', [term('^~', _), Bot])) :-
	lattice_call_bot(Bot),
	forall(member(Eq, Eqs), any_similarity(Eq)).

% is_empty_guard/1
% is_empty_guard(+Guard)
%
% Check if the unification problem of a guard is empty.
is_empty_guard(term('->', [term('~', [term(g, []), term(g, [])]), _])).
is_empty_guard(term('->', [term('^~', _), _])).

% vector_guards/2
% vector_guards(+Vector, -Guards)
% vector_guards(-Vector, +Guards)
%
% Transform a list of guards +Vector into a valid body
% -Guards for the *guards on* control construct.
vector_guards([X|Xs], term(';', [X,Right])) :-
	vector_guards(Xs, Right).
vector_guards([X],  X) :- !.

% make_guard/3
% make_guard(+Binds, -G1, -G2)
%
% This predicates makes the pair of guards -G1 -G2 from 
% a list of bindings +Binds.
make_guard([], [], []).
make_guard([K-V|Xs], [var(K)|Ks], [V|Vs]) :-
	make_guard(Xs, Ks, Vs).

% crisp_substitution/1
% crisp_substitution(+Substitution, ?CrispSubstitution)
%
% This predicate succeeds when +CrispSubstitution is +Substitution
% restringed to its variables whose images are crisp terms.
crisp_substitution(Sub, CrispSub) :-
	substitution_to_list(Sub, Binds),
	include(is_crisp, Binds, CrispBinds),
	list_to_substitution(CrispBinds, CrispSub).

% is_crisp/1
% is_crisp(+Term)
%
% Check if a term is crisp.
is_crisp(_-Term) :- !,
	is_crisp(Term).
is_crisp(term(Name, Args)) :- !,
	length(Args, Arity),
	lattice_call_top(Top),
	lattice_call_bot(Bot),
	forall(
		similarity_between(Name, _, Arity, TD, _),
		(TD == Top ; TD == Bot)
	),
	is_crisp(Args).
is_crisp([]) :- !.
is_crisp([X|Xs]) :- !,
	is_crisp(X),
	is_crisp(Xs).
is_crisp(_).

exclude_trivial_vars(Sub1, Sub2) :-
	substitution_to_list(Sub1, List1),
	exclude(trivial_var, List1, List2),
	list_to_substitution(List2, Sub2).

trivial_var(X-var(X)).



% SIMILARITY-BASED UNFOLDING

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
unfold(R1, R2) :-
	unfold(R1, R2, [rename(true)]).

unfold(R1, R2, Options) :-
	R1 = fasill_rule(head(Head), body(Body), Info),
	(member(rename(false), Options) ->
		HeadR = Head, BodyR = Body ;
		rename([Head,Body], [HeadR,BodyR])),
	select_atom(BodyR, BodyVar, Var, term(guards, [term(on, [Guards, TD])])), !,
	vector_guards(GuardsList, Guards),
	select(term('->', [HeadG, BodyG]), GuardsList, Rules, GuardsList2),
	findall(
		term('->', [H,B]),
		unfold(fasill_rule(head(HeadG), body(BodyG), Info), fasill_rule(head(H), body(B), _), [rename(false)]),
		Rules),
	Rules \= [], !,
	flatten(GuardsList2, GuardsListF),
	vector_guards(GuardsListF, GuardsU),
	Var = term(guards, term(on, [GuardsU, TD])),
	R2 = fasill_rule(head(HeadR), body(BodyVar), Info).

unfold(R1, R2, _Options) :-
	guards_unfold(R1, R2).