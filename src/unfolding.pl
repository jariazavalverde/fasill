/**
  * 
  * FILENAME: unfolding.pl
  * DESCRIPTION: This module contains predicates for unfolding FASILL programs.
  * AUTHORS: José Antonio Riaza Valverde
  * UPDATED: 28.07.2021
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

:- use_module(substitution).
:- use_module(environment).
:- use_module(resolution).
:- use_module(term).



% CLASSIC UNFOLDING

% classic_unfold_by_id/1
% classic_unfold_by_id(?Id)
%
% This predicate succeeds unfolding the FASILL
% rule Rule with identifier ?Id. This predicate
% has the side effect of retracting the rule +Rule
% and asserting the new unfolded rules.
classic_unfold_by_id(Id) :-
	environment:fasill_rule(Head, Body, Info),
	member(id(Id), Info), !,
	classic_unfold(fasill_rule(Head, Body, Info)).

% classic_unfold_by_id/2
% classic_unfold_by_id(?Id, ?Unfolded)
%
% This predicate succeeds when ?Id is the identifier
% of a FASILL rule Rule and ?Unfolded is an unfolded
% rule of Rule.
classic_unfold_by_id(Id, Rule) :-
	environment:fasill_rule(Head, Body, Info),
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
	environment:once(retract(R1)),
	( member(Rule, Rules),
	  environment:assertz(Rule),
	  fail ; true ),
	environment:sort_rules_by_id.

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
	substitution:init_substitution(BodyR, Vars),
	resolution:inference(unfolding/0, state(BodyR, Vars), state(Expr, Subs), _),
	BodyR \= Expr,
	substitution:apply(Subs, HeadR, Head_),
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
	environment:fasill_rule(Head, Body, Info),
	member(id(Id), Info), !,
	guards_unfold(fasill_rule(Head, Body, Info)).

% guards_unfold_by_id/2
% guards_unfold_by_id(?Id, ?Unfolded)
%
% This predicate succeeds when ?Id is the identifier
% of a FASILL rule Rule and ?Unfolded is an unfolded
% rule of Rule.
guards_unfold_by_id(Id, Rule) :-
	environment:fasill_rule(Head, Body, Info),
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
	environment:once(retract(R1)),
	( member(Rule, Rules),
	  environment:assertz(Rule),
	  fail ; true ),
	environment:sort_rules_by_id.

% guards_unfold/2
% guards_unfold(+Rule, ?Unfolded)
%
% This predicate succeeds when +Rule is a FASILL rule
% and ?Unfolded is an unfolded rule of +Rule.
guards_unfold(R1, R2) :-
	R1 = fasill_rule(head(Head), body(Body), Info),
	substitution:init_substitution(Body, Vars),
	resolution:select_atom(Body, Expr, Replace, _Selected), !,
	environment:similarity_tnorm(Tnorm),
	resolution:auto_fresh_variable_id(VarId),
	Var = var('$'(VarId)),
	findall(
		Guard,
		( resolution:inference(unfolding/0, state(Body, Vars), state(Expr, Sub), _),
		  exclude_trivial_vars(Sub, SubVars),
		  substitution:substitution_to_list(SubVars, GuardList),
		  bound_substitution(Sub, BoundSub),
		  make_guard(GuardList, G1, G2),
		  Unification = term('~', [term(g, G1), term(g, G2)]),
	      ReplaceVar = term(Tnorm, [Var, Replace]),
	  	  resolution:select_atom(Body, ExprVar, ReplaceVar, _),
		  substitution:apply(BoundSub, ExprVar, ExprVarSub),
		  Guard = term('->', [Unification, ExprVarSub])
		),
		RegularGuards
	),
	resolution:failure_step(state(Body, Vars), state(Expr, _), _),
	(is_safe_unfolding(RegularGuards, Expr) ->
		classic_unfold(R1, R2)
	;
		term:fasill_term_variables(Head, FSVars),
		resolution:rename(FSVars, [FSVars, Expr], [FSVarsR, ExprR]),
		FailureGuard = term('->', [term('^', [term('~', [term(g, FSVars), term(g, FSVarsR)])]), ExprR]),
		append(RegularGuards, [FailureGuard], Vector),
		vector_guards(Vector, Guards),
		BodyG = term(guards, [term(on, [Guards, Var])]),
		R2 = fasill_rule(head(Head), body(BodyG), Info)
	).
guards_unfold(R1, R2) :-
	classic_unfold(R1, R2).

% is_safe_unfolding/2
% is_safe_unfolding(+RegularGuards, +FailureBody)
%
% This predicate succeeds when it is safe to perform a classic unfolding.
% I.e.:
%     (∀ i ∈ {1,...,n}, \sigma_i is bound)
%                       ∧
%     [(∃ i ∈ {1,...,n}: \sigma_i = id) ∨ (B_{n+1} ≡ ⊥)].
is_safe_unfolding(RegularGuards, FailureBody) :-
	RegularGuard = term('->', [term('~', [_,term(g, G)]), _]),
	% (∀ i ∈ {1,...,n}, \sigma_i is bound)
	forall(member(RegularGuard, RegularGuards), is_bound(G)),
	once(
		% (∃ i ∈ {1,...,n}: \sigma_i = id)
		(member(RegularGuard, RegularGuards), G = []) ;
		% (B_{n+1} ≡ ⊥)
		(environment:lattice_call_bot(Bot), resolution:up_body(FailureBody, Bot))
	).

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

% bound_substitution/1
% bound_substitution(+Substitution, ?BoundSubstitution)
%
% This predicate succeeds when +BoundSubstitution is +Substitution
% restringed to its variables whose images are bound terms.
bound_substitution(Sub, BoundSub) :-
	substitution:substitution_to_list(Sub, Binds),
	include(is_bound, Binds, BoundBinds),
	substitution:list_to_substitution(BoundBinds, BoundSub).

% is_bound/1
% is_bound(+Term)
%
% Check if a term is bound.
is_bound(_-Term) :- !,
	is_bound(Term).
is_bound(term(Name, Args)) :- !,
	length(Args, Arity),
	environment:lattice_call_top(Top),
	environment:lattice_call_bot(Bot),
	forall(
		environment:similarity_between(Name, _, Arity, TD, _),
		(TD == Top ; TD == Bot)
	),
	is_bound(Args).
is_bound([]) :- !.
is_bound([X|Xs]) :- !,
	is_bound(X),
	is_bound(Xs).
is_bound(_).

exclude_trivial_vars(Sub1, Sub2) :-
	substitution:substitution_to_list(Sub1, List1),
	exclude(trivial_var, List1, List2),
	substitution:list_to_substitution(List2, Sub2).

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
	environment:fasill_rule(Head, Body, Info),
	member(id(Id), Info), !,
	unfold(fasill_rule(Head, Body, Info)).

% unfold_by_id/2
% unfold_by_id(?Id, ?Unfolded)
%
% This predicate succeeds when ?Id is the identifier
% of a FASILL rule Rule and ?Unfolded is an unfolded
% rule of Rule.
unfold_by_id(Id, Rule) :-
	environment:fasill_rule(Head, Body, Info),
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
	environment:once(retract(R1)),
	( member(Rule, Rules),
	  environment:assertz(Rule),
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
		resolution:rename([Head,Body], [HeadR,BodyR])),
	resolution:select_atom(BodyR, BodyVar, Var, term(guards, [term(on, [Guards, TD])])),
	!,
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