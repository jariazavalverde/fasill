%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% file: builtin.pl                                                             %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%% call_guard_tree/1
%%% call_guard_tree( +guard_tree )
%%%
%%% Invoke a guard tree as a goal.
%%% call_guard_tree(GuardTree) is true if and only if GuardTree represents a
%%% goal which is true. 
eval_builtin_predicate(call_guard_tree/1, state(_, Sub1), selected(ExprVar, Answer, Atom), state(ExprVarS, Sub2)) :-
	Atom = term(call_guard_tree, [Tree]),
	empty_substitution(Vars),
	call_guard_tree(Tree, Sub1, Vars, X-X, Answer, Sub2, Subs),
	apply_subs(Subs, ExprVar, ExprVarS).

call_guard_tree(term('.',[P,Ps]), Sub1, Vars, Subs1, Answer, Sub2, Subs2) :-
	call_guard_tree(P, Sub1, Vars, Subs1, Answer, Sub2, Subs2) ;
	call_guard_tree(Ps, Sub1, Vars, Subs1, Answer, Sub2, Subs2).
call_guard_tree(term(t,[Var, Guard1, Guard2, _Goal, term('[]',[])]), Sub1, Vars1, Subs1-X, GoalVars, Sub3, Subs1) :-
	apply_subs(Subs1, Guard1, Guard1S),
	apply_subs(Subs1, Guard2, Guard2S),
	unify(Guard1S, Guard2S, _, state(TD, Sub2)), !,
	X = [Sub2],
	compose(Sub1, Sub2, Sub3),
	(Var = var(VarID) -> put_substitution(Vars1, VarID, TD, Vars2) ; Vars2 = Vars1),
	apply(Vars2, Goal, GoalVars).
call_guard_tree(term(t,[Var, Guard1, Guard2, Goal, Child]), Sub1, Vars1, Subs1-X, Answer, Sub4, Subs2) :-
	apply_subs(Subs1, Guard1, Guard1S),
	apply_subs(Subs1, Guard2, Guard2S),
	unify(Guard1S, Guard2S, _, state(TD, Sub2)),
	X = [Sub2|Y],
	compose(Sub1, Sub2, Sub3),
	(Var = var(VarID) -> put_substitution(Vars1, VarID, TD, Vars2) ; Vars2 = Vars1),
	call_guard_tree(Child, Sub3, Vars2, Subs1-Y, Answer, Sub4, Subs2).

apply_subs(U, X, X) :- var(U), !.
apply_subs([], X, X) :- !.
apply_subs([U|Us], X, Z) :- apply(U, X, Y), apply_subs(Us, Y, Z).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% file: unfolding.pl                                                           %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% GUARD TREE BASED UNFOLDING

% guard_tree_unfold/2
% guard_tree_unfold(+Goal, +Depth)
%
%
guard_tree_unfold(Goal, Depth) :-
	guard_tree_unfold(Goal, Depth, Tree),
	asserta(fasill_rule(head(Goal), body(term(call_guard_tree, [Tree])), [id(u), syntax(fasill)])).

% guard_tree_unfold/3
% guard_tree_unfold(+Goal, +Depth, ?Tree)
%
% This predicate succeeds unfolding the FASILL
% goal +Goal with max depth +Depth, generating
% the guard tree ?Tree.
guard_tree_unfold(_, 0, term('[]',[])) :- !.
guard_tree_unfold(Goal, Depth, Tree) :-
	succ(N, Depth),
	get_variables(Goal, Vars),
	append_fresh_variable(Goal, Var, GoalVar),
	findall(term(t, [Var, term(wmgu, [term(g, Guard1), term(g, Guard2)]), Child]), (
		unfolding_inference(state(GoalVar, Vars), state(Goal2, Sub), Info),
		substitution_to_list(Sub, List),
		make_guard(List, Guard1, Guard2),
		guard_tree_unfold(Goal2, N, Child)
	), List),
	from_prolog_list(List, Tree), !.
guard_tree_unfold(Goal, _, term('.', [term(t, [term(goal, [Goal])]), term('[]',[])])).

:- dynamic last_unfolding_inference/1.
unfolding_inference(State0, State2, Info) :-
	inference(unfolding/0, State0, State1, Info),
	(simplification_step(unfolding/0, State1, State2, _) -> true ; State1 = State2),
	retractall(last_unfolding_inference(_)),
	asserta(last_unfolding_inference(Info)).
unfolding_inference(State0, State2, Info) :-
	last_unfolding_inference(_/_),
	retractall(last_unfolding_inference(_)),
	failure_step(State0, State1, Info),
	(simplification_step(unfolding/0, State1, State2, _) -> true ; State1 = State2).

% make_guard/3
% make_guard(+List, ?Guard1, ?Guard2)
%
% 
make_guard([], [], []) :- !.
make_guard([Var-var(Var)|T], Guard1, Guard2) :-
	make_guard(T, Guard1, Guard2), !.
make_guard([Var-Value|T], [var(Var)|Guard1], [Value|Guard2]) :-
	make_guard(T, Guard1, Guard2).

% append_fresh_variable/5
% append_fresh_variable(+Goal1, +Goal2, +Substitution, ?Var, ?GoalVar)
%
%
append_fresh_variable(Term, Var, TermVar) :-
	auto_fresh_variable_id(N),
	Var = var('$'(N)),
	similarity_tnorm(Tnorm),
	select_atom(Term, TermVar, term(Tnorm, [Var, Atom]), Atom), !.

% current_guard_tree_id/1
% current_guard_tree_id(?Identifier)
%
% This predicate stores the current identifier ?Identifier
% to be used in a guard tree.
:- dynamic(current_guard_tree_id/1).
?- retractall(current_guard_tree_id(_)).
current_guard_tree_id(1).

% get_guard_tree_id/1
% get_guard_tree_id(?Identifier)
%
% This predicate updates the current guard tree identifier 
% ?Identifier and returns it.
get_guard_tree_id(Id) :-
	current_guard_tree_id(Id),
	retract(current_guard_tree_id(_)),
	succ(Id, N),
	assertz(current_guard_tree_id(N)).

% reset_fresh_variable_id/0
% reset_fresh_variable_id
%
% This predicate resets the current ?Identifier identifier
% to the first.
reset_guard_tree_id :-
	retract(current_guard_tree_id(_)),
	assertz(current_guard_tree_id(1)).