/*  Part of FASILL

    Author:        José Antonio Riaza Valverde
    E-mail:        riaza.valverde@gmail.com
    WWW:           https://dectau.uclm.es/fasill
    Copyright (c)  2018 - 2021, José Antonio Riaza Valverde
    All rights reserved.

    Redistribution and use in source and binary forms, with or without
    modification, are permitted provided that the following conditions are met:

    * Redistributions of source code must retain the above copyright notice, 
      this list of conditions and the following disclaimer.

    * Redistributions in binary form must reproduce the above copyright notice,
      this list of conditions and the following disclaimer in the documentation
      and/or other materials provided with the distribution.

    * Neither the name of the copyright holder nor the names of its
      contributors may be used to endorse or promote products derived from
      this software without specific prior written permission.

    THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
    AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
    IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE 
    ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE 
    LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR 
    CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF 
    SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS 
    INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN 
    CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
    ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
    POSSIBILITY OF SUCH DAMAGE.
*/

:- module(resolution, [
	query/2,
	select_atom/4,
	select_expression/4,
	interpretable/1,
	derivation/4,
	get_variables/2,
	inference/4,
	simplification_step/4,
	operational_step/4,
	interpretive_step/4,
	short_interpretive_step/4,
	long_interpretive_step/4,
	failure_step/3,
	up_body/2,
	rename/2,
	rename/3,
	is_rename/2,
	arithmetic_evaluation/3,
	arithmetic_comparison/3,
	trace_derivation/1,
	trace_level/1,
	auto_fresh_variable_id/1
]).

:- use_module(substitution).
:- use_module(unification).
:- use_module(environment).
:- use_module(exceptions).
:- use_module(builtin).

/** <module> Resolution
    This library provides predicates for resolution.

    The procedural semantics of FASILL is defined in a stepwise manner. First,
    an operational stage is introduced which proceeds similarly to SLD
    resolution in pure logic programming, returning an expression still
    containing values and connectives. Then, an interpretive stage evaluates
    these connectives and produces a final answer.
*/

%!  is_fuzzy_computed_answer(+Expression)
%
%   This predicate succeeds when Expression is a (symbolic) fuzzy computed
%   answer.

is_fuzzy_computed_answer(X) :-
	environment:current_fasill_flag(symbolic, term(false, [])), !,
	environment:lattice_call_member(X).
is_fuzzy_computed_answer(X) :-
	interpretable(X),
	\+select_expression(X, _, _, _).

%!  select_atom(+Expression, ?ExprVar, ?Var, ?Atom)
%
%   This predicate selects an atom Atom from the expression Expression, where
%   ExprVar is the expression Expression with the variable Var instead of the
%   atom Atom.

select_atom(term(Term, Args), term(Term, Args_), Var, Atom) :-
	functor(Term, Op, _),
	member(Op, ['@','&','|','#@','#&','#|','#/','#?']),
	!,
	select_atom(Args, Args_, Var, Atom).
select_atom(term(Term, Args), Var, Var, term(Term, Args)) :-
	\+functor(Term, '#', 1),
	\+environment:lattice_call_member(term(Term, Args)),
	!.
select_atom([Term|Args], [Term_|Args], Var, Atom) :-
	select_atom(Term, Term_, Var, Atom),
	!.
select_atom([Term|Args], [Term|Args_], Var, Atom) :-
	select_atom(Args, Args_, Var, Atom).

%!  select_expression(+Expression, ?ExprVar, ?Var, ?Atom)
%
%   This predicate selects an interpretable expression Atom from the expression
%   Expression, where ExprVar is the expression Expression with the variable Var
%   instead of the atom Atom.

select_expression(top, Var, Var, top) :-
	!.
select_expression(bot, Var, Var, bot) :-
	!.
select_expression(term(Term, Args), Var, Var, term(Term, Args)) :-
	functor(Term, Op, _),
	once(member(Op, ['@','&','|'])),
	environment:maplist(lattice_call_member, Args),
	!.
select_expression(term(Term, Args), term(Term, Args_), Var, Expr) :-
	select_expression(Args, Args_, Var, Expr).
select_expression(sup(X, Y), Var, Var, sup(X, Y)) :-
    environment:lattice_call_member(X),
    environment:lattice_call_member(Y),
	!.
select_expression(sup(X, Y), ExprVar, Var, Atom) :-
	select_expression([X,Y], ExprVar, Var, Atom),
	!.
select_expression([Term|Args], [Term_|Args], Var, Atom) :-
	select_expression(Term, Term_, Var, Atom),
	!.
select_expression([Term|Args], [Term|Args_], Var, Atom) :-
	select_expression(Args, Args_, Var, Atom).

%!  select_simplifiable(+Expression, ?ExprVar, ?Var, ?Atom)
%
%   This predicate selects a simplifiable expression Atom from the expression
%   Expression, where ExprVar is the expression Expression with the variable Var
%   instead of the atom Atom.

select_simplifiable(term(Term, [X,Y]), Var, Var, term(Term, [X,Y])) :-
    functor(Term, '&', _),
    environment:lattice_call_bot(Bot),
    once((X == Bot ; X == bot ; Y == Bot ; Y == bot)),
	!.
select_simplifiable(term(Term, Args), term(Term, Args_), Var, Expr) :-
    select_simplifiable(Args, Args_, Var, Expr),
	!.
select_simplifiable(sup(X, Y), ExprVar, Var, Atom) :-
	select_simplifiable([X,Y], ExprVar, Var, Atom),
	!.
select_simplifiable([Term|Args], [Term_|Args], Var, Atom) :-
	select_simplifiable(Term, Term_, Var, Atom),
	!.
select_simplifiable([Term|Args], [Term|Args_], Var, Atom) :-
	select_simplifiable(Args, Args_, Var, Atom).

%!  interpretable(+Expression)
%
%   This predicate succeeds when the expression Expression can be interpreted
%   (i.e., there is no atoms in the expression).

interpretable(Expr) :-
	\+select_atom(Expr, _, _, _).

%!  query(+Goal, ?Answer)
%
%   This predicate succeeds when Answer is a fuzzy computed answer (fca) for the
%   goal Goal. A fca is a term of the form state(TD, Substitution), where TD is
%   the truth degree.

:- dynamic check_success/0, trace_derivation/1, trace_level/1.
query(Goal, Answer) :-
	retractall(check_success),
	retractall(trace_derivation),
	retractall(trace_level(_)),
	assertz(trace_level(0)),
	get_variables(Goal, Vars),
	State = state(Goal, Vars),
	(environment:current_fasill_flag(trace, term(true,[])) ->
		assertz(trace_derivation(trace(0, 'GOAL', State))) ;
		true),
	derivation(top_level/0, State, Answer, _).

%!  get_variables(+Term, ?Variables)
%
%   This predicate succeeds when Variables is the initial substitution for the
%   term Term, where each variable in Term is replaced by itself (X/X).

get_variables(X, Z) :-
	get_variables2(X, Y),
	list_to_set(Y, S),
	substitution:list_to_substitution(S, Z).
get_variables2(var(X), [X-var(X)]) :-
	!.
get_variables2(term(_,Args), Vars) :-
	!,
	get_variables2(Args, Vars).
get_variables2([H|T], Vars) :-
	!,
	get_variables2(H, Vh),
	get_variables2(T, Vt),
	append(Vh, Vt, Vars).
get_variables2(_,[]).

%!  derivation(+From, +State1, ?State2, ?Info)
%
%   This predicate performs a complete derivation from an initial state State1
%   to the final state State2. Info is a list containing the information of
%   each step.

derivation(From, State1, State2, Info) :-
	environment:current_fasill_flag(depth_limit, num(Depth)),
	derivation(Depth, From, State1, State2, 0, _, Info).

%!  derivation(+DepthLimit, +From, +State1, ?State2, +CurrentDepth, ?ResultDepth, ?Info)
%
%   This predicate performs a complete derivation from an initial state State1
%   to the final state State2. Info is a list containing the information of
%   each step.

derivation(Depth, _, State, State, N, Depth, []) :-
	Depth > 0,
	N >= Depth,
	!.
derivation(_, _, exception(Error), exception(Error), N, N, []) :-
	!.
derivation(_, _, state(Goal,Subs), State, N, N, []) :-
	is_fuzzy_computed_answer(Goal),
	!,
	environment:lattice_call_bot(Bot),
	(Bot == Goal ->
		environment:current_fasill_flag(failure_steps, term(true, [])) ;
		true),
	State = state(Goal, Subs).
derivation(Depth, From, State, State_, N, P, [X|Xs]) :-
	(trace_level(Level) ->
		Level_ is Level+1 ;
		Level_ = false),
	catch(
		inference(From, State, State1, X),
		Error,
		(State1 = exception(Error), !)),
	(environment:current_fasill_flag(trace, term(true,[])), State1 \= exception(_) ->
		assertz(trace_derivation(trace(Level_, X, State1))) ;
		true),
	(Level_\= false ->
		retractall(trace_level(_)), assertz(trace_level(Level_)) ;
		true),
	succ(N, M),
	derivation(Depth, From, State1, State_, M, P, Xs).

%!  inference(+From, +State1, ?State2, ?Info)
%
%   This predicate performs an inference step from the initial state State1 to
%   the final step State2. Info is an atom containg information about the rule
%   used in the derivation.

inference(From, State, State_, Info) :-
    environment:current_fasill_flag(simplification_steps, term(true,[])),
    simplification_step(From, State, State_, Info),
	!.
inference(From, State, State_, Info) :-
    operational_step(From, State, State_, Info).
inference(From, state(Goal,Subs), State_, Info) :-
    interpretable(Goal),
    interpretive_step(From, state(Goal,Subs), State_, Info).

%!  operational_step(+From, +State1, ?State2, ?Info)
%
%   This predicate performs an admissible step from the state State1 to the
%   state State2. Info is an atom containg information about the rule used in
%   the derivation.

operational_step(From, State1, State2, Info) :-
    assertz(check_success),
    success_step(From, State1, State2, Info),
    retractall(check_success).
operational_step(_, State1, State2, Info) :-
    check_success,
    retractall(check_success),
    failure_step(State1, State2, Info).

%!  simplification_step(+From, +State1, ?State2, ?Info)
%
%   This predicate performs a successful admissible step from the state State1
%   to the state State2. Info is an atom containg information about the rule
%   used in the derivation.

simplification_step(_From, state(Goal,Subs), state(Goal2,Subs), 'IS*') :-
    environment:lattice_call_bot(Bot),
    environment:lattice_call_top(Top),
    deep_simplify(Bot, Top, Goal, Goal2),
    Goal \== Goal2.

%!  success_step(+From, +State1, ?State2, ?Info)
%
%   This predicate performs a successful admissible step from the state State1
%   to the state State2. Info is an atom containg information about the rule
%   used in the derivation.

success_step(From, state(Goal,Subs), state(Goal_,Subs_), Name2/Arity) :-
	select_atom(Goal, ExprVar, Var, Expr),
	Expr = term(Name, Args),
	length(Args, Arity),
	(Name = Name2 ; 
		(environment:current_fasill_flag(weak_unification, term(true, [])) -> 
			environment:lattice_call_bot(Bot),
			environment:similarity_between(Name, Name2, Arity, Sim, _),
			Name \= Name2, Sim \== Bot)
	),
	% Builtin predicate
	(builtin:is_builtin_predicate(Name2/Arity) -> (
		builtin:eval_builtin_predicate(Name2/Arity, state(Goal,Subs), selected(ExprVar, Var, Expr), state(Goal_,Subs_))
	) ; (
		% User-defined predicate
		(environment:program_has_predicate(Name2/Arity) -> (
			environment:lattice_tnorm(Tnorm),
			environment:lattice_call_top(Top),
			environment:program_clause(Name2/Arity, fasill_rule(head(Head), Body, _)),
			rename([Head,Body], [HeadR,BodyR]),
			unification:unify(Expr, HeadR, _, state(TD, SubsExpr)),
			(BodyR = empty ->
				Var = TD ;
				(	BodyR = body(Body_),
					(TD == Top ->
						Var = Body_ ;
						Var = term('&'(Tnorm), [TD,Body_])))),
			substitution:apply(SubsExpr, ExprVar, Goal_),
			substitution:compose(Subs, SubsExpr, Subs_)
		) ; (
			% Undefined predicate
			exceptions:existence_error(procedure, Name/Arity, From, Error),
			retractall(check_success),
			exceptions:throw_exception(Error)
		))
	)).

%!  failure_step(+State1, ?State2, ?Info)
%
%   This predicate performs an unsuccessful admissible step from the state
%   State1 to the state State2. Info is an atom containg information about the
%   failure.

failure_step(state(Goal,Subs), state(Goal_,Subs), 'FS') :-
	environment:current_fasill_flag(failure_steps, term(true, [])),
	environment:lattice_call_bot(Bot),
	select_atom(Goal, Goal_, Bot, _).

%!  short_interpretive_step(+From, +State1, ?State2, ?Info)
%
%   This predicate performs a short interpretive step from the state State1 to
%   the state State2. Info is an atom containg information about the
%   derivation. This steps only can be performed when there is no atoms to
%   perform admissible steps.

short_interpretive_step(From, state(Goal,Subs), state(TD,Subs), 'IS') :-
	deep_interpret(Goal,TD) ->
		true ;
		type_error(truth_degree, Goal, From, Error),
		throw_exception(Error).

%!  long_interpretive_step(+From, +State1, ?State2, ?Info)
%
% This predicate performs a long interpretive step from the state State1 to the
% state State2. Info is an atom containg information about the derivation. This
% steps only can be performed when there is no atoms to perform admissible
% steps.

long_interpretive_step(From, state(Goal,Subs), state(Goal_,Subs), 'is') :-
	select_expression(Goal, Goal_, Var, Expr) ->
		interpret(Expr, Var) ;
		type_error(truth_degree, Goal, From, Error),
		throw_exception(Error).

%!  interpretive_step(+From, +State1, ?State2, ?Info)
%
%   This predicate performs an interpretive step from the state State1 to the
%   state State2. Info is an atom containg information about the derivation.
%   This steps only can be performed when there is no atoms to perform
%   admissible steps.

interpretive_step(From, State1, State2, Info) :-
	environment:current_fasill_flag(interpretive_steps, term(short, [])),
	!,
	short_interpretive_step(From, State1, State2, Info).
interpretive_step(From, State1, State2, Info) :-
	long_interpretive_step(From, State1, State2, Info).

%!  interpret(+Expression, ?Result)
% 
%   This predicate interprets the expression Expression in the expression. 
%   Result is the resulting expression.

interpret(bot, Bot) :-
	!,
	environment:lattice_call_bot(Bot).
interpret(top, Top) :-
	!,
	environment:lattice_call_top(Top).
interpret(sup(X, Y), Z) :-
	!,
	environment:lattice_call_supremum(X, Y, Z).
interpret(term(Op, Args), Result) :-
	environment:lattice_call_connective(Op, Args, Result).

%!  deep_interpret(+Expression, ?Result)
% 
%   This predicate fully interprets the expression Expression in the expression.
%   Result is the resulting expression.

deep_interpret(X, X) :-
	environment:lattice_call_member(X),
	!.
deep_interpret(bot, Bot) :-
	!,
	environment:lattice_call_bot(Bot).
deep_interpret(top, Top) :-
	!,
	environment:lattice_call_top(Top).
deep_interpret(sup(X, Y), Z) :-
	!,
	environment:lattice_call_supremum(X, Y, Z).
deep_interpret(term(Op, Args), Result) :-
	Op =.. [F|_],
	once(member(F, ['&','|','@','#&','#|','#@','#?'])),
	maplist(deep_interpret, Args, Args2),
	catch((environment:lattice_call_connective(Op, Args2, Result) ; Result = term(Op, Args2)), _, Result = term(Op, Args2)),
	!.
deep_interpret(X, X).

%!  deep_simplify(+Bot, +Top, +Expression, ?Result)
% 
%   This predicate fully simplifies the expression Expression in the expression.
%   Result is the simplified expression.

deep_simplify(Bot, Top, term(Op, [X,Y]), Result) :- 
	Op =.. [F|_],
	once(member(F, ['&','#&'])),
	deep_simplify(Bot, Top, X, X2),
	((X2 == Bot ; X2 == bot) ->
		Result = Bot ;
		((X2 == Top ; X2 == top) ->
			deep_simplify(Bot, Top, Y, Result) ;
			deep_simplify(Bot, Top, Y, Y2),
			((Y2 == Bot ; Y2 == bot) ->
				Result = Bot ;
				((Y2 == Top ; Y2 == top) ->
					Result = X2 ;
					Result = term(Op, [X2,Y2]))))),
	!.
deep_simplify(Bot, Top, term(Op, [X,Y]), Result) :- 
	Op =.. [F|_],
	once(member(F, ['|','#|'])),
	deep_simplify(Bot, Top, X, X2),
	deep_simplify(Bot, Top, Y, Y2),
	((X2 == Bot ; X2 == bot) ->
		Result = Y2 ;
		((Y2 == Bot ; Y2 == bot) ->
			Result = X2 ;
			Result = term(Op, [X2,Y2]))),
	!.
deep_simplify(Bot, Top, term(Op, Args), term(Op, Args2)) :- 
	Op =.. [F|_],
	once(member(F, ['@','#@','#?'])),
	maplist(deep_simplify(Bot, Top), Args, Args2),
	!.
deep_simplify(_, _, X, X).

%!  up_body(+Expression, ?ExpressionUp)
%
%   ExpressionUp is the result of interpreting the expression with no atoms,
%   obtained from the body Expression by replacing each ocurrence of an atom
%   by the top of the current lattice.

up_body(Expr, ExprUp) :-
	select_atom(Expr, ExprTop, top, _),
	!,
	up_body(ExprTop, ExprUp).
up_body(Expr, ExprUp) :-
	deep_interpret(Expr, ExprUp).

%!  rename(+Expression, ?Renamed)
%
%   This predicate renames the expression Expression, replacing the variables
%   of the expression by fresh variables. Renamed is the expression Expression
%   with fresh variables.

rename(X, Y) :-
	substitution:empty_substitution(Sub),
	rename(X, Y, Sub, _).
rename(var('_'), var('_'), Sub, Sub) :-
	!.
rename(var(X), var(Y), Sub, Sub) :-
	substitution:get_substitution(Sub, X, Y),
	!.
rename(var(X), var('$'(Id)), Sub0, Sub1) :- 
	!,
	auto_fresh_variable_id(Id),
	substitution:put_substitution(Sub0, X, '$'(Id), Sub1).
rename(term(Name, Xs), term(Name, Ys), Sub0, Sub1) :-
	!, 
	rename(Xs, Ys, Sub0, Sub1).
rename([], [], Sub, Sub) :- !.
rename([X|Xs], [Y|Ys], Sub0, Sub3) :-
	!, rename(X, Y, Sub0, Sub2),
	rename(Xs, Ys, Sub2, Sub3).
rename(X, Y, Sub0, Sub1) :-
	compound(X),
	!,
	X =.. [Name|Args],
	rename(Args, Args_, Sub0, Sub1),
	Y =.. [Name|Args_].
rename(X, X, Sub, Sub).

%!  rename(+Variables, +Expression, ?Renamed)
%
%   This predicate renames the expression Expression, replacing the variables
%   in Variables by fresh variables. Renamed is the expression +Expression with
%   fresh variables.

rename(V, X, Y) :-
	substitution:empty_substitution(Sub),
	rename(V, X, Y, Sub, _).
rename(_, var('_'), var('_'), Sub, Sub) :-
	!.
rename(V, var(X), var(Y), Sub, Sub) :-
	member(var(X), V),
	substitution:get_substitution(Sub, X, Y),
	!.
rename(V, var(X), var('$'(Id)), Sub0, Sub1) :- 
	member(var(X), V),
	!,
	auto_fresh_variable_id(Id),
	substitution:put_substitution(Sub0, X, '$'(Id), Sub1).
rename(V, term(Name, Xs), term(Name, Ys), Sub0, Sub1) :-
	!,
	rename(V, Xs, Ys, Sub0, Sub1).
rename(_, [], [], Sub, Sub) :-
	!.
rename(V, [X|Xs], [Y|Ys], Sub0, Sub3) :-
	!,
	rename(V, X, Y, Sub0, Sub2),
	rename(V, Xs, Ys, Sub2, Sub3).
rename(V, X, Y, Sub0, Sub1) :-
	compound(X),
	!,
	X =.. [Name|Args],
	rename(V, Args, Args_, Sub0, Sub1),
	Y =.. [Name|Args_].
rename(_, X, X, Sub, Sub).

%!  is_rename(+Term1, +Term2)
%
%   This predicate succeeds when Term2 is a renamed version of Term1.

is_rename(X, Y) :-
	substitution:empty_substitution(Sub),
	is_rename(X, Y, Sub, _).
is_rename(var(X), var(Y), Sub1, Sub3) :-
	!,
	(\+substitution:get_substitution(Sub1, X, _),
		substitution:put_substitution(Sub1, X, Y, Sub2) ;
		substitution:get_substitution(Sub1, X, Y),
		Sub2 = Sub1),
	(\+substitution:get_substitution(Sub2, Y, _),
		substitution:put_substitution(Sub2, Y, X, Sub3) ;
		substitution:get_substitution(Sub2, Y, X),
		Sub3 = Sub2).
is_rename(term(Name, Args1), term(Name, Args2), Sub1, Sub2) :-
	!,
	is_rename(Args1, Args2, Sub1, Sub2).
is_rename([], [], Sub, Sub) :-
	!.
is_rename([X|Xs], [Y|Ys], Sub1, Sub3) :-
	!,
	is_rename(X, Y, Sub1, Sub2),
	is_rename(Xs, Ys, Sub2, Sub3).
is_rename(X, Y, Sub, Sub) :-
	X == Y.

%!  arithmetic_evaluation(+Indicator, +Expression, ?Result)
%
%   This predicate succeeds when ?Result is the result of evaluating the
%   expression +Expression. This predicate throws an arithmetical exception if
%   there is any problem.

arithmetic_evaluation(Indicator, var(_), _) :-
	!,
	exceptions:instantiation_error(Indicator, Error),
	exceptions:throw_exception(Error).
arithmetic_evaluation(_, num(X), num(X)) :-
	!.
arithmetic_evaluation(Indicator, term(Op,Args), Result) :-
	catch(
		(   maplist(arithmetic_evaluation(Indicator), Args, Args_),
			maplist(arithmetic_type, Args_, Types),
			maplist(to_prolog, Args_, Prolog),
			arithmetic_op(Op, Prolog, Types, Result),
			!
		), Error,
		(Error = type(Type, From) ->
			(from_prolog(From, From_), exceptions:type_error(Type, From_, Indicator, Exception), exceptions:throw_exception(Exception)) ;
			(Error = evaluation(Cause) ->
				(evaluation_error(Cause, Indicator, Exception), exceptions:throw_exception(Exception)) ;
				(Error = exception(Exception) -> exceptions:throw_exception(Exception) ;
					exceptions:throw_exception(Error)
				)
			)
		)
	).

%!  arithmetic_comparison(+Op, +Expression1, +Expression2)
%
%   This predicate succeeds when expressions Expression1 and Expression2,
%   evaluated as much as possible, fulfill the ordering relation Op.

arithmetic_comparison(Name/2, Expr1, Expr2) :-
	arithmetic_evaluation(Name/2, Expr1, Result1),
	arithmetic_evaluation(Name/2, Expr2, Result2),
	environment:to_prolog(Result1, Result1_),
	environment:to_prolog(Result2, Result2_),
	call(Name, Result1_, Result2_).

%!  arithmetic_type(+Number, ?Type)
%
%   This predicate succeeds when Number has the type Type (integer or float).

arithmetic_type(num(X), integer) :-
	integer(X).
arithmetic_type(num(X), float) :-
	float(X).

%!  arithmetic_op(+Operator, +Arguments, +Types, ?Result)
%
%   This predicate succeeds when Result is the result of evaluating the
%   operator Operator with the arguments Arguments with types Types.

arithmetic_op(pi, [], _, num(Z)) :- Z is pi.
arithmetic_op(e, [], _, num(Z)) :- Z is e.
arithmetic_op('+', [X,Y], _, num(Z)) :- Z is X+Y.
arithmetic_op('-', [X,Y], _, num(Z)) :- Z is X-Y.
arithmetic_op('*', [X,Y], _, num(Z)) :- Z is X*Y.
arithmetic_op('**', [X,Y], _, num(Z)) :- Z is float(X**Y).
arithmetic_op('/', [_,0], _, _) :- !, throw(evaluation(zero_division)).
arithmetic_op('/', [_,0.0], _, _) :- !, throw(evaluation(zero_division)).
arithmetic_op('/', [X,Y], _, num(Z)) :- Z is float(X/Y).
arithmetic_op('//', [X,_], [float,_], _) :- throw(type(integer, X)).
arithmetic_op('//', [_,Y], [_,float], _) :- throw(type(integer, Y)).
arithmetic_op('//', [_,0], _, _) :- !, throw(evaluation(zero_division)).
arithmetic_op('//', [_,0.0], _, _) :- !, throw(evaluation(zero_division)).
arithmetic_op('//', [X,Y], _, num(Z)) :- Z is X//Y.
arithmetic_op('+', [X], _, num(Z)) :- Z is X.
arithmetic_op('-', [X], _, num(Z)) :- Z is -X.
arithmetic_op(exp, [X], _, num(Z)) :- Z is exp(X).
arithmetic_op(sqrt, [X], _, num(Z)) :- Z is sqrt(X).
arithmetic_op(log, [X], _, num(Z)) :- X =< 0 -> throw(evaluation(undefined)) ; Z is log(X).
arithmetic_op(sin, [X], _, num(Z)) :- Z is sin(X).
arithmetic_op(cos, [X], _, num(Z)) :- Z is cos(X).
arithmetic_op(tan, [X], _, num(Z)) :- Z is tan(X).
arithmetic_op(asin, [X], _, num(Z)) :- Z is asin(X).
arithmetic_op(acos, [X], _, num(Z)) :- Z is acos(X).
arithmetic_op(atan, [X], _, num(Z)) :- Z is atan(X).
arithmetic_op(sign, [X], _, num(Z)) :- Z is sign(X).
arithmetic_op(float, [X], _, num(Z)) :- Z is float(X).
arithmetic_op(floor, [X], [integer], _) :- throw(type(float, X)).
arithmetic_op(floor, [X], _, num(Z)) :- Z is floor(X).
arithmetic_op(round, [X], [integer], _) :- throw(type(float, X)).
arithmetic_op(round, [X], _, num(Z)) :- Z is round(X).
arithmetic_op(truncate, [X], [integer], _) :- throw(type(float, X)).
arithmetic_op(truncate, [X], _, num(Z)) :- Z is truncate(X).
arithmetic_op(ceiling, [X], [integer], _) :- throw(type(float, X)).
arithmetic_op(ceiling, [X], _, num(Z)) :- Z is ceiling(X).
arithmetic_op(float_integer_part, [X], [integer], _) :- throw(type(float, X)).
arithmetic_op(float_integer_part, [X], _, num(Z)) :- Z is float_integer_part(X).
arithmetic_op(float_fractional_part, [X], [integer], _) :- throw(type(float, X)).
arithmetic_op(float_fractional_part, [X], _, num(Z)) :- Z is float_fractional_part(X).
arithmetic_op(abs, [X], _, num(Z)) :- Z is abs(X).
arithmetic_op(rem, [X,_], [float,_], _) :- throw(type(integer, X)).
arithmetic_op(rem, [_,Y], [_,float], _) :- throw(type(integer, Y)).
arithmetic_op(rem, [_,0], _, _) :- !, throw(evaluation(zero_division)).
arithmetic_op(rem, [X,Y], _, num(Z)) :- Z is rem(X,Y).
arithmetic_op(mod, [X,_], [float,_], _) :- throw(type(integer, X)).
arithmetic_op(mod, [_,Y], [_,float], _) :- throw(type(integer, Y)).
arithmetic_op(mod, [_,0], _, _) :- !, throw(evaluation(zero_division)).
arithmetic_op(mod, [X,Y], _, num(Z)) :- Z is mod(X,Y).
arithmetic_op(min, [X,Y], _, num(Z)) :- Z is min(X,Y).
arithmetic_op(max, [X,Y], _, num(Z)) :- Z is max(X,Y).
arithmetic_op('<<', [X,_], [float,_], _) :- throw(type(integer, X)).
arithmetic_op('<<', [_,Y], [_,float], _) :- throw(type(integer, Y)).
arithmetic_op('<<', [X,Y], _, num(Z)) :- Z is X << Y.
arithmetic_op('>>', [X,_], [float,_], _) :- throw(type(integer, X)).
arithmetic_op('>>', [_,Y], [_,float], _) :- throw(type(integer, Y)).
arithmetic_op('>>', [X,Y], _, num(Z)) :- Z is X >> Y.
arithmetic_op('\\/', [X,_], [float,_], _) :- throw(type(integer, X)).
arithmetic_op('\\/', [_,Y], [_,float], _) :- throw(type(integer, Y)).
arithmetic_op('\\/', [X,Y], _, num(Z)) :- Z is '\\/'(X,Y).
arithmetic_op('/\\', [X,_], [float,_], _) :- throw(type(integer, X)).
arithmetic_op('/\\', [_,Y], [_,float], _) :- throw(type(integer, Y)).
arithmetic_op('/\\', [X,Y], _, num(Z)) :- Z is '/\\'(X,Y).
arithmetic_op('\\', [X], [float], _) :- throw(type(integer, X)).
arithmetic_op('\\', [X], _, num(Z)) :- Z is '\\'(X).
arithmetic_op(Op, Args, _, _) :- length(Args, Length), throw(type(evaluable, Op/Length)).



% VARIABLES

%!  current_fresh_variable_id(?Identifier)
%
%   This predicate stores the current identifier Identifier to be used in a
%   fresh variable.
:- dynamic(current_fresh_variable_id/1).
?- retractall(current_fresh_variable_id(_)).
current_fresh_variable_id(1).

%!  auto_fresh_variable_id(?Identifier)
%
%   This predicate updates the current variable identifier Identifier and
%   returns it.

auto_fresh_variable_id(Id) :-
	current_fresh_variable_id(Id),
	retract(current_fresh_variable_id(_)),
	N is Id+1,
	assertz(current_fresh_variable_id(N)).

%!  reset_fresh_variable_id
%
%   This predicate resets the current Identifier identifier to the first.

reset_fresh_variable_id :-
	retract(current_fresh_variable_id(_)),
	assertz(current_fresh_variable_id(1)).