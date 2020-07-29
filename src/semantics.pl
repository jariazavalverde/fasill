/**
  * 
  * FILENAME: semantics.pl
  * DESCRIPTION: This module contains predicates implementing the semantics for FASILL.
  * AUTHORS: José Antonio Riaza Valverde
  * UPDATED: 11.03.2020
  * 
  **/



:- module(semantics, [
    lambda_wmgu/5,
    wmgu/4,
    mgu/4,
    unify/4,
    query/2,
    select_atom/4,
    select_expression/4,
    derivation/4,
    get_variables/2,
    inference/4,
    operational_step/4,
    interpretive_step/4,
    failure_step/3,
    apply/3,
    compose/3,
    rename/2,
    arithmetic_evaluation/3,
    arithmetic_comparison/3,
    trace_derivation/1,
    trace_level/1
]).

:- use_module(library(assoc)).
:- use_module('environment').
:- use_module('exceptions').
:- use_module('builtin').



% UNIFICATION

% lambda_wmgu/5
% lambda_wmgu(+ExpressionA, +ExpressionB, +Threshold, +OccursCheck, ?State)
%
% This predicate returns the thresholded weak most general unifier
% (lambda-wmgu) ?State of the expressions +ExpressionA and
% +ExpressionB with level +Threshold.
lambda_wmgu(ExprA, ExprB, Lambda, OccursCheck, State) :-
    lattice_call_top(Top),
    empty_assoc(Subs),
    lambda_wmgu(ExprA, ExprB, Lambda, OccursCheck, state(Top,Subs), State).
%%% anonymous variable
lambda_wmgu(var('_'), _, _, _, State, State) :- !.
lambda_wmgu(_, var('_'), _, _, State, State) :- !.
%%% var with expression
lambda_wmgu(var(X), Y, Lambda, OccursCheck, state(TD,Subs), State_) :-
    get_assoc(X, Subs, Z), !,
    lambda_wmgu(Z, Y, Lambda, OccursCheck, state(TD,Subs), State_).
lambda_wmgu(var(X), Y, _, OccursCheck, state(TD,Subs0), state(TD,Subs3)) :- !,
    (OccursCheck == true -> occurs_check(X, Y) ; true),
    list_to_assoc([X-Y], Subs1),
    compose(Subs0, Subs1, Subs2),
    put_assoc(X, Subs2, Y, Subs3).
%%% expression with var
lambda_wmgu(X, var(Y), Lambda, OccursCheck, State, State_) :- !,
    lambda_wmgu(var(Y), X, Lambda, OccursCheck, State, State_).
%%% num with num
lambda_wmgu(num(X), num(X), _, _, State, State) :- !.
%%% term with term
lambda_wmgu(term(X,Xs), term(X,Ys), Lambda, OccursCheck, State, State_) :- !,
    length(Xs, Arity),
    length(Ys, Arity),
    lambda_wmgu(Xs, Ys, Lambda, OccursCheck, State, State_).
lambda_wmgu(term(X,Xs), term(Y,Ys), Lambda, OccursCheck, state(TD, Subs), State) :- !,
    length(Xs, Arity),
    length(Ys, Arity),
    similarity_between(X, Y, Arity, TDxy, S),
    lattice_call_top(Top),
    (TD == Top -> TD2 = TDxy; 
        (TDxy == Top -> TD2 = TD; 
            (similarity_tnorm(Tnorm),
                ((S == no, Tnorm = '&'(_)) ->
                    lattice_call_connective(Tnorm, [TD, TDxy], TD2),
                    lattice_call_leq(Lambda, TD2)
                    ; TD2 = term(Tnorm, [TD, TDxy])
                )
            )
        )
    ),
    lattice_call_bot(Bot),
    TD2 \== Bot,
    lambda_wmgu(Xs, Ys, Lambda, OccursCheck, state(TD2, Subs), State).
%%% arguments
lambda_wmgu([], [], _, _, State, State) :- !.
lambda_wmgu([X|Xs], [Y|Ys], Lambda, OccursCheck, State, State_) :- !,
    lambda_wmgu(X, Y, Lambda, OccursCheck, State, StateXY),
    StateXY = state(_, Subs),
    apply(Subs, Xs, Xs_),
    apply(Subs, Ys, Ys_),
    lambda_wmgu(Xs_, Ys_, Lambda, OccursCheck, StateXY, State_).

% wmgu/4
% wmgu(+ExpressionA, +ExpressionB, +OccursCheck, ?State)
%
% This predicate returns the weak most general unifier (wmgu)
% ?State of the expressions +ExpressionA and +ExpressionB.
wmgu(ExprA, ExprB, OccursCheck, State) :-
    lattice_call_bot(Bot),
    lambda_wmgu(ExprA, ExprB, Bot, OccursCheck, State).

% mgu/4
% mgu(+ExpressionA, +ExpressionB, +OccursCheck, ?MGU)
%
% This predicate returns the most general unifier (mgu)
% ?MGU of the expressions +ExpressionA and +ExpressionB.
mgu(ExprA, ExprB, OccursCheck, Subs1) :-
    empty_assoc(Subs0),
    mgu(ExprA, ExprB, OccursCheck, Subs0, Subs1).
%%% anonymous variable
mgu(var('_'), _, _, Subs, Subs) :- !.
mgu(_, var('_'), _, Subs, Subs) :- !.
%%% var with expression
mgu(var(X), Y, OccursCheck, Subs0, Subs1) :-
    get_assoc(X, Subs0, Z), !,
    mgu(Z, Y, OccursCheck, Subs0, Subs1).
mgu(var(X), Y, OccursCheck, Subs0, Subs3) :- !,
    (OccursCheck == true -> occurs_check(X, Y) ; true),
    list_to_assoc([X-Y], Subs1),
    compose(Subs0, Subs1, Subs2),
    put_assoc(X, Subs2, Y, Subs3).
%%% expression with var
mgu(X, var(Y), OccursCheck, Subs0, Subs1) :- !,
    mgu(var(Y), X, OccursCheck, Subs0, Subs1).
%%% num with num
mgu(num(X), num(X), _, Subs, Subs) :- !.
%%% term with term
mgu(term(X,Xs), term(X,Ys), OccursCheck, Subs0, Subs1) :- !,
    length(Xs, Length),
    length(Ys, Length),
    mgu(Xs, Ys, OccursCheck, Subs0, Subs1).
%%% arguments
mgu([], [], _, Subs, Subs) :- !.
mgu([X|Xs], [Y|Ys], OccursCheck, Subs0, Subs2) :- !,
    mgu(X, Y, OccursCheck, Subs0, Subs1),
    apply(Subs1, Xs, Xs_),
    apply(Subs1, Ys, Ys_),
    mgu(Xs_, Ys_, OccursCheck, Subs1, Subs2).

% occurs_check/2
% occurs_check(+Variable, +Expression)
%
% This predicate succeds when +Expression does not contain
% the variable +Variable.
occurs_check(Var, var(Var)) :- !, fail.
occurs_check(Var, term(_, Xs)) :- !, maplist(occurs_check(Var), Xs).
occurs_check(_, _).

% unify/4
% unify(+ExpressionA, +ExpressionB, +OccursCheck, ?State)
%
% This predicate returns the unification ?State of
% expressions +ExpressionA and ExpressionB using
% the (possible weak) unification algorithm.
unify(Term1, Term2, OccursCheck, Subs) :-
    current_fasill_flag(weak_unification, term(true,[])), !,
    current_fasill_flag(lambda_unification, Lambda_),
    (var(OccursCheck) -> current_fasill_flag(occurs_check, term(OccursCheck, [])) ; true),
    (Lambda_ == bot ->
        lattice_call_bot(Lambda) ;
        (Lambda_ == top ->
            lattice_call_top(Lambda) ; 
            Lambda = Lambda_
        )
    ),
    lambda_wmgu(Term1, Term2, Lambda, OccursCheck, Subs).
unify(Term1, Term2, OccursCheck, state(Top, Subs)) :-
    (var(OccursCheck) -> current_fasill_flag(occurs_check, term(OccursCheck, [])) ; true),
    mgu(Term1, Term2, OccursCheck, Subs),
    lattice_call_top(Top).



% DERIVATIONS

% is_fuzzy_computed_answer/1
% is_fuzzy_computed_answer(+Expression)
%
% This predicate succeeds when +Expression is
% a (symbolic) fuzzy computed answer.
is_fuzzy_computed_answer(X) :-
    current_fasill_flag(symbolic, term(false, [])), !,
    lattice_call_member(X).
is_fuzzy_computed_answer(X) :-
    interpretable(X),
    \+select_expression(X, _, _, _).

% select_atom/4
% select_atom(+Expression, ?ExprVar, ?Var, ?Atom)
%
% This predicate selects an atom ?Atom from the expression
% +Expression, where ?ExprVar is the expression +Expression
% with the variable ?Var instead of the atom ?Atom.
select_atom(term(Term, Args), term(Term, Args_), Var, Atom) :-
    functor(Term, Op, _),
    member(Op, ['@','&','|','#@','#&','#|','#/','#?']), !,
    select_atom(Args, Args_, Var, Atom).
select_atom(term(Term, Args), Var, Var, term(Term, Args)) :-
    \+functor(Term, '#', 1),
    \+lattice_call_member(term(Term, Args)), !.
select_atom([Term|Args], [Term_|Args], Var, Atom) :- select_atom(Term, Term_, Var, Atom), !.
select_atom([Term|Args], [Term|Args_], Var, Atom) :- select_atom(Args, Args_, Var, Atom).

% select_expression/4
% select_expression(+Expression, ?ExprVar, ?Var, ?Atom)
%
% This predicate selects an interpretable expression ?Atom
% from the expression +Expression, where ?ExprVar is the
% expression +Expression with the variable ?Var instead of
% the atom ?Atom.
select_expression(top, Var, Var, top) :- !.
select_expression(bot, Var, Var, bot) :- !.
select_expression(term(Term, Args), Var, Var, term(Term, Args)) :-
    functor(Term, Op, _),
    once(member(Op, ['@','&','|'])),
    maplist(lattice_call_member, Args), !.
select_expression(term(Term, Args), term(Term, Args_), Var, Expr) :- select_expression(Args, Args_, Var, Expr).
select_expression(sup(X, Y), Var, Var, sup(X, Y)) :-
    lattice_call_member(X),
    lattice_call_member(Y), !.
select_expression(sup(X, Y), ExprVar, Var, Atom) :- select_expression([X,Y], ExprVar, Var, Atom), !.
select_expression([Term|Args], [Term_|Args], Var, Atom) :- select_expression(Term, Term_, Var, Atom), !.
select_expression([Term|Args], [Term|Args_], Var, Atom) :- select_expression(Args, Args_, Var, Atom).

% interpretable/1
% interpretable(+Expression)
%
% This predicate succeeds when the expression +Expression
% can be interpreted (i.e., there is no atoms in the expression).
interpretable(Expr) :- \+select_atom(Expr, _, _, _).

% query/2
% query(+Goal, ?Answer)
%
% This predicate succeeds when ?Answer is a fuzzy computed
% answer (fca) for the goal +Goal. A fca is a term of the
% form state(TD, Substitution), where TD is the truth degree.
:- dynamic check_success/0, trace_derivation/1, trace_level/1.
query(Goal, Answer) :-
    retractall(check_success),
    retractall(trace_derivation),
    retractall(trace_level(_)),
    assertz(trace_level(0)),
    get_variables(Goal, Vars),
    State = state(Goal, Vars),
    (current_fasill_flag(trace, term(true,[])) -> assertz(trace_derivation(trace(0, 'GOAL', State))) ; true),
    derivation(top_level/0, State, Answer, _).

% get_variables/2
% get_variables(+Term, ?Variables)
%
% This predicate succeeds when ?Variables is the initial
% substitution for the term +Term, where each variable in
% +Term is replaced by itself (X/X).
get_variables(X, Z) :- get_variables2(X, Y), list_to_set(Y, S), list_to_assoc(S, Z).
get_variables2(var(X), [X-var(X)]) :- !.
get_variables2(term(_,Args), Vars) :- !, get_variables2(Args, Vars).
get_variables2([H|T], Vars) :- !,
    get_variables2(H, Vh),
    get_variables2(T, Vt),
    append(Vh, Vt, Vars).
get_variables2(_,[]).

% derivation/4
% derivation(+From, +State1, ?State2, ?Info)
%
% This predicate performs a complete derivation from
% an initial state ?State1 to the final state ?State2,
% using the program +Program. ?Info is a list containing
% the information of each step.
derivation(_, exception(Error), exception(Error), []) :- !.
derivation(_, state(Goal,Subs), State, []) :-
    is_fuzzy_computed_answer(Goal), !,
    lattice_call_bot(Bot),
    (Bot == Goal -> current_fasill_flag(failure_steps, term(true, [])) ; true),
    State = state(Goal, Subs).
derivation(From, State, State_, [X|Xs]) :-
    (trace_level(Level) -> Level_ is Level+1 ; Level_ = false),
    catch(inference(From, State, State1, X), Error, (State1 = exception(Error), !)),
    (current_fasill_flag(trace, term(true,[])), State1 \= exception(_) -> assertz(trace_derivation(trace(Level_, X, State1))) ; true),
    ( Level_\= false -> retractall(trace_level(_)), assertz(trace_level(Level_)) ; true),
    derivation(From, State1, State_, Xs).

% inference/4
% inference(+From, +State1, ?State2, ?Info)
%
% This predicate performs an inference step from the
% initial state +State1 to the final step ?State2. ?Info
% is an atom containg information about the rule used in
% the derivation.
inference(From, State, State_, Info) :-
    operational_step(From, State, State_, Info).
inference(From, state(Goal,Subs), State_, Info) :-
    interpretable(Goal),
    interpretive_step(From, state(Goal,Subs), State_, Info).

% operational_step/4
% operational_step(+From, +State1, ?State2, ?Info)
%
% This predicate performs an admissible step from the
% state +State1 to the state ?State2. ?Info is an atom
% containg information about the rule used in the derivation.
operational_step(From, State1, State2, Info) :-
    assertz(check_success),
    success_step(From, State1, State2, Info),
    retractall(check_success).
operational_step(_, State1, State2, Info) :-
    check_success,
    retractall(check_success),
    failure_step(State1, State2, Info).

% success_step/4
% success_step(+From, +State1, ?State2, ?Info)
%
% This predicate performs a successful admissible step
% from the state +State1 to the state ?State2. ?Info is
% an atom containg information about the rule used in
% the derivation.
success_step(From, state(Goal,Subs), state(Goal_,Subs_), Name2/Arity) :-
    select_atom(Goal, ExprVar, Var, Expr),
    Expr = term(Name, Args),
    length(Args, Arity),
    (Name = Name2 ; 
        (current_fasill_flag(weak_unification, term(true, [])) -> 
            lattice_call_bot(Bot),
            similarity_between(Name, Name2, Arity, Sim, _),
            Name \= Name2, Sim \== Bot)
    ),
    % Builtin predicate
    (is_builtin_predicate(Name2/Arity) -> (
        eval_builtin_predicate(Name2/Arity, state(Goal,Subs), selected(ExprVar, Var, Expr), state(Goal_,Subs_))
    ) ; (
        % User-defined predicate
        (program_has_predicate(Name2/Arity) -> (
            lattice_tnorm(Tnorm),
            lattice_call_top(Top),
            program_clause(Name2/Arity, fasill_rule(head(Head), Body, _)),
            rename([Head,Body], [HeadR,BodyR]),
            unify(Expr, HeadR, _, state(TD, SubsExpr)),
            (BodyR = empty -> Var = TD ; (
                BodyR = body(Body_),
                (TD == Top -> Var = Body_ ; Var = term('&'(Tnorm), [TD,Body_]))
            )),
            apply(SubsExpr, ExprVar, Goal_),
            compose(Subs, SubsExpr, Subs_)
        ) ; (
            % Undefined predicate
            existence_error(procedure, Name/Arity, From, Error),
            retractall(check_success),
            throw_exception(Error)
        ))
    )).

% failure_step/3
% failure_step(+State1, ?State2, ?Info)
%
% This predicate performs an unsuccessful admissible step
% from the state +State1 to the state ?State2. ?Info is an
% atom containg information about the failure.
failure_step(state(Goal,Subs), state(Goal_,Subs), 'FS') :-
    current_fasill_flag(failure_steps, term(true, [])),
    lattice_call_bot(Bot),
    select_atom(Goal, Goal_, Bot, _).

% interpretive_step/4
% interpretive_step(+From, +State1, ?State2, ?Info)
%
% This predicate performs an interpretive step from the
% state +State1 to the state ?State2 ?Info is an atom
% containg information about the derivation. This steps
% only can be performed when there is no atoms to perform
% admissible steps.
interpretive_step(From, state(Goal,Subs), state(Goal_,Subs), 'IS') :-
    ( select_expression(Goal, Goal_, Var, Expr) -> interpret(Expr, Var) ; (
        type_error(truth_degree, Goal, From, Error),
        throw_exception(Error)
    )).

% interpret/2
% interpret(+Expression, ?Result)
% 
% This predicate interprets the expression +Expression
% in the expression. ?Result is the resulting expression.
interpret(bot, Bot) :- !, lattice_call_bot(Bot).
interpret(top, Top) :- !, lattice_call_top(Top).
interpret(sup(X, Y), Z) :- !, lattice_call_supremum(X, Y, Z).
interpret(term(Op, Args), Result) :- lattice_call_connective(Op, Args, Result).

% rename/2
% rename(+Expression, ?Renamed)
%
% This predicate renames the expression +Expression, replacing
% the variables of the expression by fresh variables. ?Renamed
% is the expression +Expression with fresh variables.
rename(X, Y) :-
    empty_assoc(Subs),
    rename(X, Y, Subs, _).
rename(var('_'), var('_'), Subs, Subs) :- !.
rename(var(X), var(Y), Subs, Subs) :-
    get_assoc(X, Subs, Y), !.
rename(var(X), var('$'(Id)), Subs0, Subs1) :- 
    !, auto_fresh_variable_id(Id),
    put_assoc(X, Subs0, '$'(Id), Subs1).
rename(term(Name, Xs), term(Name, Ys), Subs0, Subs1) :-
    !, rename(Xs, Ys, Subs0, Subs1).
rename([], [], Subs, Subs) :- !.
rename([X|Xs], [Y|Ys], Subs0, Subs3) :-
    !, rename(X, Y, Subs0, Subs2),
    rename(Xs, Ys, Subs2, Subs3).
rename(X, Y, Subs0, Subs1) :-
    compound(X), !,
    X =.. [Name|Args],
    rename(Args, Args_, Subs0, Subs1),
    Y =.. [Name|Args_].
rename(X, X, Subs, Subs).

% compose/3
% compose(+Substitution1, +Substitution2, ?SubstitutionOut)
%
% This predicate composes both substitutions, +Substitution1
% and +Substitution2 in ?SubstitutionOut.
compose(Subs0, Subs1, Subs2) :- map_assoc(apply(Subs1), Subs0, Subs2).

% apply/3
% apply(+Substitution, +ExpressionIn, ?ExpressionOut)
%
% This predicate applies the substitution +Substitution to
% the expression +ExpressionIn. ?ExpressionOut is the resulting
% expression.
apply(Subs, term(T,Args), term(T,Args_)) :- !, apply(Subs, Args, Args_).
apply(Subs, var(X), Y) :- !, (get_assoc(X, Subs, Y) -> true ; Y = var(X)).
apply(Subs, [X|Xs], [Y|Ys]) :- !, apply(Subs, X, Y), apply(Subs, Xs, Ys).
apply(_, X, X).

% arithmetic_evaluation/3
% arithmetic_evaluation(+Indicator, +Expression, ?Result)
%
% This predicate succeeds when ?Result is the result
% of evaluating the expression +Expression. This predicate
% throws an arithmetical exception if there is any problem.
arithmetic_evaluation(Indicator, var(_), _) :- !,
    instantiation_error(Indicator, Error),
    throw_exception(Error).
arithmetic_evaluation(_, num(X), num(X)) :- !.
arithmetic_evaluation(Indicator, term(Op,Args), Result) :-
    catch(
        (   maplist(arithmetic_evaluation(Indicator), Args, Args_),
            maplist(arithmetic_type, Args_, Types),
            maplist(to_prolog, Args_, Prolog),
            arithmetic_op(Op, Prolog, Types, Result), !
        ), Error,
        (Error = type(Type, From) ->
            (from_prolog(From, From_), type_error(Type, From_, Indicator, Exception), throw_exception(Exception)) ;
            (Error = evaluation(Cause) ->
                (evaluation_error(Cause, Indicator, Exception), throw_exception(Exception)) ;
                (Error = exception(Exception) -> throw_exception(Exception) ;
                    throw_exception(Error)
                )
            )
        )
    ).

% arithmetic_comparison/3
% arithmetic_comparison(+Op, +Expression1, +Expression2)
%
% This predicate succeeds when expressions +Expression1 and
% +Expression2, evaluated as much as possible, fulfill the
% ordering relation +Op.
arithmetic_comparison(Name/2, Expr1, Expr2) :-
    arithmetic_evaluation(Name/2, Expr1, Result1),
    arithmetic_evaluation(Name/2, Expr2, Result2),
    to_prolog(Result1, Result1_),
    to_prolog(Result2, Result2_),
    call(Name, Result1_, Result2_).

% arithmetic_type/2
% arithmetic_type(+Number, ?Type)
%
% This predicate succeeds when +Number has the type
% ?Type (integer or float).
arithmetic_type(num(X), integer) :- integer(X).
arithmetic_type(num(X), float) :- float(X).

% arithmetic_op/2
% arithmetic_op(+Operator, +Arguments, +Types, ?Result)
%
% This predicate succeeds when ?Result is the result
% of evaluating the operator +Operator with the arguments
% +Arguments with types +Types.
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

% current_fresh_variable_id/1
% current_fresh_variable_id(?Identifier)
%
% This predicate stores the current identifier ?Identifier
% to be used in a fresh variable.
:- dynamic(current_fresh_variable_id/1).
?- retractall(current_fresh_variable_id(_)).
current_fresh_variable_id(1).

% auto_fresh_variable_id/1
% auto_fresh_variable_id(?Identifier)
%
% This predicate updates the current variable identifier 
% ?Identifier and returns it.
auto_fresh_variable_id(Id) :-
    current_fresh_variable_id(Id),
    retract(current_fresh_variable_id(_)),
    N is Id+1,
    assertz(current_fresh_variable_id(N)).

% reset_fresh_variable_id/0
% reset_fresh_variable_id
%
% This predicate resets the current ?Identifier identifier
% to the first.
reset_fresh_variable_id :-
    retract(current_fresh_variable_id(_)),
    assertz(current_fresh_variable_id(1)).