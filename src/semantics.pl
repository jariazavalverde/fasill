/**
  * 
  * FILENAME: semantics.pl
  * DESCRIPTION: This module contains predicates implementing the semantics for FASILL.
  * AUTHORS: José Antonio Riaza Valverde
  * UPDATED: 15.11.2018
  * 
  **/



:- module(semantics, [
    wmgu/3,
    mgu/3,
    query/2,
    select_atom/4,
    select_expression/4,
    derivation/4,
    get_variables/2,
    inference/4,
    admissible_step/4,
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

:- use_module('environment').
:- use_module('exceptions').
:- use_module('builtin').



% UNIFICATION

% wmgu/3
% wmgu(+ExpressionA, +ExpressionB, ?State)
%
% This predicate returns the weak most general unifier (wmgu)
% ?State of the expressions +ExpressionA and +ExpressionB.
wmgu(ExprA, ExprB, State) :-
    lattice_call_top(Top),
    wmgu(ExprA, ExprB, state(Top,[]), State).
%%% var with expression
wmgu(var(X), Y, state(TD,Subs), State_) :-
    member(X/Z, Subs), !,
    wmgu(Z, Y, state(TD,Subs), State_).
wmgu(var(X), Y, state(TD,Subs), state(TD,[X/Y|Subs_])) :- !, compose(Subs,[X/Y],Subs_).
%%% expression with var
wmgu(X, var(Y), State, State_) :- !, wmgu(var(Y), X, State, State_).
%%% num with num
wmgu(num(X), num(X), State, State) :- !.
%%% term with term
wmgu(term(X,Xs), term(X,Ys), State, State_) :- !,
    length(Xs, Length),
    length(Ys, Length),
    wmgu(Xs, Ys, State, State_).
wmgu(term(X,Xs), term(Y,Ys), state(TD, Subs), State) :- !,
    length(Xs, Length),
    length(Ys, Length),
    similarity_between(X, Y, Length, TDxy),
    similarity_tnorm(Tnorm),
    lattice_call_connective('&'(Tnorm), [TD, TDxy], TD2),
    wmgu(Xs, Ys, state(TD2, Subs), State).
%%% arguments
wmgu([], [], State, State) :- !.
wmgu([X|Xs], [Y|Ys], State, State_) :- !,
    wmgu(X, Y, State, StateXY),
    StateXY = state(_,Subs),
    apply(Xs, Subs, Xs_),
    apply(Ys, Subs, Ys_),
    wmgu(Xs_, Ys_, StateXY, State_).


% mgu/3
% mgu(+ExpressionA, +ExpressionB, ?MGU)
%
% This predicate returns the most general unifier (mgu)
% ?MGU of the expressions +ExpressionA and +ExpressionB.
mgu(ExprA, ExprB, Subs) :-
    mgu(ExprA, ExprB, [], Subs).
%%% var with expression
mgu(var(X), Y, Subs, Subs_) :-
    member(X/Z, Subs), !,
    mgu(Z, Y, Subs, Subs_).
mgu(var(X), Y, Subs, [X/Y|Subs_]) :- !, compose(Subs,[X/Y],Subs_).
%%% expression with var
mgu(X, var(Y), Subs, Subs_) :- !, mgu(var(Y), X, Subs, Subs_).
%%% num with num
mgu(num(X), num(X), Subs, Subs) :- !.
%%% term with term
mgu(term(X,Xs), term(X,Ys), Subs, Subs_) :- !,
    length(Xs, Length),
    length(Ys, Length),
    mgu(Xs, Ys, Subs, Subs_).
%%% arguments
mgu([], [], Subs, Subs) :- !.
mgu([X|Xs], [Y|Ys], Subs1, Subs3) :- !,
    mgu(X, Y, Subs1, Subs2),
    apply(Xs, Subs2, Xs_),
    apply(Ys, Subs2, Ys_),
    mgu(Xs_, Ys_, Subs2, Subs3).



% DERIVATIONS

% is_fuzzy_computed_answer/1
% is_fuzzy_computed_answer(+Expression)
%
% This predicate succeeds when +Expression is
% a (symbolic) fuzzy computed answer.
is_fuzzy_computed_answer(X) :- interpretable(X), \+select_expression(X, _, _, _).

% select_atom/4
% select_atom(+Expression, ?ExprVar, ?Var, ?Atom)
%
% This predicate selects an atom ?Atom from the expression
% +Expression, where ?ExprVar is the expression +Expression
% with the variable ?Var instead of the atom ?Atom.
select_atom(term(Term, Args), term(Term, Args_), Var, Atom) :-
    (Term =.. [Op,_] ; Term =.. [Op]), member(Op, ['@','&','|','#@','#&','#|']), !,
    select_atom(Args, Args_, Var, Atom).
select_atom(term(Term, Args), Var, Var, term(Term, Args)) :-
    Term =.. ['#',_] -> fail ;
    \+lattice_call_member(term(Term, Args)).
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
    ( (Term =.. [Op,_] ; Term =.. [Op]), member(Op, ['@','&','|']) ;
      member(Term, ['@','&','|']) ),
    maplist(lattice_call_member, Args), !.
select_expression(term(Term, Args), term(Term, Args_), Var, Expr) :- select_expression(Args, Args_, Var, Expr).
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
:- dynamic(check_success/0, trace_derivation/1, trace_level/1).
query(Goal, Answer) :-
    retractall(check_success),
    retractall(trace_derivation),
    retractall(trace_level(_)),
    assertz(trace_level(0)),
    get_variables(Goal, Vars),
    State = state(Goal, Vars),
    (current_fasill_flag(trace, true) -> assertz(trace_derivation(trace(0, 'GOAL', State))) ; true),
    derivation(top_level/0, State, Answer, _).

% get_variables/2
% get_variables(+Term, ?Variables)
%
% This predicate succeeds when ?Variables is the initial
% substitution for the term +Term, where each variable in
% +Term is replaced by itself (X/X).
get_variables(X, Z) :- get_variables2(X, Y), list_to_set(Y, Z).
get_variables2(var(X), [X/var(X)]) :- !.
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
    catch(
        (is_fuzzy_computed_answer(Goal), State = state(Goal, Subs)),
        Error,
        State = exception(Error)
    ), !.
derivation(From, State, State_, [X|Xs]) :-
    (trace_level(Level) -> Level_ is Level+1 ; Level_ = false),
    catch(inference(From, State, State1, X), Error, (State1 = exception(Error), !)),
    (current_fasill_flag(trace, true), State1 \= exception(_) -> assertz(trace_derivation(trace(Level_, X, State1))) ; true),
    ( Level_\= false -> retractall(trace_level(_)), assertz(trace_level(Level_)) ; true),
    derivation(X, State1, State_, Xs).

% inference/4
% inference(+From, +State1, ?State2, ?Info)
%
% This predicate performs an inference step from the
% initial state +State1 to the final step ?State2. ?Info
% is an atom containg information about the rule used in
% the derivation.
inference(From, State, State_, Info) :- admissible_step(From, State, State_, Info).
inference(From, state(Goal,Subs), State_, Info) :- interpretable(Goal), interpretive_step(From, state(Goal,Subs), State_, Info).

% admissible_step/4
% admissible_step(+From, +State1, ?State2, ?Info)
%
% This predicate performs an admissible step from the
% state +State1 to the state ?State2. ?Info is an atom
% containg information about the rule used in the derivation.
admissible_step(From, State1, State2, Info) :-
    assertz(check_success),
    success_step(From, State1, State2, Info),
    retractall(check_success).
admissible_step(_, State1, State2, Info) :-
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
success_step(From, state(Goal,Subs), state(Goal_,Subs_), Info) :-
    select_atom(Goal, ExprVar, Var, Expr),
    Expr = term(Name, Args),
    length(Args, Arity),
    % Builtin predicate
    (is_builtin_predicate(Name/Arity) -> (
        eval_builtin_predicate(Name/Arity, state(Goal,Subs), selected(ExprVar, Var, Expr), state(Goal_,Subs_)),
        Info = Name/Arity
    ) ; (
        % User-defined predicate
        (program_has_predicate(Name/Arity) -> (
            lattice_tnorm(Tnorm),
            lattice_call_bot(Bot),
            lattice_call_top(Top),
            program_clause(Name2/Arity, Rule),
            (Name = Name2 -> true ; similarity_between(Name, Name2, Arity, Sim), Sim \= Bot),
            Rule = fasill_rule(head(Head),Body,_),
            rename([Head,Body], [HeadR,BodyR]),
            wmgu(Expr, HeadR, state(TD,SubsExpr)),
            (BodyR = empty -> Var = TD ; (
                BodyR = body(Body_),
                (TD == Top -> Var = Body_ ; Var = term('&'(Tnorm), [TD,Body_]))
            )),
            apply(ExprVar, SubsExpr, Goal_),
            compose(Subs, SubsExpr, Subs_),
            Info = Name2/Arity
        ) ; (
            % Undefined predicate
            existence_error(procedure, Name/Arity, From, Error),
            Info = Name/Arity,
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
interpret(term(Op, Args), Result) :- lattice_call_connective(Op, Args, Result).

% rename/2
% rename(+Expression, ?Renamed)
%
% This predicate renames the expression +Expression, replacing
% the variables of the expression by fresh variables. ?Renamed
% is the expression +Expression with fresh variables.
rename(X, Y) :- rename(X, Y, [], _).
rename(var(X), var(Y), Subs, Subs) :- member(X/Y, Subs), !.
rename(var(X), var(Y), Subs, [X/Y|Subs]) :- 
    !, auto_fresh_variable_id(Id),
    atom_number(Atom, Id),
    atom_concat('V', Atom, Y).
rename(term(Name, Xs), term(Name, Ys), Subs, Subs_) :-
    !, rename(Xs, Ys, Subs, Subs_).
rename([], [], Subs, Subs) :- !.
rename([X|Xs], [Y|Ys], Subs, Subs3) :-
    !, rename(X, Y, Subs, Subs2),
    rename(Xs, Ys, Subs2, Subs3).
rename(X, Y, Subs, Subs_) :-
    compound(X), !,
    X =.. [Name|Args],
    rename(Args, Args_, Subs, Subs_),
    Y =.. [Name|Args_].
rename(X, X, Subs, Subs).

% compose/3
% compose(+Substitution1, +Substitution2, ?SubstitutionOut)
%
% This predicate composes both substitutions, +Substitution1
% and +Substitution2 in ?SubstitutionOut.
compose([], _, []).
compose([X/Y|T], Subs, [X/Z|S]) :- apply(Y, Subs, Z), compose(T, Subs, S).

% apply/3
% apply(+ExpressionIn, +Substitution, ?ExpressionOut)
%
% This predicate applies the substitution +Substitution to
% the expression +ExpressionIn. ?ExpressionOut is the resulting
% expression.
apply(term(T,Args), Subs, term(T,Args_)) :- !, apply(Args, Subs, Args_).
apply(var(X), Subs, Y) :- !, (member(X/Y, Subs) -> true ; Y = var(X)).
apply([X|Xs], Subs, [Y|Ys]) :- !, apply(X, Subs, Y), apply(Xs, Subs, Ys).
apply(X, _, X).

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