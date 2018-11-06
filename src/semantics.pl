:- module(semantics, [
    wmgu/3,
    query/2,
    derivation/4,
    inference/4,
    admissible_step/4,
    interpretive_step/3,
    apply/3,
    compose/3,
    rename/2,
    arithmetic_evaluation/2
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
wmgu(var(X), Y, state(TD,Subs), state(TD,[X/Y|Subs])) :- !.
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
    wmgu(Xs, Ys, StateXY, State_).



% DERIVATIONS

% select_atom/4
% select_atom(+Expression, ?ExprVar, ?Var, ?Atom)
%
% This predicate selects an atom ?Atom from the expression
% +Expression, where ?ExprVar is the expression +Expression
% with the variable ?Var instead of the atom ?Atom.
select_atom(term(Term, Args), term(Term, Args_), Var, Atom) :-
    ( (Term =.. [Op,_] ; Term =.. [Op]), member(Op, ['@','&','|']) ;
      member(Term, ['@','&','|']) ), !,
    select_atom(Args, Args_, Var, Atom).
select_atom(term(Term, Args), Var, Var, term(Term, Args)).
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
:- dynamic(check_success/0).
:- dynamic(check_cut/0).
query(Goal, Answer) :-
    retractall(check_success),
    retractall(check_cut),
    get_variables(Goal, Vars),
    derivation(top_level/0, state(Goal, Vars), Answer, _).

% get_variables/2
% get_variables(+Term, ?Variables)
%
% This predicate succeeds when ?Variables is the initial
% substitution for the term +Term, where each variable in
% +Term is replace by itself (X/X).
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
derivation(From, State, State_, [X|Xs]) :-
    catch(inference(From, State, State1, X), Error, (State1 = exception(Error), !)),
    (check_cut -> retractall(check_cut), ! ; true),
    derivation(X, State1, State_, Xs).
derivation(_, state(Goal,Subs), state(Goal,Subs), []) :-
    lattice_call_member(Goal).

% inference/4
% inference(+From, +State1, ?State2, ?Info)
%
% This predicate performs an inference step from the
% initial state +State1 to the final step ?State2. ?Info
% is an atom containg information about the rule used in
% the derivation.
inference(From, State, State_, Info) :- admissible_step(From, State, State_, Info).
inference(_, state(Goal,Subs), State_, Info) :- interpretable(Goal), interpretive_step(state(Goal,Subs), State_, Info).

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
        Info = Name/Arity,
        (Name/Arity = '!'/0 -> assertz(check_cut) ; true)
    ) ; (
        % User-defined predicate
        (program_has_predicate(Name/Arity) -> (
            lattice_tnorm(Tnorm),
            lattice_call_bot(Bot),
            program_clause(Name2/Arity, Rule),
            (Name = Name2 -> true ; similarity_between(Name, Name2, Arity, Sim), Sim \= Bot),
            Rule = fasill_rule(head(Head),Body,_),
            rename([Head,Body], [HeadR,BodyR]),
            wmgu(Expr, HeadR, state(TD,SubsExpr)),
            (BodyR = empty -> Var = TD ; (BodyR = body(Body_), Var = term('&'(Tnorm), [TD,Body_]))),
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
    select_atom(Goal, Goal_, bot, _).

% interpretive_step/3
% interpretive_step(+State1, ?State2, ?Info)
%
% This predicate performs an interpretive step from the
% state +State1 to the state ?State2 ?Info is an atom
% containg information about the derivation. This steps
% only can be performed when there is no atoms to perform
% admissible steps.
interpretive_step(state(Goal,Subs), state(Goal_,Subs), 'IS') :-
    select_expression(Goal, Goal_, Var, Expr),
    interpret(Expr, Var).

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

% arithmetic_evaluation/2
% arithmetic_evaluation(+Expression, ?Result)
%
% This predicate succeeds when ?Result is the result
% of evaluating the expression +Expression. This predicate
% throws an arithmetical exception if there is any problem.
arithmetic_evaluation(var(_), _) :- !, throw(instantiation).
arithmetic_evaluation(num(X), num(X)) :- !.
arithmetic_evaluation(term(Op,Args), Result) :-
    maplist(arithmetic_evaluation, Args, Args_),
    maplist(arithmetic_type, Args_, Types),
    maplist(to_prolog, Args_, Prolog),
    arithmetic_op(Op, Prolog, Types, Result), !.

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