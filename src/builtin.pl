:- module(builtin, [
    is_builtin_predicate/1,
    eval_builtin_predicate/4
]).

:- use_module('environment').
:- use_module('exceptions').
:- use_module('semantics').



% is_builtin_predicate/1
% is_builtin_predicate(?Indicator)
%
% This predicate succeeds when ?Indicator is the
% indicator of a builtin predicate of FASILL. An indicator
% is a term of the form Name/Arity, where Name is an atom
% and Arity is a non-negative integer.
is_builtin_predicate(Name/Arity) :-
    member(Name/Arity, [
        % term unification
        '='/2,
        % arithmetic evaluation
        is/2,
        % type testing
        atom/1,
        compound/1,
        number/1,
        integer/1,
        float/1,
        var/1,
        nonvar/1,
        % atom processing
        atom_length/2,
        atom_concat/3
    ]).



% eval_builtin_predicate/4
% is_builtin_predicate(+Indicator, +State1, +Atom, ?State2)
%
% This predicate succeeds when +Indicator is the
% indicator of a builtin predicate of FASILL, and
% ?State2 is the resulting state of performing a
% step over the state +State1 with selected atom
% +Atom whose indicator is +Indicator.



% TERM UNIFICATION

% '='/2
% '='(@term, @term)
eval_builtin_predicate('='/2, state(_, Subs), selected(ExprVar, TD, Term), state(ExprSubs, Subs_)) :-
    Term = term('=', [X,Y]),
    wmgu(X, Y, state(TD, SubsUnification)),
    apply(ExprVar, SubsUnification, ExprSubs),
    compose(Subs, SubsUnification, Subs_).



% ARITHMETIC EVALUATION

% is/2
% is(?term, @evaluable)
eval_builtin_predicate(is/2, state(_, Subs), selected(ExprVar, Var, Atom), state(ExprVar, Subs)) :-
    Atom = term(is, [Variable, Expression]),
    catch(
        (arithmetic_evaluation(Expression, Result), Var = term('=', [Variable, Result])),
        Error,
        (Error = '/'(_,_) ->
            (type_error(evaluable, Error, is/2, Exception), throw(Exception)) ;
            (evaluation_error(Error, is/2, Exception), throw(Exception))
        )
    ).


% TYPE TESTING

% atom/1
% atom(@term)
eval_builtin_predicate(atom/1, state(_, Subs), selected(ExprVar, top, Atom), state(ExprVar, Subs)) :-
    Atom = term(atom, [term(_, [])]).

% compound/1
% compound(@term)
eval_builtin_predicate(compound/1, state(_, Subs), selected(ExprVar, top, Atom), state(ExprVar, Subs)) :-
    Atom = term(compound, [term(_, [_|_])]).

% var/1
% var(@term)
eval_builtin_predicate(var/1, state(_, Subs), selected(ExprVar, top, Atom), state(ExprVar, Subs)) :-
    Atom = term(var, [var(_)]).

% nonvar/1
% nonvar(@term)
eval_builtin_predicate(nonvar/1, state(_, Subs), selected(ExprVar, top, Atom), state(ExprVar, Subs)) :-
    Atom = term(nonvar, [X]),
    X \= var(_).

% number/1
% number(@term)
eval_builtin_predicate(number/1, state(_, Subs), selected(ExprVar, top, Atom), state(ExprVar, Subs)) :-
    Atom = term(number, [num(_)]).

% float/1
% float(@term)
eval_builtin_predicate(float/1, state(_, Subs), selected(ExprVar, top, Atom), state(ExprVar, Subs)) :-
    Atom = term(float, [num(X)]),
    float(X).

% integer/1
% integer(@term)
eval_builtin_predicate(integer/1, state(_, Subs), selected(ExprVar, top, Atom), state(ExprVar, Subs)) :-
    Atom = term(integer, [num(X)]),
    integer(X).



% ATOM PROCESSING

% atom_length/2
% atom_length(+Atom, ?Length)
eval_builtin_predicate(atom_length/2, state(_, Subs), selected(ExprVar, Var, Term), state(ExprVar, Subs)) :-
    Term = term(atom_length, [Atom,Length]),
    ( fasill_var(Atom) -> instantiation_error(atom_length/2, Error), throw_exception(Error) ;
        ( \+fasill_atom(Atom) -> type_error(atom, Atom, atom_length/2, Error), throw_exception(Error) ;
            ( \+fasill_var(Length), \+fasill_integer(Length) -> type_error(integer, Length, atom_length/2, Error), throw_exception(Error) ;
                to_prolog(Atom, X), to_prolog(Length, Y),
                atom_length(X,Y),
                from_prolog(X, Fx), from_prolog(Y, Fy),
                Var = term('&', [term('=',[Atom, Fx]), term('=',[Length, Fy])])
            )
        )
    ).

% atom_concat/3
% atom_concat(+First, +Second, -Concat).
eval_builtin_predicate(atom_concat/3, state(_, Subs), selected(ExprVar, Var, Atom), state(ExprVar, Subs)) :-
    Atom = term(atom_concat, [X,Y,Z]),
    X = term(AtomX, []),
    Y = term(AtomY, []),
    atom_concat(AtomX, AtomY, AtomZ),
    Var = term(=, [Z, term(AtomZ, [])]).