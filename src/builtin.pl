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
        % control constructs
        ','/2,
        ';'/2,
        % term unification
        '='/2,
        '\\='/2,
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



%% CONTROL CONSTRUCTS

%%% ,/2
%%% ','(X,Y)
%%%
%%% Conjunction.
%%% ','(First, Second) is true if and only if First is true and Second is true.
eval_builtin_predicate(','/2, state(_, Subs), selected(ExprVar, Var, Term), state(ExprVar, Subs)) :-
    Term = term(',', [X,Y]),
    Var = term('&', [X,Y]).

%%% ;/2
%%% ';'(X,Y)
%%%
%%% Disjunction.
%%% ';'(Either, Or) is true if and only if either Either or Or is true.
eval_builtin_predicate(';'/2, state(_, Subs), selected(ExprVar, Var, Term), state(ExprVar, Subs)) :-
    Term = term(';', [X,Y]),
    (Var = X ; Var = Y).



%% TERM UNIFICATION

%%% '='/2
%%% '='(@term, @term)
%%%
%%% Weak unification.
%%% X = Y is true if and only if X and Y are unifiable.
%%% True if the unification succeeds.
eval_builtin_predicate('='/2, state(_, Subs), selected(ExprVar, TD, Term), state(ExprSubs, Subs_)) :-
    Term = term('=', [X,Y]),
    wmgu(X, Y, state(TD, SubsUnification)),
    apply(ExprVar, SubsUnification, ExprSubs),
    compose(Subs, SubsUnification, Subs_).

%%% '\='/2
%%% '\='(@term, @term)
%%%
%%% Not unification.
%%% X \= Y is true if and only if X and Y are not unifiable.
eval_builtin_predicate('\\='/2, state(_, Subs), selected(ExprVar, top, Term), state(ExprVar, Subs)) :-
    Term = term('\\=', [X,Y]),
    lattice_call_bot(Bot),
    (wmgu(X, Y, state(TD,_)) -> TD == Bot ; true).



%% ARITHMETIC EVALUATION

%%% is/2
%%% 'is'(?term, @evaluable)
%%%
%%% Evaluate expression.
%%% Result is Expression is true if and only if evaluating
%%% Expression as an expression gives Result as a result.
eval_builtin_predicate(is/2, state(_, Subs), selected(ExprVar, Var, Atom), state(ExprVar, Subs)) :-
    Atom = term(is, [Variable, Expression]),
    catch(
        (arithmetic_evaluation(Expression, Result), Var = term('=', [Variable, Result])),
        Error,
        (Error = type(Type, From) ->
            (from_prolog(From, From_), type_error(Type, From_, is/2, Exception), throw(Exception)) ;
            (Error = evaluation(Cause) ->
                (evaluation_error(Cause, is/2, Exception), throw(Exception)) ;
                (instantiation_error(is/2, Exception), throw(Exception))
            )
        )
    ).


%% TYPE TESTING

%%% atom/1
%%% atom(@term)
%%%
%%% Check if atom.
%%% atom(X) is true if and only if X is an atom.
eval_builtin_predicate(atom/1, state(_, Subs), selected(ExprVar, top, Atom), state(ExprVar, Subs)) :-
    Atom = term(atom, [term(_, [])]).

%%% compound/1
%%% compound(@term)
%%%
%%% Check if compound.
%%% compound(X) is true if and only if X is a compound
%%% term (neither atomic nor a variable).
eval_builtin_predicate(compound/1, state(_, Subs), selected(ExprVar, top, Atom), state(ExprVar, Subs)) :-
    Atom = term(compound, [term(_, [_|_])]).

%%% var/1
%%% var(@term)
%%%
%%% Check if variable.
%%% var(X) is true if and only if X is a variable.
eval_builtin_predicate(var/1, state(_, Subs), selected(ExprVar, top, Atom), state(ExprVar, Subs)) :-
    Atom = term(var, [var(_)]).

%%% nonvar/1
%%% nonvar(@term)
%%%
%%% Check if not variable.
%%% nonvar(X) is true if and only if X is not a variable.
eval_builtin_predicate(nonvar/1, state(_, Subs), selected(ExprVar, top, Atom), state(ExprVar, Subs)) :-
    Atom = term(nonvar, [X]),
    X \= var(_).

%%% number/1
%%% number(@term)
%%%
%%% Check if integer or float.
%%% number(X) is true if and only if X is either an integer or a float.
eval_builtin_predicate(number/1, state(_, Subs), selected(ExprVar, top, Atom), state(ExprVar, Subs)) :-
    Atom = term(number, [num(_)]).

%%% float/1
%%% float(@term)
%%%
%%% Check if float.
%%% float(X) is true if and only if X is a float.
eval_builtin_predicate(float/1, state(_, Subs), selected(ExprVar, top, Atom), state(ExprVar, Subs)) :-
    Atom = term(float, [num(X)]),
    float(X).

%%% integer/1
%%% integer(@term)
%%%
%%% Check if integer.
%%% integer(X) is true if and only if X is an integer.
eval_builtin_predicate(integer/1, state(_, Subs), selected(ExprVar, top, Atom), state(ExprVar, Subs)) :-
    Atom = term(integer, [num(X)]),
    integer(X).



%% ATOM PROCESSING

%%% atom_length/2
%%% atom_length( +atom, ?integer )
%%%
%%% Length of an atom.
%%% atom_length(Atom, Length) is true if and only if the number
%%% of characters in the name of Atom is equal to Length. If
%%% Length is not instantiated, atom_length will calculate the
%%% length of Atom's name.
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

%%% atom_concat/3
%%% atom_concat( ?atom, ?atom +atom )
%%% atom_concat( +atom, +atom, -atom )
%%%
%%% Concatenate characters.
%%% atom_concat(Start, End, Whole) is true if and only if Whole
%%% is the atom obtained by adding the characters of End at the
%%% end of Start. If Whole is the only argument instantiated,
%%% atom_concat/3 will obtain all possible decompositions of it.
eval_builtin_predicate(atom_concat/3, state(_, Subs), selected(ExprVar, Var, Atom), state(ExprVar, Subs)) :-
    Atom = term(atom_concat, [Start,End,Whole]),
    ( fasill_var(Whole), fasill_var(Start) -> instantiation_error(atom_concat/3, Error), throw_exception(Error) ;
        ( fasill_var(Whole), fasill_var(End) -> instantiation_error(atom_concat/3, Error), throw_exception(Error) ;
            ( \+fasill_var(Start), \+fasill_atom(Start) -> type_error(atom, Start, atom_concat/3, Error), throw_exception(Error) ;
                ( \+fasill_var(End), \+fasill_atom(End) -> type_error(atom, End, atom_concat/3, Error), throw_exception(Error) ;
                    ( \+fasill_var(Whole), \+fasill_atom(Whole) -> type_error(atom, Whole, atom_concat/3, Error), throw_exception(Error) ;
                        to_prolog(Start, X), to_prolog(End, Y), to_prolog(Whole, Z),
                        atom_concat(X,Y,Z),
                        from_prolog(X, Fx), from_prolog(Y, Fy), from_prolog(Z, Fz),
                        Var = term('&', [term('=',[Start,Fx]), term('&',[term('=',[End,Fy]),term('=',[Whole,Fz])])])
                    )
                )
            )
        )
    ).