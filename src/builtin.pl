/**
  * 
  * FILENAME: builtin.pl
  * DESCRIPTION: This module contains the definition of the FASILL built-in predicates.
  * AUTHORS: José Antonio Riaza Valverde
  * UPDATED: 04.02.2020
  * 
  **/



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
        % consult files
        consult/1,
        consult_sim/1,
        % control constructs
        ','/2,
        ';'/2,
        %'!'/0,
        call/_,
        throw/1,
        catch/3,
        top/0,
        bot/0,
        truth_degree/2,
        % all solutions
        findall/3,
        findall/4,
        % term unification
        '='/2,
        '~'/2,
        '\\='/2,
        '\\~'/2,
        unify_with_occurs_check/2,
        weakly_unify_with_occurs_check/2,
        % term comparison
        '=='/2,
        '@<'/2,
        '@>'/2,
        '@=<'/2,
        '@>='/2,
        '\\=='/2,
        % term creation and decomposition
        '=..'/2,
        % arithmetic comparison
        '<'/2,
        '=:='/2,
        '=<'/2,
        '=\\='/2,
        '>'/2,
        '>='/2,
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
        ground/1,
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



%% CONSULT FILES

%%% consult/1
%%% consult( +atom )
%%%
%%% consult(Path) is true if the file Path exists and is loaded
%%% into the environment.
eval_builtin_predicate(consult/1, state(_, Subs), selected(ExprVar, top, Term), state(ExprVar, Subs)) :-
    Term = term(consult, [term(Path, [])]),
    program_consult(Path).

%%% consult_sim/1
%%% consult_sim( +atom )
%%%
%%% consult_sim(Path) is true if the file Path exists and is loaded
%%% into the environment.
eval_builtin_predicate(consult_sim/1, state(_, Subs), selected(ExprVar, top, Term), state(ExprVar, Subs)) :-
    Term = term(consult_sim, [term(Path, [])]),
    similarity_consult(Path).



%% CONTROL CONSTRUCTS

%%% ,/2
%%% ','( +callable_term, +callable_term )
%%%
%%% Conjunction.
%%% ','(First, Second) is true if and only if First is true and Second is true.
eval_builtin_predicate(','/2, state(_, Subs), selected(ExprVar, Var, Term), state(ExprVar, Subs)) :-
    Term = term(',', [X,Y]),
    Var = term('&', [X,Y]).

%%% ;/2
%%% ';'( +callable_term, +callable_term )
%%%
%%% Disjunction.
%%% ';'(Either, Or) is true if and only if either Either or Or is true.
eval_builtin_predicate(';'/2, state(_, Subs), selected(ExprVar, Var, Term), state(ExprVar, Subs)) :-
    Term = term(';', [X,Y]),
    (Var = X ; Var = Y).

%%% !/0
%%% !
%%%
%%% Cut.
%%% ! is true. All choice points between the cut and the parent goal are removed.
%%% The effect is commit to use of both the current clause and the substitutions
%%% found at the point of the cut.
eval_builtin_predicate('!'/0, state(_, Subs), selected(ExprVar, top, term('!',[])), state(ExprVar, Subs)).

%%% call/[1..]
%%% call( +callable_term [, @term, ...] )
%%%
%%% Invoke a callable term as a goal.
%%% call(Goal, Arg1, ..., ArgN) is true if and only if Goal represents a goal which is true
%%% for the (optional) arguments Arg1, ..., ArgN. 
eval_builtin_predicate('call'/Arity, state(_, Subs), selected(ExprVar, Var, Atom), state(ExprVar, Subs)) :-
    Atom = term('call', [Term|Args]),
    \+lattice_call_member(Term), !,
    ( fasill_var(Term) -> instantiation_error(call/Arity, Error), throw_exception(Error) ; 
        ( \+fasill_callable(Term) -> type_error(callable, Term, call/Arity, Error), throw_exception(Error) ;
            Term = term(Name, Args2),
            append(Args2, Args, Args3),
            Var = term(Name, Args3)
        )
    ).
eval_builtin_predicate('call'/Arity, state(_, Subs), selected(ExprVar, Var, Atom), state(ExprVar, Subs)) :-
    Atom = term('call', [Term|Args]),
    lattice_call_member(Term), !,
    ( fasill_var(Term) -> instantiation_error(call/Arity, Error), throw_exception(Error) ; 
        ( Args \= [] -> type_error(callable, Term, call/Arity, Error), throw_exception(Error) ;
            Var = Term
        )
    ).

%%% throw/1
%%% throw( +term )
%%%
%%% Raise an exception.
%%% throw(Exception) raise the Exception exception. The system looks for
%%% the innermost catch/3 ancestor for which Exception unifies with the
%%% Catcher argument of the catch/3 call.
eval_builtin_predicate(throw/1, _, selected(_, _, Term), _) :-
    Term = term(throw, [Exception]),
    (fasill_var(Exception) -> instantiation_error(throw/1, Error), throw_exception(Error) ;
        throw_exception(Exception)).

%%% catch/3
%%% catch( +callable_term, ?term, +callable_term )
%%%
%%% Enable recovery from exceptions.
%%% catch(Goal, Catcher, Handler) behaves as call/1 if no exception is
%%% raised when executing Goal. If an exception is raised using throw/1
%%% while Goal executes, and the Goal is the innermost goal for which
%%% Catcher unifies with the argument of throw/1, all choice points
%%% generated by Goal are cut, the system backtracks to the start of
%%% catch/3 while preserving the thrown exception term, and Handler is
%%% called as in call/1.
eval_builtin_predicate(catch/3, state(_, Subs), selected(ExprVar, Goal_, Term), state(ExprVar, Subs_)) :-
    Term = term(catch, [Goal, Catcher, Handler]),
    (trace_level(Level) -> Level_ is Level+1, retractall(trace_level(_)), assertz(trace_level(Level_)) ; true),
    (current_fasill_flag(trace, term(true,[])) -> assertz(trace_derivation(trace(Level_, catch/3, state(Goal,Subs)))) ; true),
    derivation(catch/3, state(Goal,Subs), State, _),
    ( State = state(Goal_,Subs_) -> true ; (
        State = exception(Exception), !,
        lattice_call_bot(Bot),
        ((unify(Catcher, Exception, state(TD, _)), TD \= Bot) ->
            Goal_ = term('&',[term('~',[Catcher,Exception]),Handler]), Subs_ = Subs ;
            throw_exception(Exception))
    )).

%%% top/0
%%% top
%%%
%%% True.
%%% top is always true with the maximum truth degree of the lattice.
eval_builtin_predicate(top/0, state(_, Subs), selected(ExprVar, top, _), state(ExprVar, Subs)).

%%% bot/0
%%% bot
%%%
%%% Fail.
%%% bot is always true with the minimum truth degree of the lattice.
eval_builtin_predicate(bot/0, state(_, Subs), selected(ExprVar, bot, _), state(ExprVar, Subs)).

%%% truth_degree/2
%%% truth_degree( +callable_tem, ?term )
%%%
%%% Truth degree.
%%% truth_degree(Goal, TD) is true if TD is the truth degree for the 
%%% goal Goal.
eval_builtin_predicate(truth_degree/2, state(_, Subs), selected(ExprVar, Var, Term), state(ExprVar, Subs_)) :-
    Term = term(truth_degree, [Goal,TD]),
    (trace_level(Level) -> Level_ is Level+1, retractall(trace_level(_)), assertz(trace_level(Level_)) ; true),
    (current_fasill_flag(trace, term(true,[])) -> assertz(trace_derivation(trace(Level_, truth_degree/2, state(Goal,Subs)))) ; true),
    derivation(truth_degree/2, state(Goal,Subs), State, _),
    (State = state(TD_,Subs_) -> Var = term('~',[TD,TD_]) ; State = exception(Error), throw_exception(Error)).



%% ALL SOLUTIONS

%%% findall/3
%%% findall( ?term, +callable_term, ?list )
%%%
%%% Find all the values that would make a goal succeed.
%%% findall(Template, Goal, Instances) is true if and only if Instances
%%% is a list of values in the form Templates that would make the goal
%%% Goal succeed. Usually, Template and Goal share some variables, so
%%% Instances is filled with the values that make Goal succeed. If there is
%%% not a single value that make Goal unify, Instances will be an empty list.
eval_builtin_predicate(findall/3, state(_, Subs), selected(ExprVar, Var, Term), state(ExprVar, Subs)) :-
    Term = term(findall, Args),
    Var = term(findall, [term('&',[])|Args]).

%%% findall/4
%%% findall( +term, ?term, +callable_term, ?list )
%%%
%%% Find all the values that would make a goal succeed.
%%% findall(Connective, Template, Goal, Instances) is true if and only if
%%% Instances is a list of values in the form Templates that would make the 
%%% goal Goal succeed. Usually, Template and Goal share some variables, so
%%% Instances is filled with the values that make Goal succeed. If there is
%%% not a single value that make Goal unify, Instances will be an empty list.
eval_builtin_predicate(findall/4, state(_, Subs), selected(ExprVar, Var, Term), state(ExprVar, Subs)) :-
    Term = term(findall, [Op, Template, Goal, Instances]),
    ( fasill_var(Goal) -> instantiation_error(findall/4, Error), throw_exception(Error) ;
        ( \+fasill_callable(Goal) -> type_error(callable, Goal, findall/4, Error), throw_exception(Error) ;
            (\+fasill_var(Instances), \+fasill_list(Instances) -> type_error(list, Instances, findall/4, Error), throw_exception(Error) ;
                lattice_call_bot(Bot),
                get_variables(Goal, GoalVars),
                (trace_level(Level) -> Level_ is Level+1, retractall(trace_level(_)), assertz(trace_level(Level_)) ; true),
                (current_fasill_flag(trace, term(true,[])) -> assertz(trace_derivation(trace(Level_, findall/4, state(Goal,GoalVars)))) ; true),
                findall([TD,Template_], (
                    derivation(findall/4, state(Goal,GoalVars), State, _),
                    (State = state(TD,Subs_) -> TD \= Bot, apply(Template, Subs_, Template_) ;
                        State = exception(Error), throw_exception(Error)
                    )
                ), List),
                maplist(nth0(0), List, TDs),
                maplist(nth0(1), List, Bodies),
                from_prolog_list(Bodies, Result),
                to_prolog(Op, Op_),
                lattice_reduce_connective(Op_, TDs, TD),
                Var = term(Op_, [TD, term('~',[Instances, Result])])
            )
        )
    ).



%% TERM UNIFICATION

%%% '~'/2
%%% '~'(@term, @term)
%%%
%%% Weak unification.
%%% X ~ Y is true if and only if X and Y are weakly unifiable.
%%% True if the weak unification succeeds.
eval_builtin_predicate('~'/2, state(_, Subs), selected(ExprVar, TD, Term), state(ExprSubs, Subs_)) :-
    Term = term('~', [X,Y]),
    unify(X, Y, _, state(TD, SubsUnification)),
    apply(SubsUnification, ExprVar, ExprSubs),
    compose(Subs, SubsUnification, Subs_).

%%% '='/2
%%% '='(@term, @term)
%%%
%%% Unification.
%%% X = Y is true if and only if X and Y are unifiable.
%%% True if the unification succeeds.
eval_builtin_predicate('='/2, state(_, Subs), selected(ExprVar, top, Term), state(ExprSubs, Subs_)) :-
    Term = term('=', [X,Y]),
    current_fasill_flag(occurs_check, term(OccursCheck, [])),
    mgu(X, Y, OccursCheck, SubsUnification),
    apply(SubsUnification, ExprVar, ExprSubs),
    compose(Subs, SubsUnification, Subs_).

%%% '\~'/2
%%% '\~'(@term, @term)
%%%
%%% Not weak unification.
%%% X \~ Y is true if and only if X and Y are not weakly unifiable.
eval_builtin_predicate('\\~'/2, state(_, Subs), selected(ExprVar, top, Term), state(ExprVar, Subs)) :-
    Term = term('\\~', [X,Y]),
    lattice_call_bot(Bot),
    (unify(X, Y, _, state(TD,_)) -> TD == Bot ; true).

%%% '\='/2
%%% '\='(@term, @term)
%%%
%%% Not unification.
%%% X \= Y is true if and only if X and Y are not unifiable.
eval_builtin_predicate('\\='/2, state(_, Subs), selected(ExprVar, top, Term), state(ExprVar, Subs)) :-
    Term = term('\\=', [X,Y]),
    current_fasill_flag(occurs_check, term(OccursCheck, [])),
    \+mgu(X, Y, OccursCheck, _).

%%% weakly_unify_with_occurs_check/2
%%% weakly_unify_with_occurs_check(@term, @term)
%%%
%%% Weak unification with occurs check.
%%% weakly_unify_with_occurs_check(X, Y) is true if and only if X and Y are weakly unifiable.
%%% True if the weak unification succeeds.
eval_builtin_predicate(weakly_unify_with_occurs_check/2, state(_, Subs), selected(ExprVar, TD, Term), state(ExprSubs, Subs_)) :-
    Term = term(weakly_unify_with_occurs_check, [X,Y]),
    unify(X, Y, true, state(TD, SubsUnification)),
    apply(SubsUnification, ExprVar, ExprSubs),
    compose(Subs, SubsUnification, Subs_).

%%% unify_with_occurs_check/2
%%% unify_with_occurs_check(@term, @term)
%%%
%%% Unification with occurs check.
%%% unify_with_occurs_check(X, Y) is true if and only if X and Y are unifiable.
%%% True if the unification succeeds.
eval_builtin_predicate(unify_with_occurs_check/2, state(_, Subs), selected(ExprVar, top, Term), state(ExprSubs, Subs_)) :-
    Term = term(unify_with_occurs_check, [X,Y]),
    mgu(X, Y, true, SubsUnification),
    apply(SubsUnification, ExprVar, ExprSubs),
    compose(Subs, SubsUnification, Subs_).



%% TERM COMPARISON

%%% '=='/2
%%% '=='(@term, @term)
%%%
%%% Term identical.
%%% True if the compared terms are identical.
eval_builtin_predicate('=='/2, state(_, Subs), selected(ExprVar, top, Term), state(ExprVar, Subs)) :-
    Term = term('==', [X,Y]),
    (( X = var(X_), Y = var(Y_)) -> X_ == Y_ ;
        ( to_prolog(X, X_), to_prolog(Y, Y_), X_ == Y_ )
    ).

%%% '\=='/2
%%% '\=='(@term, @term)
%%%
%%% Term not identical.
%%% True if the compared terms are not identical.
eval_builtin_predicate('\\=='/2, state(_, Subs), selected(ExprVar, top, Term), state(ExprVar, Subs)) :-
    Term = term('\\==', [X,Y]),
    (( X = var(X_), Y = var(Y_)) -> X_ \== Y_ ;
        ( to_prolog(X, X_), to_prolog(Y, Y_), X_ \== Y_ )
    ).

%%% '@<'/2
%%% '@<'(@term, @term)
%%%
%%% Term less than.
%%% True if the first term is less than the second one.
eval_builtin_predicate('@<'/2, state(_, Subs), selected(ExprVar, top, Term), state(ExprVar, Subs)) :-
    Term = term('@<', [X,Y]),
    (( X = var(X_), Y = var(Y_)) -> X_ @< Y_ ;
        ( to_prolog(X, X_), to_prolog(Y, Y_), X_ @< Y_ )
    ).

%%% '@>'/2
%%% '@>'(@term, @term)
%%%
%%% Term greater than.
%%% True if the first term is greater than the second one.
eval_builtin_predicate('@>'/2, state(_, Subs), selected(ExprVar, top, Term), state(ExprVar, Subs)) :-
    Term = term('@>', [X,Y]),
    (( X = var(X_), Y = var(Y_)) -> X_ @> Y_ ;
        ( to_prolog(X, X_), to_prolog(Y, Y_), X_ @> Y_ )
    ).

%%% '@=<'/2
%%% '@=<'(@term, @term)
%%%
%%% Term less than or equal to.
%%% True if the first term is less than or equal to the second one.
eval_builtin_predicate('@=<'/2, state(_, Subs), selected(ExprVar, top, Term), state(ExprVar, Subs)) :-
    Term = term('@=<', [X,Y]),
    (( X = var(X_), Y = var(Y_)) -> X_ @=< Y_ ;
        ( to_prolog(X, X_), to_prolog(Y, Y_), X_ @=< Y_ )
    ).

%%% '@>='/2
%%% '@>='(@term, @term)
%%%
%%% Term greater than or equal to.
%%% True if the first term is greater than or equal to the second one.
eval_builtin_predicate('@>='/2, state(_, Subs), selected(ExprVar, top, Term), state(ExprVar, Subs)) :-
    Term = term('@>=', [X,Y]),
    (( X = var(X_), Y = var(Y_)) -> X_ @>= Y_ ;
        ( to_prolog(X, X_), to_prolog(Y, Y_), X_ @>= Y_ )
    ).



%% TERM CREATION AND DECOMPOSITION

%%% '=..'/2
%%% Check the descomposition of a term.
%%%
%%% Term =.. List is true if and only if (1) Term is an atomic term
%%% and List is a list consisted of just one element, Term, or (2)
%%% Term is a compound term and List is a list which has the functor
%%% name of Term as head and the arguments of that functor as tail.
eval_builtin_predicate('=..'/2, state(_, Subs), selected(ExprVar, Expr, Atom), state(ExprVar, Subs)) :-
    Atom = term('=..', [Term, List]),
    (fasill_var(Term), fasill_var(List) -> instantiation_error('=..'/2, Error), throw_exception(Error) ; (
        (\+fasill_list(List) -> type_error(list, List, '=..'/2, Error), throw_exception(Error) ; (
            (\+fasill_var(List), \+fasill_list(List) -> type_error(list, List, '=..'/2, Error), throw_exception(Error) ; (
                (\+fasill_var(Term), \+fasill_term(Term) -> type_error(atom, Term, '=..'/2, Error), throw_exception(Error) ; (
                    (\+fasill_var(Term) -> Term = term(Name,Args), from_prolog_list(Args,Args_), List_ = term('.',[term(Name,[]),Args_]), Expr = term('~',[List,List_]) ; (
                        (List = term('[]',[]) -> Term_ = List ; List = term('.',[term(Name,[]), Args]), to_prolog_list(Args,Args_), Term_ = term(Name, Args_), Expr = term('~',[Term,Term_]))
                    ))
                ))
            ))
        ))
    )).



%% ARITHMETIC COMPARISON

%%% '<'/2
%%% '<'(@evaluable, @evaluable)
%%%
%%% Arithmetic less than.
%%% True if the first number is less than the second one.
eval_builtin_predicate('<'/2, state(_, Subs), selected(ExprVar, top, Atom), state(ExprVar, Subs)) :-
    Atom = term('<', [Left, Right]),
    arithmetic_comparison('<'/2, Left, Right).

%%% '>'/2
%%% '>'(@evaluable, @evaluable)
%%%
%%% Arithmetic greater than.
%%% True if the first number is greater than the second one.
eval_builtin_predicate('>'/2, state(_, Subs), selected(ExprVar, top, Atom), state(ExprVar, Subs)) :-
    Atom = term('>', [Left, Right]),
    arithmetic_comparison('>'/2, Left, Right).

%%% '=:='/2
%%% '=:='(@evaluable, @evaluable)
%%%
%%% Arithmetic equal.
%%% True if both numbers are equal.
eval_builtin_predicate('=:='/2, state(_, Subs), selected(ExprVar, top, Atom), state(ExprVar, Subs)) :-
    Atom = term('=:=', [Left, Right]),
    arithmetic_comparison('=:='/2, Left, Right).

%%% '=\\='/2
%%% '=\\='(@evaluable, @evaluable)
%%%
%%% Arithmetic not equal.
%%% True if the compared numbers are not equal.
eval_builtin_predicate('=\\='/2, state(_, Subs), selected(ExprVar, top, Atom), state(ExprVar, Subs)) :-
    Atom = term('=\\=', [Left, Right]),
    arithmetic_comparison('=\\='/2, Left, Right).

%%% '=<'/2
%%% '=<'(@evaluable, @evaluable)
%%%
%%% Arithmetic less than or equal to.
%%% True if the first number is less than or equal to the second one.
eval_builtin_predicate('=<'/2, state(_, Subs), selected(ExprVar, top, Atom), state(ExprVar, Subs)) :-
    Atom = term('=<', [Left, Right]),
    arithmetic_comparison('=<'/2, Left, Right).

%%% '>='/2
%%% '>='(@evaluable, @evaluable)
%%%
%%% Arithmetic greater than or equal to.
%%% True if the first number is greater than or equal to the second one.
eval_builtin_predicate('>='/2, state(_, Subs), selected(ExprVar, top, Atom), state(ExprVar, Subs)) :-
    Atom = term('>=', [Left, Right]),
    arithmetic_comparison('>='/2, Left, Right).



%% ARITHMETIC EVALUATION

%%% is/2
%%% 'is'(?term, @evaluable)
%%%
%%% Evaluate expression.
%%% Result is Expression is true if and only if evaluating
%%% Expression as an expression gives Result as a result.
eval_builtin_predicate(is/2, state(_, Subs), selected(ExprVar, Var, Atom), state(ExprVar, Subs)) :-
    Atom = term(is, [Variable, Expression]),
    arithmetic_evaluation('is'/2, Expression, Result),
    Var = term('~', [Variable, Result]).



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

%%% ground/1
%%% ground(@term)
%%%
%%% Check if ground term.
%%% ground(X) is true if and only if X is a ground term.
eval_builtin_predicate(ground/1, state(_, Subs), selected(ExprVar, top, Atom), state(ExprVar, Subs)) :-
    Atom = term(ground, [X]), fasill_ground(X).



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
                Var = term('&', [term('~',[Atom, Fx]), term('~',[Length, Fy])])
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
                        Var = term('&', [term('~',[Start,Fx]), term('&',[term('~',[End,Fy]),term('~',[Whole,Fz])])])
                    )
                )
            )
        )
    ).