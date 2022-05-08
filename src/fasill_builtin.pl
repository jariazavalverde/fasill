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

:- module(fasill_builtin, [
    is_builtin_predicate/1,
    eval_builtin_predicate/4
]).

:- use_module(fasill_arithmetic).
:- use_module(fasill_substitution).
:- use_module(fasill_unification).
:- use_module(fasill_environment).
:- use_module(fasill_exceptions).
:- use_module(fasill_inference).
:- use_module(fasill_term).

/** <module> Built-in predicates
    This library provides predicates for running built-in predicates.

    FASILL has a large set of built-in predicates for arithmetic comparison,
    arithmetic evaluation, atom processing, control constructs, term comparison,
    term unification, type testing, list manipulation, etc.
*/

%!  is_builtin_predicate(?Indicator)
%
%   This predicate succeeds when Indicator is the indicator of a builtin
%   predicate of FASILL. An indicator is a term of the form Name/Arity, where
%   Name is an atom and Arity is a non-negative integer.

is_builtin_predicate(Name/Arity) :-
    member(Name/Arity, [
        % consult files
        consult/1,
        consult_sim/1,
        % transformations
        unfold/1,
        % control constructs
        ','/2,
        ';'/2,
        '->'/2,
        call/_,
        once/1,
        throw/1,
        catch/3,
        top/0,
        bot/0,
        truth_degree/2,
        on/2,
        '+'/1,
        guards/1,
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

%!  eval_builtin_predicate(+Indicator, +State1, +Atom, ?State2)
%
%   This predicate succeeds when Indicator is the indicator of a builtin
%   predicate of FASILL, and State2 is the resulting state of performing a
%   step over the state State1 with selected atom Atom whose indicator is 
%   Indicator.

:- discontiguous eval_builtin_predicate/4.

/** <builtin> Loading FASILL source files
    This section deals with loading FASILL source files. A FASILL source file
    is a plain text file containing a FASILL program or similarity scheme.
*/

%!  consult(+atom)
%
%   Load program rules.
%   consult(Path) is true if the file Path exists and is loaded into the
%   environment.

eval_builtin_predicate(consult/1, state(_, Subs), selected(ExprVar, top, Term), state(ExprVar, Subs)) :-
    Term = term(consult, [term(Path, [])]),
    fasill_environment:program_consult(Path).

%!  consult_sim(+atom)
%
%   Load similarities.
%   consult_sim(Path) is true if the file Path exists and is loaded into the
%   environment.

eval_builtin_predicate(consult_sim/1, state(_, Subs), selected(ExprVar, top, Term), state(ExprVar, Subs)) :-
    Term = term(consult_sim, [term(Path, [])]),
    fasill_environment:similarity_consult(Path).

/** <builtin> Program transformations
    This section deals with automatic program transformations such as unfolding
    and tuning techniques.
*/

%!  unfold(+rule_id)
%
%   Unfolding transformation.
%   unfold(Id) unfolds the rule with identifier Id.

eval_builtin_predicate(unfold/1, state(_, Subs), selected(ExprVar, top, Term), state(ExprVar, Subs)) :-
    Term = term(_, [Id]),
    (fasill_term:fasill_var(Id) ->
        fasill_exceptions:instantiation_error(unfold/1, Error),
        fasill_exceptions:throw_exception(Error) ;
        true),
    (\+fasill_term:fasill_atom(Id) ->
        fasill_exceptions:type_error(atom, Id, unfold/1, Error),
        fasill_exceptions:throw_exception(Error) ;
        true),
    Id = term(Rule, []),
    (fasill_environment:fasill_rule(_, _, Info), member(id(Rule), Info) ->
        fasill_unfolding:unfold_by_id(Rule) ;
        fasill_exceptions:existence_error(rule, Rule, unfold/1, Error),
        fasill_exceptions:throw_exception(Error)).

/** <builtin> Control constructs
    The predicates of this section implement control structures.
*/

%!  ','(+callable_term, +callable_term)
%
%   Conjunction.
%   ','(First, Second) is true if and only if First is true and Second is true.

eval_builtin_predicate(','/2, state(_, Subs), selected(ExprVar, Var, Term), state(ExprVar, Subs)) :-
    Term = term(',', [X,Y]),
    Var = term('&', [X,Y]).

%!  ';'(+callable_term, +callable_term)
%
%   Disjunction.
%   ';'(Either, Or) is true if and only if either Either or Or is true.

eval_builtin_predicate(';'/2, state(_, Subs), selected(ExprVar, Var, Term), state(ExprVar, Subs)) :-
    Term = term(';', [X,Y]),
    (Var = X ; Var = Y).

%!  '->'(+callable_term, +callable_term)
%
%   If-Then.
%   '->'(If, Then) is true if and only if If is true and Then is true for the
%   first solution of If.

eval_builtin_predicate('->'/2, state(_, S0), selected(ExprVar, Var, Term), state(ExprVar, S0)) :-
    Term = term('->', [If,Then]),
    ((fasill_term:fasill_var(If) ; fasill_term:fasill_var(Then)) ->
        fasill_exceptions:instantiation_error(call/Arity, Error),
        fasill_exceptions:throw_exception(Error) ;
        true),
    (\+fasill_term:fasill_callable(If) ->
        fasill_exceptions:type_error(callable, If, call/Arity, Error),
        fasill_exceptions:throw_exception(Error) ;
        true),
    (\+fasill_term:fasill_callable(Then) ->
        fasill_exceptions:type_error(callable, Then, call/Arity, Error),
        fasill_exceptions:throw_exception(Error) ;
        true),
    fasill_environment:lattice_call_bot(Bot),
    ExprVar = term('&', [
        term('+', [term(once, [If])]),
        term(call, [Then])
    ]).

%!  call(+callable_term [, @term, ...])
%
%   Invoke a callable term as a goal.
%   call(Goal, Arg1, ..., ArgN) is true if and only if Goal represents a goal
%   which is true for the (optional) arguments Arg1, ..., ArgN.

eval_builtin_predicate(call/Arity, state(_, Subs), selected(ExprVar, Var, Atom), state(ExprVar, Subs)) :-
    Atom = term(call, [Term|Args]),
    \+fasill_environment:lattice_call_member(Term),
    !,
    (fasill_term:fasill_var(Term) ->
        fasill_exceptions:instantiation_error(call/Arity, Error),
        fasill_exceptions:throw_exception(Error) ;
        true),
    (\+fasill_term:fasill_callable(Term) ->
        fasill_exceptions:type_error(callable, Term, call/Arity, Error),
        fasill_exceptions:throw_exception(Error) ;
        true),
    Term = term(Name, Args2),
    append(Args2, Args, Args3),
    Var = term(Name, Args3).

eval_builtin_predicate(call/Arity, state(_, Subs), selected(ExprVar, Var, Atom), state(ExprVar, Subs)) :-
    Atom = term(call, [Term|Args]),
    fasill_environment:lattice_call_member(Term),
    !,
    (fasill_term:fasill_var(Term) ->
        fasill_exceptions:instantiation_error(call/Arity, Error),
        fasill_exceptions:throw_exception(Error) ;
        true),
    (Args \= [] ->
        fasill_exceptions:type_error(callable, Term, call/Arity, Error),
        fasill_exceptions:throw_exception(Error) ;
        true),
    Var = Term.

%!  once(+callable_term)
%
%   Evaluate a term just once.
%   once(Term) is true. once makes sure that Term fails or succeeds just once.

eval_builtin_predicate(once/1, state(Goal, S0), selected(ExprVar, Var, Atom), state(ExprSub, S1)) :-
    Atom = term(once, [Term]),
    (fasill_term:fasill_var(Term) ->
        fasill_exceptions:instantiation_error(once/1, Error),
        fasill_exceptions:throw_exception(Error) ;
        true),
    (\+fasill_term:fasill_callable(Term) ->
        fasill_exceptions:type_error(callable, Term, once/1, Error),
        fasill_exceptions:throw_exception(Error) ;
        true),
    fasill_environment:lattice_call_bot(Bot),
    once((
        fasill_inference:derivation(once/1, state(Term,S0), State, _),
        State = state(TD,S1),
        TD \== Bot ;
        State = exception(_)
    )),
    ( State = state(TD,S1) ->
      Var = TD,
      fasill_substitution:apply(S1, ExprVar, ExprSub)
    ; State = exception(Error),
      fasill_exceptions:throw_exception(Error)
    ).

%!  throw(+term)
%
%   Raise an exception.
%   throw(Exception) raise the Exception exception. The system looks for the
%   innermost catch/3 ancestor for which Exception unifies with the Catcher
%   argument of the catch/3 call.

eval_builtin_predicate(throw/1, _, selected(_, _, Term), _) :-
    Term = term(throw, [Exception]),
    (fasill_term:fasill_var(Exception) ->
        fasill_exceptions:instantiation_error(throw/1, Error),
        fasill_exceptions:throw_exception(Error) ;
        true),
    fasill_exceptions:throw_exception(Exception).

%!  catch(+callable_term, ?term, +callable_term)
%
%   Enable recovery from exceptions.
%   catch(Goal, Catcher, Handler) behaves as call/1 if no exception is raised
%   when executing Goal. If an exception is raised using throw/1 while Goal
%   executes, and the Goal is the innermost goal for which Catcher unifies with
%   the argument of throw/1, all choice points generated by Goal are cut, the
%   system backtracks to the start of catch/3 while preserving the thrown
%   exception term, and Handler is called as in call/1.

eval_builtin_predicate(catch/3, state(_,S0), selected(E0,Var,Term), state(E1,S1)) :-
    Term = term(catch, [Goal, Catcher, Handler]),
    ((fasill_term:fasill_var(Goal) ; fasill_term:fasill_var(Handler)) ->
        fasill_exceptions:instantiation_error(catch/3, Error),
        fasill_exceptions:throw_exception(Error) ;
        true),
    (\+fasill_term:fasill_callable(Goal) ->
        fasill_exceptions:type_error(callable, Goal, catch/3, Error),
        fasill_exceptions:throw_exception(Error) ;
        true),
    (\+fasill_term:fasill_callable(Handler) ->
        fasill_exceptions:type_error(callable, Handler, catch/3, Error),
        fasill_exceptions:throw_exception(Error) ;
        true),
    fasill_inference:derivation(catch/3, state(Goal,S0), State, _),
    ( State = state(TD,S1) ->
      Var = TD,
      fasill_substitution:apply(S1, E0, E1)
    ; State = exception(Exception),
      !,
      fasill_environment:lattice_call_bot(Bot),
      ( fasill_unification:unify(Catcher, Exception, _, state(Bot,_)) ->
        fasill_exceptions:throw_exception(Exception)
      ; Var = term('&',[term('~',[Catcher,Exception]),Handler]),
        E1 = E0,
        S1 = S0
      )
    ).

%!  top
%
%   True.
%   top is always true with the maximum truth degree of the lattice.

eval_builtin_predicate(top/0, state(_, Subs), selected(ExprVar, top, _), state(ExprVar, Subs)).

%!  bot
%
%   Fail.
%   bot is always true with the minimum truth degree of the lattice.

eval_builtin_predicate(bot/0, state(_, Subs), selected(ExprVar, bot, _), state(ExprVar, Subs)).

%!  truth_degree(+callable_tem, ?term)
%
%   Truth degree.
%   truth_degree(Goal, TD) is true if TD is the truth degree for the goal Goal.

eval_builtin_predicate(truth_degree/2, state(_, S0), selected(E0, Var, Term), state(E1, S1)) :-
    Term = term(truth_degree, [Goal,TD]),
    (fasill_term:fasill_var(Goal) ->
        fasill_exceptions:instantiation_error(truth_degree/2, Error),
        fasill_exceptions:throw_exception(Error) ;
        true),
    (\+fasill_term:fasill_callable(Goal) ->
        fasill_exceptions:type_error(callable, Goal, truth_degree/2, Error),
        fasill_exceptions:throw_exception(Error) ;
        true),
    fasill_inference:derivation(truth_degree/2, state(Goal,S0), State, _),
    ( State = state(TD_,S1) ->
      Var = term('~',[TD,TD_]),
      fasill_substitution:apply(S1, E0, E1)
    ; State = exception(Error),
      fasill_exceptions:throw_exception(Error)
    ).

%!  on(+callable_tem, ?term)
%
%   Truth degree.
%   Infix form of truth_degree/2.

eval_builtin_predicate(on/2, state(_, S0), selected(E0, Var, Term), state(E1, S1)) :-
    Term = term(on, [Goal,TD]),
    (fasill_term:fasill_var(Goal) ->
        fasill_exceptions:instantiation_error(on/2, Error),
        fasill_exceptions:throw_exception(Error) ;
        true),
    (\+fasill_term:fasill_callable(Goal) ->
        fasill_exceptions:type_error(callable, Goal, on/2, Error),
        fasill_exceptions:throw_exception(Error) ;
        true),
    fasill_inference:derivation(on/2, state(Goal,S0), State, _),
    ( State = state(TD_,S1) ->
      Var = term('~',[TD,TD_]),
      fasill_substitution:apply(S1, E0, E1)
    ; State = exception(Error),
      fasill_exceptions:throw_exception(Error)
    ).

%!  +(+callable_term)
%
%   Goal that must succeed.
%   +(Goal) is true if and only if Goal represents a goal which is true. If
%   goal fails, the derivation fails instead of performing a failure step.

eval_builtin_predicate('+'/1, state(_, S0), selected(E0, Goal_, Atom), state(E1, S1)) :-
    Atom = term('+', [Goal]),
    (fasill_term:fasill_var(Goal) ->
        fasill_exceptions:instantiation_error('+'/1, Error),
        fasill_exceptions:throw_exception(Error) ;
        true),
    (\+fasill_term:fasill_callable(Goal) ->
        fasill_exceptions:type_error(callable, Goal, '+'/1, Error),
        fasill_exceptions:throw_exception(Error) ;
        true),
    fasill_inference:derivation('+'/1, state(Goal,S0), State, _),
    ( State = state(Goal_,S1) ->
      \+fasill_environment:lattice_call_bot(Goal_),
      fasill_substitution:apply(S1, E0, E1)
    ; State = exception(Error),
      !,
      fasill_exceptions:throw_exception(Error)
    ).

%!  guards(on(+Guards, -TD))
%
%   Guards.
%   Guards on control construct.

eval_builtin_predicate(guards/1, state(_, Sub), selected(ExprVar, Body, Atom), state(ExprVar, SubU)) :-
    Atom = term(guards, [term(on, [Guards, TD])]),
    guards_last_id(N),
    retractall(guards_last_id(_)),
    succ(N, M),
    asserta(guards_last_id(M)),
    asserta(guards_count(M, 0)),
    call_guards(M, Guards, TD, Body, Sub, SubS, Unifier),
    fasill_substitution:compose(SubS, Unifier, SubU).

call_guards(N, term(';', [A, B]), TD, Body, Sub, SubS, Unifier) :- !,
    (call_guards(N, A, TD, Body, Sub, SubS, Unifier) ;
     call_guards(N, B, TD, Body, Sub, SubS, Unifier)).
call_guards(N, term('->', [term('~', [G,H]), Body]), var(V), BodyU, Sub, SubS, Unifier) :- !,
    fasill_unification:unify(G, H, _, state(TD, Unifier)),
    guards_count(N, C1),
    succ(C1, C2),
    retractall(guards_count(N, _)),
    asserta(guards_count(N, C2)),
    fasill_substitution:empty_substitution(Empty),
    fasill_substitution:put_substitution(Empty, V, TD, VarSub),
    fasill_substitution:apply(VarSub, Body, BodyS),
    fasill_substitution:apply(Unifier, BodyS, BodyU),
    fasill_substitution:compose(Sub, Unifier, SubS).
call_guards(N, term('->', [term('^', [term('~', [G, H])]), Body]), var(V), BodyU, Sub, SubS, Unifier) :-
    guards_count(N, 0),
    fasill_unification:unify(G, H, _, state(TD, Unifier)),
    fasill_substitution:empty_substitution(Empty),
    fasill_substitution:put_substitution(Empty, V, TD, VarSub),
    fasill_substitution:apply(VarSub, Body, BodyS),
    fasill_substitution:apply(Unifier, BodyS, BodyU),
    fasill_substitution:compose(Sub, Unifier, SubS).
call_guards(N, term('->', [Goal, Body]), var(V), BodyU, Sub, SubS, Unifier) :-
    Goal \= term('^', [_]),
    Goal \= term('~', [_,_]),
    fasill_substitution:init_substitution(Goal, Vars),
    fasill_inference:derivation(guards/1, state(Goal,Vars), state(TD,Unifier), _),
    fasill_environment:lattice_call_bot(Bot),
    TD \= Bot,
    guards_count(N, C1),
    succ(C1, C2),
    retractall(guards_count(N, _)),
    asserta(guards_count(N, C2)),
    fasill_substitution:empty_substitution(Empty),
    fasill_substitution:put_substitution(Empty, V, TD, VarSub),
    fasill_substitution:apply(VarSub, Body, BodyS),
    fasill_substitution:apply(Unifier, BodyS, BodyU),
    fasill_substitution:compose(Sub, Unifier, SubS).
call_guards(N, term('->', [term('^', [Goal]), Body]), var(V), BodyU, Sub, SubS, Unifier) :-
    Goal \= term('~', [_,_]),
    guards_count(N, 0),
    fasill_substitution:init_substitution(Goal, Vars),
    fasill_inference:derivation(guards/1, state(Goal,Vars), state(TD,Unifier), _),
    fasill_environment:lattice_call_bot(Bot),
    TD \= Bot,
    fasill_substitution:empty_substitution(Empty),
    fasill_substitution:put_substitution(Empty, V, TD, VarSub),
    fasill_substitution:apply(VarSub, Body, BodyS),
    fasill_substitution:apply(Unifier, BodyS, BodyU),
    fasill_substitution:compose(Sub, Unifier, SubS).
    
:- dynamic guards_last_id/1, guards_count/2.
guards_last_id(0).

/** <builtin> All solutions
    The predicates of this section are convenient for collecting solutions to a
    given goal.
*/

%!  findall(?term, +callable_term, ?list)
%
%   Find all the values that would make a goal succeed.
%   findall(Template, Goal, Instances) is true if and only if Instances is a
%   list of values in the form Templates that would make the goal Goal succeed.
%   Usually, Template and Goal share some variables, so Instances is filled with
%   the values that make Goal succeed. If there is not a single value that make
%   Goal unify, Instances will be an empty list.

eval_builtin_predicate(findall/3, state(_, Subs), selected(ExprVar, Var, Term), state(ExprVar, Subs)) :-
    Term = term(findall, Args),
    Var = term(findall, [term('&',[])|Args]).

%!  findall(+term, ?term, +callable_term, ?list)
%
%   Find all the values that would make a goal succeed.
%   findall(Connective, Template, Goal, Instances) is true if and only if
%   Instances is a list of values in the form Templates that would make the
%   goal Goal succeed. Usually, Template and Goal share some variables, so
%   Instances is filled with the values that make Goal succeed. If there is
%   not a single value that make Goal unify, Instances will be an empty list.

eval_builtin_predicate(findall/4, state(_, Subs), selected(ExprVar, Var, Term), state(ExprVar, Subs)) :-
    Term = term(findall, [Op, Template, Goal, Instances]),
    (fasill_term:fasill_var(Goal) ->
        fasill_exceptions:instantiation_error(findall/4, Error),
        fasill_exceptions:throw_exception(Error) ;
        true),
    (\+fasill_term:fasill_callable(Goal) ->
        fasill_exceptions:type_error(callable, Goal, findall/4, Error),
        fasill_exceptions:throw_exception(Error) ;
        true),
    (\+fasill_term:fasill_var(Instances), \+fasill_termfasill_list(Instances) ->
        fasill_exceptions:type_error(list, Instances, findall/4, Error),
        fasill_exceptions:throw_exception(Error) ;
        true),
    fasill_environment:lattice_call_bot(Bot),
    fasill_substitution:init_substitution(Goal, GoalVars),
    (fasill_inference:trace_level(Level) ->
        Level_ is Level+1,
        fasill_inference:retractall(trace_level(_)),
        fasill_inference:assertz(trace_level(Level_)) ;
        true),
    (fasill_environment:current_fasill_flag(trace, term(true,[])) ->
        fasill_inference:assertz(trace_derivation(trace(Level_, findall/4, state(Goal,GoalVars)))) ;
        true),
    findall([TD,Template_], (
        fasill_inference:derivation(findall/4, state(Goal,GoalVars), State, _),
        (State = state(TD,Subs_) ->
            TD \= Bot,
            fasill_substitution:apply(Subs_, Template, Template_) ;
            State = exception(Error), throw_exception(Error))
    ), List),
    maplist(nth0(0), List, TDs),
    maplist(nth0(1), List, Bodies),
    fasill_term:from_prolog_list(Bodies, Result),
    fasill_term:to_prolog(Op, Op_),
    fasill_environment:lattice_reduce_connective(Op_, TDs, TD),
    Var = term(Op_, [TD, term('~',[Instances, Result])]).

/** <builtin> Term unification
    The predicates of this section implement weak unification and syntantic
    unification.
*/

%!  '~'(@term, @term)
%
%   Weak unification.
%   X ~ Y is true if and only if X and Y are weakly unifiable. True if the weak
%   unification succeeds.

eval_builtin_predicate('~'/2, state(_, Subs), selected(ExprVar, TD, Term), state(ExprSubs, Subs_)) :-
    Term = term('~', [X,Y]),
    fasill_unification:unify(X, Y, _, state(TD, SubsUnification)),
    fasill_substitution:apply(SubsUnification, ExprVar, ExprSubs),
    fasill_substitution:compose(Subs, SubsUnification, Subs_).

%!  '='(@term, @term)
%
%   Unification.
%   X = Y is true if and only if X and Y are unifiable. True if the unification
%   succeeds.

eval_builtin_predicate('='/2, state(_, Subs), selected(ExprVar, top, Term), state(ExprSubs, Subs_)) :-
    Term = term('=', [X,Y]),
    fasill_environment:current_fasill_flag(occurs_check, term(OccursCheck, [])),
    fasill_unification:mgu(X, Y, OccursCheck, SubsUnification),
    fasill_substitution:apply(SubsUnification, ExprVar, ExprSubs),
    fasill_substitution:compose(Subs, SubsUnification, Subs_).

%!  '\~'(@term, @term)
%
%   Not weak unification.
%   X \~ Y is true if and only if X and Y are not weakly unifiable.

eval_builtin_predicate('\\~'/2, state(_, Subs), selected(ExprVar, top, Term), state(ExprVar, Subs)) :-
    Term = term('\\~', [X,Y]),
    fasill_environment:lattice_call_bot(Bot),
    (fasill_unification:unify(X, Y, _, state(TD,_)) ->
        TD == Bot ;
        true).

%!  '\='(@term, @term)
%
%   Not unification.
%   X \= Y is true if and only if X and Y are not unifiable.

eval_builtin_predicate('\\='/2, state(_, Subs), selected(ExprVar, top, Term), state(ExprVar, Subs)) :-
    Term = term('\\=', [X,Y]),
    fasill_environment:current_fasill_flag(occurs_check, term(OccursCheck, [])),
    \+fasill_unification:mgu(X, Y, OccursCheck, _).

%!  weakly_unify_with_occurs_check(@term, @term)
%
%   Weak unification with occurs check.
%   weakly_unify_with_occurs_check(X, Y) is true if and only if X and Y are
%   weakly unifiable. True if the weak unification succeeds.

eval_builtin_predicate(weakly_unify_with_occurs_check/2, state(_, Subs), selected(ExprVar, TD, Term), state(ExprSubs, Subs_)) :-
    Term = term(weakly_unify_with_occurs_check, [X,Y]),
    fasill_unification:unify(X, Y, true, state(TD, SubsUnification)),
    fasill_substitution:apply(SubsUnification, ExprVar, ExprSubs),
    fasill_substitution:compose(Subs, SubsUnification, Subs_).

%!  unify_with_occurs_check(@term, @term)
%
%   Unification with occurs check.
%   unify_with_occurs_check(X, Y) is true if and only if X and Y are unifiable.
%   True if the unification succeeds.

eval_builtin_predicate(unify_with_occurs_check/2, state(_, Subs), selected(ExprVar, top, Term), state(ExprSubs, Subs_)) :-
    Term = term(unify_with_occurs_check, [X,Y]),
    fasill_unification:mgu(X, Y, true, SubsUnification),
    fasill_substitution:apply(SubsUnification, ExprVar, ExprSubs),
    fasill_substitution:compose(Subs, SubsUnification, Subs_).

/** <builtin> Term comparison
    Comparison of arbitrary FASILL terms. Terms are ordered in the so-called
    "standard order" (dependent on the Prolog system on which FASILL is run). 
*/

%!  '=='(@term, @term)
%
%   Term identical.
%   True if the compared terms are identical.

eval_builtin_predicate('=='/2, state(_, Subs), selected(ExprVar, top, Term), state(ExprVar, Subs)) :-
    Term = term('==', [X,Y]),
    (X = var(X_), Y = var(Y_) ->
        X_ == Y_ ;
        fasill_term:to_prolog(X, X_),
        fasill_term:to_prolog(Y, Y_),
        X_ == Y_).

%!  '\=='(@term, @term)
%
%   Term not identical.
%   True if the compared terms are not identical.

eval_builtin_predicate('\\=='/2, state(_, Subs), selected(ExprVar, top, Term), state(ExprVar, Subs)) :-
    Term = term('\\==', [X,Y]),
    (X = var(X_), Y = var(Y_) ->
        X_ \== Y_ ;
        fasill_term:to_prolog(X, X_),
        fasill_term:to_prolog(Y, Y_),
        X_ \== Y_).

%!  '@<'(@term, @term)
%
%   Term less than.
%   True if the first term is less than the second one.

eval_builtin_predicate('@<'/2, state(_, Subs), selected(ExprVar, top, Term), state(ExprVar, Subs)) :-
    Term = term('@<', [X,Y]),
    (X = var(X_), Y = var(Y_) ->
        X_ @< Y_ ;
        fasill_term:to_prolog(X, X_),
        fasill_term:to_prolog(Y, Y_),
        X_ @< Y_).

%!  '@>'(@term, @term)
%
%   Term greater than.
%   True if the first term is greater than the second one.

eval_builtin_predicate('@>'/2, state(_, Subs), selected(ExprVar, top, Term), state(ExprVar, Subs)) :-
    Term = term('@>', [X,Y]),
    (X = var(X_), Y = var(Y_) ->
        X_ @> Y_ ;
        fasill_term:to_prolog(X, X_),
        fasill_term:to_prolog(Y, Y_),
        X_ @> Y_ ).

%!  '@=<'(@term, @term)
%
%   Term less than or equal to.
%   True if the first term is less than or equal to the second one.

eval_builtin_predicate('@=<'/2, state(_, Subs), selected(ExprVar, top, Term), state(ExprVar, Subs)) :-
    Term = term('@=<', [X,Y]),
    (X = var(X_), Y = var(Y_) ->
        X_ @=< Y_ ;
        fasill_term:to_prolog(X, X_),
        fasill_term:to_prolog(Y, Y_),
        X_ @=< Y_).

%!  '@>='(@term, @term)
%
%   Term greater than or equal to.
%   True if the first term is greater than or equal to the second one.

eval_builtin_predicate('@>='/2, state(_, Subs), selected(ExprVar, top, Term), state(ExprVar, Subs)) :-
    Term = term('@>=', [X,Y]),
    (X = var(X_), Y = var(Y_) ->
        X_ @>= Y_ ;
        fasill_term:to_prolog(X, X_),
        fasill_term:to_prolog(Y, Y_),
        X_ @>= Y_).

/** <builtin> Term creation and decomposition
    The predicates of this section are convenient for analysing and
    constructing terms.
*/

%!  '=..'(+nonvar, ?list)
%!  '=..'(-nonvar, +list)
%
%   Check the descomposition of a term.
%   Term =.. List is true if and only if (1) Term is an atomic term and List is
%   a list consisted of just one element, Term, or (2) Term is a compound term
%   and List is a list which has the functor name of Term as head and the
%   arguments of that functor as tail.

eval_builtin_predicate('=..'/2, state(_, Sub), selected(ExprVar, Expr, Atom), state(ExprVar, Sub)) :-
    Atom = term('=..', [Term, List]),
    (fasill_term:fasill_var(Term), fasill_term:fasill_var(List) ->
        fasill_exceptions:instantiation_error('=..'/2, Error),
        fasill_exceptions:throw_exception(Error) ;
        true),
    (\+fasill_term:fasill_list(List) ->
        fasill_exceptions:type_error(list, List, '=..'/2, Error),
        fasill_exceptions:throw_exception(Error) ;
        true),
    (\+fasill_term:fasill_var(List), \+fasill_term:fasill_list(List) ->
        fasill_exceptions:type_error(list, List, '=..'/2, Error),
        fasill_exceptions:throw_exception(Error) ; 
        true),
    (\+fasill_term:fasill_var(Term), \+fasill_term:fasill_term(Term) ->
        fasill_exceptions:type_error(atom, Term, '=..'/2, Error),
        fasill_exceptions:throw_exception(Error) ; 
        true),
    (\+fasill_term:fasill_var(Term) ->
        Term = term(Name,Args),
        fasill_term:from_prolog_list(Args,Args_),
        List_ = term('.',[term(Name,[]),Args_]),
        Expr = term('~',[List,List_]) ;
        (List = term('[]',[]) ->
            Term_ = List ;
            List = term('.',[term(Name,[]), Args]),
            fasill_term:to_prolog_list(Args,Args_),
            Term_ = term(Name, Args_)),
        Expr = term('~',[Term,Term_])).

/** <builtin> Arithmetic comparison
    This section provides predicates for arithmetic comparison.
*/

%!  '<'(@evaluable, @evaluable)
%
%   Arithmetic less than.
%   True if the first number is less than the second one.

eval_builtin_predicate('<'/2, state(_, Subs), selected(ExprVar, top, Atom), state(ExprVar, Subs)) :-
    Atom = term('<', [Left, Right]),
    fasill_arithmetic:arithmetic_comparison('<'/2, Left, Right).

%!  '>'(@evaluable, @evaluable)
%
%   Arithmetic greater than.
%   True if the first number is greater than the second one.

eval_builtin_predicate('>'/2, state(_, Subs), selected(ExprVar, top, Atom), state(ExprVar, Subs)) :-
    Atom = term('>', [Left, Right]),
    fasill_arithmetic:arithmetic_comparison('>'/2, Left, Right).

%!  '=:='(@evaluable, @evaluable)
%
%   Arithmetic equal.
%   True if both numbers are equal.

eval_builtin_predicate('=:='/2, state(_, Subs), selected(ExprVar, top, Atom), state(ExprVar, Subs)) :-
    Atom = term('=:=', [Left, Right]),
    fasill_arithmetic:arithmetic_comparison('=:='/2, Left, Right).

%!  '=\\='(@evaluable, @evaluable)
%
%   Arithmetic not equal.
%   True if the compared numbers are not equal.

eval_builtin_predicate('=\\='/2, state(_, Subs), selected(ExprVar, top, Atom), state(ExprVar, Subs)) :-
    Atom = term('=\\=', [Left, Right]),
    fasill_arithmetic:arithmetic_comparison('=\\='/2, Left, Right).

%!  '=<'(@evaluable, @evaluable)
%
%   Arithmetic less than or equal to.
%   True if the first number is less than or equal to the second one.

eval_builtin_predicate('=<'/2, state(_, Subs), selected(ExprVar, top, Atom), state(ExprVar, Subs)) :-
    Atom = term('=<', [Left, Right]),
    fasill_arithmetic:arithmetic_comparison('=<'/2, Left, Right).

%!  '>='(@evaluable, @evaluable)
%
%   Arithmetic greater than or equal to.
%   True if the first number is greater than or equal to the second one.

eval_builtin_predicate('>='/2, state(_, Subs), selected(ExprVar, top, Atom), state(ExprVar, Subs)) :-
    Atom = term('>=', [Left, Right]),
    fasill_arithmetic:arithmetic_comparison('>='/2, Left, Right).

/** <builtin> Arithmetic evaluation
    This section provides predicates for arithmetic evaluation.
*/

%!  'is'(?term, @evaluable)
%
%   Evaluate expression.
%   Result is Expression is true if and only if evaluating Expression as an
%   expression gives Result as a result.

eval_builtin_predicate(is/2, state(_, Subs), selected(ExprVar, Var, Atom), state(ExprVar, Subs)) :-
    Atom = term(is, [Variable, Expression]),
    fasill_arithmetic:arithmetic_evaluation('is'/2, Expression, Result),
    Var = term('~', [Variable, Result]).

/** <builtin> Type testing
    This section provides predicates for type testing.
*/

%!  atom(@term)
%
%   Check if atom.
%   atom(X) is true if and only if X is an atom.

eval_builtin_predicate(atom/1, state(_, Subs), selected(ExprVar, top, Atom), state(ExprVar, Subs)) :-
    Atom = term(atom, [term(_, [])]).

%!  compound(@term)
%
%   Check if compound.
%   compound(X) is true if and only if X is a compound term (neither atomic nor
%   a variable).

eval_builtin_predicate(compound/1, state(_, Subs), selected(ExprVar, top, Atom), state(ExprVar, Subs)) :-
    Atom = term(compound, [term(_, [_|_])]).

%!  var(@term)
%
%   Check if variable.
%   var(X) is true if and only if X is a variable.

eval_builtin_predicate(var/1, state(_, Subs), selected(ExprVar, top, Atom), state(ExprVar, Subs)) :-
    Atom = term(var, [var(_)]).

%!  nonvar(@term)
%
%   Check if not variable.
%   nonvar(X) is true if and only if X is not a variable.

eval_builtin_predicate(nonvar/1, state(_, Subs), selected(ExprVar, top, Atom), state(ExprVar, Subs)) :-
    Atom = term(nonvar, [X]),
    X \= var(_).

%!  number(@term)
%
%   Check if integer or float.
%   number(X) is true if and only if X is either an integer or a float.

eval_builtin_predicate(number/1, state(_, Subs), selected(ExprVar, top, Atom), state(ExprVar, Subs)) :-
    Atom = term(number, [num(_)]).

%!  float(@term)
%
%   Check if float.
%   float(X) is true if and only if X is a float.

eval_builtin_predicate(float/1, state(_, Subs), selected(ExprVar, top, Atom), state(ExprVar, Subs)) :-
    Atom = term(float, [num(X)]),
    float(X).

%!  integer(@term)
%
%   Check if integer.
%   integer(X) is true if and only if X is an integer.

eval_builtin_predicate(integer/1, state(_, Subs), selected(ExprVar, top, Atom), state(ExprVar, Subs)) :-
    Atom = term(integer, [num(X)]),
    integer(X).

%!  ground(@term)
%
%   Check if ground term.
%   ground(X) is true if and only if X is a ground term.

eval_builtin_predicate(ground/1, state(_, Subs), selected(ExprVar, top, Atom), state(ExprVar, Subs)) :-
    Atom = term(ground, [X]),
    fasill_term:fasill_ground(X).

/** <builtin> Atom processing
    This section provides predicates for atom processing.
*/

%!  atom_length(+atom, ?integer)
%
%   Length of an atom.
%   atom_length(Atom, Length) is true if and only if the number of characters
%   in the name of Atom is equal to Length. If Length is not instantiated,
%   atom_length will calculate the length of Atom's name.

eval_builtin_predicate(atom_length/2, state(_, Sub), selected(ExprVar, Var, Term), state(ExprVar, Sub)) :-
    Term = term(atom_length, [Atom,Length]),
    (fasill_term:fasill_var(Atom) ->
        fasill_exceptions:instantiation_error(atom_length/2, Error),
        fasill_exceptions:throw_exception(Error) ;
        true),
    (\+fasill_term:fasill_atom(Atom) ->
        fasill_exceptions:type_error(atom, Atom, atom_length/2, Error),
        fasill_exceptions:throw_exception(Error) ;
        true),
    (\+fasill_term:fasill_var(Length), \+fasill_term:fasill_integer(Length) ->
        fasill_exceptions:type_error(integer, Length, atom_length/2, Error),
        fasill_exceptions:throw_exception(Error) ;
        true),
    fasill_term:to_prolog(Atom, X),
    fasill_term:to_prolog(Length, Y),
    atom_length(X, Y),
    fasill_term:from_prolog(X, Fx),
    fasill_term:from_prolog(Y, Fy),
    Var = term('&', [term('~',[Atom, Fx]), term('~',[Length, Fy])]).

%!  atom_concat(?atom, ?atom, +atom)
%!  atom_concat(+atom, +atom, -atom)
%
%   Concatenate characters.
%   atom_concat(Start, End, Whole) is true if and only if Whole  is the atom
%   obtained by adding the characters of End at the end of Start. If Whole is
%   the only argument instantiated, atom_concat/3 will obtain all possible
%   decompositions of it.

eval_builtin_predicate(atom_concat/3, state(_, Sub), selected(ExprVar, Var, Atom), state(ExprVar, Sub)) :-
    Atom = term(atom_concat, [Start,End,Whole]),
    (fasill_term:fasill_var(Whole), fasill_term:fasill_var(Start) ->
        fasill_exceptions:instantiation_error(atom_concat/3, Error),
        fasill_exceptions:throw_exception(Error) ;
        true),
    (fasill_term:fasill_var(Whole), fasill_term:fasill_var(End) ->
        fasill_exceptions:instantiation_error(atom_concat/3, Error),
        fasill_exceptions:throw_exception(Error) ;
        true),
    (\+fasill_term:fasill_var(Start), \+fasill_term:fasill_atom(Start) ->
        fasill_exceptions:type_error(atom, Start, atom_concat/3, Error),
        fasill_exceptions:throw_exception(Error) ;
        true),
    (\+fasill_term:fasill_var(End), \+fasill_term:fasill_atom(End) ->
        fasill_exceptions:type_error(atom, End, atom_concat/3, Error),
        fasill_exceptions:throw_exception(Error) ;
        true),
    (\+fasill_term:fasill_var(Whole), \+fasill_term:fasill_atom(Whole) ->
        fasill_exceptions:type_error(atom, Whole, atom_concat/3, Error),
        fasill_exceptions:throw_exception(Error) ;
        true),
    fasill_term:to_prolog(Start, X),
    fasill_term:to_prolog(End, Y),
    fasill_term:to_prolog(Whole, Z),
    atom_concat(X, Y, Z),
    fasill_term:from_prolog(X, Fx),
    fasill_term:from_prolog(Y, Fy),
    fasill_term:from_prolog(Z, Fz),
    Var = term('&', [
        term('~',[Start,Fx]), term('&',[
            term('~',[End,Fy]),
                term('~',[Whole,Fz])])]).