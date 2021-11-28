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

:- module(fasill_unfolding, [
    % classic unfolding
    classic_unfold/1,
    classic_unfold/2,
    classic_unfold_by_id/1,
    classic_unfold_by_id/2,
    % safety conditions
    bound_similarity/1,
    bound_similarity_by_id/1,
    head_preserving/1,
    head_preserving_by_id/1,
    body_overriding/1,
    body_overriding_by_id/1,
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

:- use_module(fasill_substitution).
:- use_module(fasill_environment).
:- use_module(fasill_inference).
:- use_module(fasill_term).

/** <module> Unfolding
    This library provides predicates for unfolding FASILL programs.
    
    Unfolding is a well-known, widely used, semantics-preserving program
    transformation operation which is able to improve programs, generating more
    efficient code. The unfolding transformation traditionally considered in
    pure logic programming consists in the replacement of a program clause $C$
    by the set of clauses obtained after applying a computation step in all its
    possible forms on the body of $C$.

    Let $\mathcal{P} = \langle\Pi,\mathcal{R},L\rangle$ be a FASILL program and
    let $R: A\leftarrow \mathcal{B} \in \Pi$ be a program rule with no empty
    body. Then, the classic unfolding of rule $R$ in program $\mathcal{P}$ is
    the new program $\mathcal{P}'= \langle\Pi', \mathcal{R}, L\rangle,
    \Pi' = (\Pi - \{R\}) \cup \{A\sigma\leftarrow \mathcal{B}' ~|~
    \langle\mathcal{B};id\rangle \leadsto\ \langle\mathcal{B}';\sigma\rangle\}$.

    In logic programming, classic unfolding preserves the computed answers and
    it leads to shorter derivations. However, in FASILL the classic unfolding
    may lose fca's when failure steps are involved, for some goals subsumed by
    the head of the unfolded rule. Furthermore, it may lead to wrong fca's when
    similarities are involved.
*/

% CLASSIC UNFOLDING

%!  classic_unfold_by_id(?Id)
%
%   This predicate succeeds unfolding the FASILL rule Rule with identifier Id.
%   This predicate has the side effect of retracting the rule Rule and
%   asserting the new unfolded rules.

classic_unfold_by_id(Id) :-
    fasill_environment:fasill_rule(Head, Body, Info),
    member(id(Id), Info), !,
    classic_unfold(fasill_rule(Head, Body, Info)).

%!  classic_unfold_by_id(?Id, ?Unfolded)
%
%   This predicate succeeds when Id is the identifier of a FASILL rule Rule
%   and Unfolded is an unfolded rule of Rule.

classic_unfold_by_id(Id, Rule) :-
    fasill_environment:fasill_rule(Head, Body, Info),
    member(id(Id), Info), !,
    classic_unfold(fasill_rule(Head, Body, Info), Rule).

%!  classic_unfold(+Rule)
%
%   This predicate succeeds unfolding the FASILL rule Rule. This predicate has
%   the side effect of retracting the rule Rule and asserting the new unfolded
%   rules.

classic_unfold(R1) :-
    findall(R, classic_unfold(R1, R), Rules),
    Rules \= [],
    fasill_environment:once(retract(R1)),
    ( member(Rule, Rules),
      fasill_environment:assertz(Rule),
      fail ; true ),
    fasill_environment:sort_rules_by_id.

%!  classic_unfold(+Rule, ?Unfolded)
%
%   This predicate succeeds when Rule is a FASILL rule and Unfolded is an
%   unfolded rule of Rule.

:- dynamic(unfolding_id/1).
classic_unfold(R1, R2) :-
    retractall(unfolding_id(_)),
    assertz(unfolding_id(1)),
    R1 = fasill_rule(head(Head), body(Body), [id(Id)|Info]),
    HeadR = Head, BodyR = Body,
    fasill_substitution:init_substitution(BodyR, Vars),
    fasill_inference:inference(unfolding/0, state(BodyR, Vars), state(Expr, Subs), _),
    BodyR \= Expr,
    fasill_substitution:apply(Subs, HeadR, Head_),
    ( unfolding_id(R),
      atom_number(Atom, R),
      atom_concat(Id, '-', Id_),
      atom_concat(Id_, Atom, Id2),
      retractall(unfolding_id(_)),
      succ(R, N),
      assertz(unfolding_id(N)) ),
    R2 = fasill_rule(head(Head_), body(Expr), [id(Id2)|Info]).

% SAFETY CONDITIONS

%!  bound_similarity(+Rule)
%
%   This predicate succeeds when Rule is a FASILL rule that holds the 
%   bound-similarity condition.
bound_similarity(R) :-
    R = fasill_rule(head(Head), body(Body), _),
    fasill_substitution:init_substitution(Head, Sub0),
    forall(
        fasill_inference:inference(unfolding/0, state(Body, Sub0), state(_, Sub1), _),
        is_bound_substitution(Sub1)
    ).

%!  bound_similarity_by_id(+Id)
%
%   This predicate succeeds when Id is the identifier of a FASILL rule that
%   holds the bound-similarity condition.
bound_similarity_by_id(Id) :-
    fasill_environment:fasill_rule(Head, Body, Info),
    member(id(Id), Info), !,
    bound_similarity(fasill_rule(Head, Body, Info)).

%!  head_preserving(+Rule)
%
%   This predicate succeeds when Rule is a FASILL rule that holds the 
%   head-preserving condition.
head_preserving(R) :-
    R = fasill_rule(head(Head), body(Body), _),
    fasill_substitution:init_substitution(Head, Sub0),
    forall((
        fasill_inference:inference(unfolding/0, state(Body, Sub0), state(_, Sub1), _),
        fasill_substitution:apply(Sub1, Head, Head1)
    ),
        fasill_inference:is_rename(Head, Head1)
    ).

%!  bound_similarity_by_id(+Id)
%
%   This predicate succeeds when Id is the identifier of a FASILL rule that
%   holds the head-preserving condition.
head_preserving_by_id(Id) :-
    fasill_environment:fasill_rule(Head, Body, Info),
    member(id(Id), Info), !,
    head_preserving(fasill_rule(Head, Body, Info)).

%!  body_overriding(+Rule)
%
%   This predicate succeeds when Rule is a FASILL rule that holds the 
%   body-overriding condition.
body_overriding(R) :-
    R = fasill_rule(head(Head), body(Body), _),
    fasill_substitution:init_substitution(Head, Sub0),
    fasill_environment:lattice_call_bot(Bot),
    (fasill_inference:select_atom(Body, BodyBot, Bot, _) ->
        forall(
            fasill_inference:derivation(unfolding/0, state(BodyBot, Sub0), State, _),
            ( State = exception(_)
            ; State = state(TD, Sub1),
              TD = Bot,
              fasill_substitution:apply(Sub1, Head, Head1),
              fasill_inference:is_rename(Head, Head1)
            )
        ) ; true).

%!  body_overriding_by_id(+Id)
%
%   This predicate succeeds when Id is the identifier of a FASILL rule that
%   holds the body-overriding condition.
body_overriding_by_id(Id) :-
    fasill_environment:fasill_rule(Head, Body, Info),
    member(id(Id), Info), !,
    body_overriding(fasill_rule(Head, Body, Info)).

% GUARDS ON-BASED UNFOLDING

%!  guards_unfold_by_id(?Id)
%
%   This predicate succeeds unfolding the FASILL rule Rule with identifier Id.
%   This predicate has the side effect of retracting the rule Rule and
%   asserting the new unfolded rules.

guards_unfold_by_id(Id) :-
    fasill_environment:fasill_rule(Head, Body, Info),
    member(id(Id), Info), !,
    guards_unfold(fasill_rule(Head, Body, Info)).

%!  guards_unfold_by_id(?Id, ?Unfolded)
%
%   This predicate succeeds when Id is the identifier of a FASILL rule Rule
%   and Unfolded is an unfolded rule of Rule.

guards_unfold_by_id(Id, Rule) :-
    fasill_environment:fasill_rule(Head, Body, Info),
    member(id(Id), Info), !,
    guards_unfold(fasill_rule(Head, Body, Info), Rule).

%!  guards_unfold(+Rule)
%
%   This predicate succeeds unfolding the FASILL rule Rule. This predicate has
%   the side effect of retracting the rule Rule and asserting the new unfolded
%   rules.

guards_unfold(R1) :-
    findall(R, guards_unfold(R1, R), Rules),
    Rules \= [],
    fasill_environment:once(retract(R1)),
    ( member(Rule, Rules),
      fasill_environment:assertz(Rule),
      fail ; true ),
    fasill_environment:sort_rules_by_id.

%!  guards_unfold(+Rule, ?Unfolded)
%
%   This predicate succeeds when Rule is a FASILL rule and Unfolded is an
%   unfolded rule of Rule.

guards_unfold(R1, R2) :-
    R1 = fasill_rule(head(Head), body(Body), Info),
    fasill_substitution:init_substitution(Body, Vars),
    fasill_inference:select_atom(Body, Expr, Replace, _Selected), !,
    fasill_environment:similarity_tnorm(Tnorm),
    fasill_environment:fresh_variable(Var),
    findall(
        Guard,
        ( fasill_inference:inference(unfolding/0, state(Body, Vars), state(Expr, Sub), _),
          exclude_trivial_vars(Sub, SubVars),
          fasill_substitution:substitution_to_list(SubVars, GuardList),
          bound_substitution(Sub, BoundSub),
          make_guard(GuardList, G1, G2),
          Unification = term('~', [term(g, G1), term(g, G2)]),
          ReplaceVar = term(Tnorm, [Var, Replace]),
            fasill_inference:select_atom(Body, ExprVar, ReplaceVar, _),
          fasill_substitution:apply(BoundSub, ExprVar, ExprVarSub),
          Guard = term('->', [Unification, ExprVarSub])
        ),
        RegularGuards
    ),
    fasill_inference:failure_step(state(Body, Vars), state(Expr, _), _),
    (is_safe_unfolding(RegularGuards, Expr) ->
        classic_unfold(R1, R2)
    ;
        fasill_term:fasill_term_variables(Head, FSVars),
        fasill_inference:rename(FSVars, [FSVars, Expr], [FSVarsR, ExprR]),
        FailureGuard = term('->', [term('^', [term('~', [term(g, FSVars), term(g, FSVarsR)])]), ExprR]),
        append(RegularGuards, [FailureGuard], Vector),
        vector_guards(Vector, Guards),
        BodyG = term(guards, [term(on, [Guards, Var])]),
        R2 = fasill_rule(head(Head), body(BodyG), Info)
    ).
guards_unfold(R1, R2) :-
    classic_unfold(R1, R2).

%!  is_safe_unfolding(+RegularGuards, +FailureBody)
%
%   This predicate succeeds when it is safe to perform a classic unfolding.
%   I.e.:
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
        (fasill_environment:lattice_call_bot(Bot), fasill_inference:up_body(FailureBody, Bot))
    ).

%!  vector_guards(+Vector, -Guards)
%!  vector_guards(-Vector, +Guards)
%
%   Transform a list of guards Vector into a valid body Guards for the
%   *guards on* control construct.

vector_guards([X|Xs], term(';', [X,Right])) :-
    vector_guards(Xs, Right).
vector_guards([X],  X) :- !.

%!  make_guard(+Binds, -G1, -G2)
%
%   This predicates makes the pair of guards G1-G2 from a list of bindings
%   Binds.

make_guard([], [], []).
make_guard([K-V|Xs], [var(K)|Ks], [V|Vs]) :-
    make_guard(Xs, Ks, Vs).

%!  bound_substitution(+Substitution, ?BoundSubstitution)
%
%   This predicate succeeds when BoundSubstitution is Substitution restringed
%   to its variables whose images are bound terms.

bound_substitution(Sub, BoundSub) :-
    fasill_substitution:substitution_to_list(Sub, Binds),
    include(is_bound, Binds, BoundBinds),
    fasill_substitution:list_to_substitution(BoundBinds, BoundSub).

%!  is_bound_substitution(+Substitution)
%
%   Check if a substitution is bound.

is_bound_substitution(Sub) :-
    fasill_substitution:substitution_to_list(Sub, List),
    forall(member(_-Term, List), is_bound(Term)).

%!  is_bound(+Term)
%
%   Check if a term is bound.

is_bound(_-Term) :- !,
    is_bound(Term).
is_bound(term(Name, Args)) :- !,
    length(Args, Arity),
    fasill_environment:lattice_call_top(Top),
    fasill_environment:lattice_call_bot(Bot),
    forall(
        fasill_environment:similarity_between(Name, _, Arity, TD, _),
        (TD == Top ; TD == Bot)
    ),
    is_bound(Args).
is_bound([]) :- !.
is_bound([X|Xs]) :- !,
    is_bound(X),
    is_bound(Xs).
is_bound(_).

exclude_trivial_vars(Sub1, Sub2) :-
    fasill_substitution:substitution_to_list(Sub1, List1),
    exclude(trivial_var, List1, List2),
    fasill_substitution:list_to_substitution(List2, Sub2).

trivial_var(X-var(X)).

% SIMILARITY-BASED UNFOLDING

%!  unfold_by_id(?Id)
%
%   This predicate succeeds unfolding the FASILL rule Rule with identifier Id.
%   This predicate has the side effect of retracting the rule Rule and asserting
%   the new unfolded rules.

unfold_by_id(Id) :-
    fasill_environment:fasill_rule(Head, Body, Info),
    member(id(Id), Info),
    !,
    unfold(fasill_rule(Head, Body, Info)).

%!  unfold_by_id(?Id, ?Unfolded)
%
%   This predicate succeeds when Id is the identifier of a FASILL rule Rule and
%   Unfolded is an unfolded rule of Rule.

unfold_by_id(Id, Rule) :-
    fasill_environment:fasill_rule(Head, Body, Info),
    member(id(Id), Info), !,
    unfold(fasill_rule(Head, Body, Info), Rule).

%!  unfold(+Rule)
%
%   This predicate succeeds unfolding the FASILL rule Rule. This predicate has
%   the side effect of retracting the rule Rule and asserting the new unfolded
%   rules.

unfold(R1) :-
    findall(R, unfold(R1, R), Rules),
    Rules \= [],
    fasill_environment:once(retract(R1)),
    ( member(Rule, Rules),
      fasill_environment:assertz(Rule),
      fail ; true ),
    fasill_environment:sort_rules_by_id.

%!  unfold(+Rule, ?Unfolded)
%
%   This predicate succeeds when Rule is a FASILL rule and Unfolded is an
%   unfolded rule of Rule.

unfold(R1, R2) :-
    unfold(R1, R2, [rename(true)]).

unfold(R1, R2, Options) :-
    R1 = fasill_rule(head(Head), body(Body), Info),
    (member(rename(false), Options) ->
        HeadR = Head, BodyR = Body ;
        fasill_inference:rename([Head,Body], [HeadR,BodyR])),
    fasill_inference:select_atom(BodyR, BodyVar, Var, term(guards, [term(on, [Guards, TD])])),
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
    Var = term(guards, [term(on, [GuardsU, TD])]),
    R2 = fasill_rule(head(HeadR), body(BodyVar), Info).

unfold(R1, R2, _Options) :-
    guards_unfold(R1, R2).