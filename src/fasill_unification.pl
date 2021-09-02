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

:- module(fasill_unification, [
    lambda_wmgu/5,
    wmgu/4,
    mgu/4,
    unify/4,
    occurs_check/2
]).

:- use_module(fasill_substitution).
:- use_module(fasill_environment).

/** <module> Unification
    This library provides predicates for unification.
    
    In FASILL the concepts of unifier and most general unifier (mgu) are
    extended to cope with similarities. Let $\mathcal{R}$ be a similarity
    relation, $\lambda$ be a cut value and $\mathcal{E}_1$ and $\mathcal{E}_2$
    be two expressions. The substitution $\theta$ is a weak unifier of level
    $\lambda$ for $\mathcal{E}_1$ and $\mathcal{E}_2$ with respect to
    $\mathcal{R}$ if its unification degree
    $\hat{\mathcal{R}}(\mathcal{E}_1\theta, \mathcal{E}_2\theta) \geq \lambda$.
    Note that our algorithm uses a different notion of unification state, where
    an extra component accumulates an approximation degree. The unification of
    the expressions $\mathcal{E}_1$ and $\mathcal{E}_2$ is obtained by a state
    transformation sequence starting from an initial state
    $\langle\{\mathcal{E}_1 \approx \mathcal{E}_2\}, id, \alpha_0\rangle$,
    where $id$ is the identity substitution and $\alpha_0 = \top$ is the
    supremum of the lattice $(L, \leq)$. The thresholded similarity-based
    unification relation, "$\Rightarrow_\lambda$", is defined as the smallest
    relation derived by the following set of transition rules (where
    $\mathcal{V}ar(t)$ denotes the set of variables of a given term $t$):

    $$
    \frac
        {\langle\{f(t_1,\dots,t_n) \approx g(s_1,\dots,s_n)\} \cup E,
        \theta, v_1\rangle, \mathcal{R}(f, g) \wedge v_1 = v_2 \geq \lambda,
        v_2 \geq \bot}
        {\langle\{t_1 \approx s_1, \dots, t_n \approx s_n\} \cup E, \theta,
        v_2\rangle}1
    \\ \ \\
    \frac
        {\langle\{X \approx X\} \cup E, \theta, v_1\rangle}
        {\langle E, \theta, v_1\rangle}2
    \ \ \
    \frac
        {\langle\{X \approx t\} \cup E, \theta, v_1\rangle, X \not\in
        \mathcal{V}ar(t)}
        {\langle (E)\{X/t\}, \theta\{X/t\}, v_1\rangle}3
    \\ \ \\
    \frac
        {\langle\{t \approx X\} \cup E, \theta, v_1\rangle}
        {\langle\{X \approx t\} \cup E, \theta, v_1\rangle}4
    \ \ \
    \frac
        {\langle\{X \approx t\} \cup E, \theta, v_1\rangle, X \in
        \mathcal{V}ar(t)}
        {\langle Fail, \theta, v_1\rangle}5
    \\ \ \\
    \frac
        {\langle\{f(t_1,\dots,t_n) \approx g(s_1,\dots,s_n)\} \cup E, \theta,
        v_1\rangle, \mathcal{R}(f, g) \wedge v_1 = v_2 \not\geq \lambda \ or \
        v_2 = \bot}
        {\langle Fail, \theta, v_1\rangle}6
    $$

    In addition to a different notion of unification state, which uses an extra
    component to accumulate the approximation  degree obtained so far, our
    algorithm diverges from the classical algorithm of Martelli and Montanari in
    what concerns the rules 1 (Term Decomposition) and 6 (Failure Rule). Rule 1
    is triggered when the value $v_2$, resulting from the composition of the
    approximation degree, $\mathcal{R}(f, g)$, of the symbols at the root in the
    terms to be unified and the accumulated approximation degree $v_1$, is equal
    or greater than $\lambda$ and, also, greater than $\bot$ (the last condition
    deals with the case where $\mathcal{R}(f, g) \geq \lambda$ and
    $\lambda = \bot$). Otherwise, Rule 6 is triggered and the unification
    process ends with failure. Usually, given two expressions $\mathcal{E}_1$
    and $\mathcal{E}_2$, if there is a successful transition sequence,
    $\langle\{\mathcal{E}_1 \approx \mathcal{E}_2\}, id, \top\rangle
    \Rightarrow_\lambda^* \langle\emptyset, \theta, v\rangle$, then we write
    that $wmgu^\lambda_\mathcal{R}(\mathcal{E}_1, \mathcal{E}_2) = \langle
    \theta, v\rangle$, being $\theta$ the $\lambda$-wmgu of $\mathcal{E}_1$ and
    $\mathcal{E}_2$, and $v \geq \lambda$ is their unification degree.
    
    In the particular case where $\lambda = \bot$, no thresholding effects are
    achieved by our weak unification algorithm for supporting the basic
    (non-thresholded yet) operational semantics of FASILL. In the FASILL system,
    the user can set the cut value $\lambda$ by modifying the value of the flag
    `lambda_unification` (whose value is $\bot$ by default).

    For more details see:

    * Julián-Iranzo, Pascual, Ginés Moreno, and Jaime Penabad. "Thresholded
      semantic framework for a fully integrated fuzzy logic language." Journal of
      logical and algebraic methods in programming 93 (2017): 42-67.
      [https://doi.org/10.1016/j.jlamp.2017.08.002](https://doi.org/10.1016/j.jlamp.2017.08.002)
*/

%!  lambda_wmgu(+ExpressionA, +ExpressionB, +Threshold, +OccursCheck, ?WMGU)
%
%   This predicate returns the thresholded weak most general unifier
%   (lambda-wmgu) WMGU of the expressions ExpressionA and ExpressionB with
%   level Threshold.

lambda_wmgu(ExprA, ExprB, Lambda, OccursCheck, WMGU) :-
    fasill_environment:lattice_call_top(Top),
    fasill_substitution:empty_substitution(Sub),
    lambda_wmgu(ExprA, ExprB, Lambda, OccursCheck, state(Top,Sub), WMGU).

% Anonymous variable ~ Term
lambda_wmgu(var('_'), _, _, _, WMGU, WMGU) :-
    !.
% Term ~ Anonymous variable
lambda_wmgu(_, var('_'), _, _, WMGU, WMGU) :-
    !.
% Variable ~ Term
lambda_wmgu(var(V), Term, Lambda, OccursCheck, state(TD,Sub), WMGU) :-
    fasill_substitution:get_substitution(Sub, V, TermSub),
    !,
    lambda_wmgu(TermSub, Term, Lambda, OccursCheck, state(TD,Sub), WMGU).
lambda_wmgu(var(V), Term, _, OccursCheck, state(TD,Sub0), state(TD,Sub3)) :-
    !,
    (OccursCheck == true -> occurs_check(V, Term) ; true),
    fasill_substitution:list_to_substitution([V-Term], Sub1),
    fasill_substitution:compose(Sub0, Sub1, Sub2),
    fasill_substitution:put_substitution(Sub2, V, Term, Sub3).
% Term ~ Variable
lambda_wmgu(X, var(Y), Lambda, OccursCheck, State, WMGU) :-
    !,
    lambda_wmgu(var(Y), X, Lambda, OccursCheck, State, WMGU).
% Number ~ Number
lambda_wmgu(num(X), num(X), _, _, WMGU, WMGU) :-
    !.
% Term ~ Term
lambda_wmgu(term(X,Xs), term(X,Ys), Lambda, OccursCheck, State, WMGU) :-
    !,
    length(Xs, Arity),
    length(Ys, Arity),
    lambda_wmgu(Xs, Ys, Lambda, OccursCheck, State, WMGU).
lambda_wmgu(term(X,Xs), term(Y,Ys), Lambda, OccursCheck, state(TD, Sub), WMGU) :-
    !,
    length(Xs, Arity),
    length(Ys, Arity),
    fasill_environment:similarity_between(X, Y, Arity, TDxy, S),
    fasill_environment:lattice_call_top(Top),
    (TD == Top -> TD2 = TDxy; 
        (TDxy == Top -> TD2 = TD; 
            (fasill_environment:similarity_tnorm(Tnorm),
                ((S == no, Tnorm = '&'(_)) ->
                    fasill_environment:lattice_call_connective(Tnorm, [TD, TDxy], TD2),
                    fasill_environment:lattice_call_leq(Lambda, TD2)
                    ; TD2 = term(Tnorm, [TD, TDxy])
                )
            )
        )
    ),
    fasill_environment:lattice_call_bot(Bot),
    TD2 \== Bot,
    lambda_wmgu(Xs, Ys, Lambda, OccursCheck, state(TD2, Sub), WMGU).
% List ~ List
lambda_wmgu([], [], _, _, WMGU, WMGU) :-
    !.
lambda_wmgu([X|Xs], [Y|Ys], Lambda, OccursCheck, State, WMGU) :-
    !,
    lambda_wmgu(X, Y, Lambda, OccursCheck, State, StateXY),
    StateXY = state(_, Sub),
    fasill_substitution:apply(Sub, Xs, Xs_),
    fasill_substitution:apply(Sub, Ys, Ys_),
    lambda_wmgu(Xs_, Ys_, Lambda, OccursCheck, StateXY, WMGU).

%!  wmgu(+ExpressionA, +ExpressionB, +OccursCheck, ?WMGU)
%
%   This predicate returns the weak most general unifier (wmgu) WMGU of the
%   expressions ExpressionA and ExpressionB.

wmgu(ExprA, ExprB, OccursCheck, WMGU) :-
    fasill_environment:lattice_call_bot(Bot),
    lambda_wmgu(ExprA, ExprB, Bot, OccursCheck, WMGU).

%!  mgu(+ExpressionA, +ExpressionB, +OccursCheck, ?MGU)
%
%   This predicate returns the most general unifier (mgu) MGU of the
%   expressions ExpressionA and ExpressionB.

mgu(ExprA, ExprB, OccursCheck, MGU) :-
    fasill_substitution:empty_substitution(Sub),
    mgu(ExprA, ExprB, OccursCheck, Sub, MGU).

% Anonymous variable ~ Term
mgu(var('_'), _, _, Subs, Subs) :-
    !.
% Term ~ Anonymous variable
mgu(_, var('_'), _, Subs, Subs) :-
    !.
% Variable ~ Term
mgu(var(V), Term, OccursCheck, Sub, MGU) :-
    fasill_substitution:get_substitution(Sub, V, TermSub),
    !,
    mgu(TermSub, Term, OccursCheck, Sub, MGU).
mgu(var(V), Term, OccursCheck, Sub0, MGU) :-
    !,
    (OccursCheck == true -> occurs_check(V, Term) ; true),
    fasill_substitution:list_to_substitution([V-Term], Sub1),
    fasill_substitution:compose(Sub0, Sub1, Sub2),
    fasill_substitution:put_substitution(Sub2, V, Term, MGU).
% Term ~ Variable
mgu(Term, var(V), OccursCheck, Sub, MGU) :-
    !,
    mgu(var(V), Term, OccursCheck, Sub, MGU).
% Number ~ Number
mgu(num(X), num(X), _, Subs, Subs) :-
    !.
% Term ~ Term
mgu(term(X,Xs), term(X,Ys), OccursCheck, Sub, MGU) :-
    !,
    length(Xs, Length),
    length(Ys, Length),
    mgu(Xs, Ys, OccursCheck, Sub, MGU).
% List ~ List
mgu([], [], _, Subs, Subs) :-
    !.
mgu([X|Xs], [Y|Ys], OccursCheck, Sub, WMGU) :- !,
    mgu(X, Y, OccursCheck, Sub, SubXY),
    fasill_substitution:apply(SubXY, Xs, Xs_),
    fasill_substitution:apply(SubXY, Ys, Ys_),
    mgu(Xs_, Ys_, OccursCheck, SubXY, WMGU).

%!  unify(+ExpressionA, +ExpressionB, +OccursCheck, ?WMGU)
%
%   This predicate returns the (W)MGU of the expressions ExpressionA and
%   ExpressionB using the (possible weak) unification algorithm. The FASILL
%   system allows selecting the unification algorithm by setting the value of
%   the flag `weak_unification` to `true` (WMGU) or `false` (MGU). If weak
%   unification is active, it is possible to choose the unification threshold
%   by setting the flag `lambda_unification` (`bot` by default).

% Weak most general unifier
unify(Term1, Term2, OccursCheck, WMGU) :-
    fasill_environment:current_fasill_flag(weak_unification, term(true,[])), !,
    fasill_environment:current_fasill_flag(lambda_unification, Lambda_),
    (var(OccursCheck) ->
        fasill_environment:current_fasill_flag(occurs_check, term(OccursCheck, [])) ;
        true),
    (Lambda_ == bot ->
        fasill_environment:lattice_call_bot(Lambda) ;
        (Lambda_ == top ->
            fasill_environment:lattice_call_top(Lambda) ; 
            Lambda = Lambda_)),
    lambda_wmgu(Term1, Term2, Lambda, OccursCheck, WMGU).

% Most general unifier
unify(Term1, Term2, OccursCheck, state(Top, MGU)) :-
    (var(OccursCheck) ->
        fasill_environment:current_fasill_flag(occurs_check, term(OccursCheck, [])) ;
        true),
    mgu(Term1, Term2, OccursCheck, MGU),
    fasill_environment:lattice_call_top(Top).

%!  occurs_check(+Variable, +Expression)
%
%   This predicate succeds when Expression does not contain the variable
%   Variable.
occurs_check(Var, var(Var)) :-
    !,
    fail.
occurs_check(Var, term(_, Xs)) :-
    !,
    maplist(occurs_check(Var), Xs).
occurs_check(_, _).