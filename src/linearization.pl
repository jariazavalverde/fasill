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

:- module(linearization, [
	% linearization
	linearize_head_rule/1,
	linearize_head_rule/2,
	linearize_head_rule_by_id/1,
	linearize_head_rule_by_id/2,
	linearize_head_program/0,
	% extended program
	extend_rule/1,
	extend_rule/2,
	extend_rule_by_id/1,
	extend_rule_by_id/2,
	extend_program/0
]).

:- use_module(environment).
:- use_module(term).

/** <module> Linearization
    This library provides predicates for linearization of FASILL programs.

    A term or atom is linear if it does not contain multiple occurrences of the
    same variable. Any term or atom that is not linear is said to be nonlinear.
    Given a nonlinear atom $A$, the linearization of $A$ is a process by which
    the structure $\langle A_l, C_l\rangle$ is computed, where: $A_l$ is a
    linear atom built from $A$ by replacing each one of the $n_i$ multiple
    occurrences of the same variable $x_i$ by new fresh variables $y_k$
    $(1 \leq k \leq n_i)$; and $C_l$ is a set of proximity constrains
    $x_i \sim y_k$ (with $1 \leq k \leq n_i$). The operator "$s \sim t$" is
    asserting the similarity of two terms $s$ and $t$. Now, let
    $R = A \leftarrow \mathcal{B}$ be a rule and $\langle A_l, C_l\rangle$ be
    the linearization of $A$, where $C_l = \{x_1 \sim y_1, \dots,  x_n \sim y_n}$,
    $lin(R) = A_l \leftarrow x_1 \sim y_1 \wedge \dots \wedge x_n \sim y_n
    \wedge \mathcal{B}$. For a set $\Pi$ of rules, $lin(\Pi) = \{lin(R) :
    R \in \Pi\}$.

    Given a FASILL program $\mathcal{P} = \langle\Pi, \mathcal{R}, L\rangle$,
    where $\Pi$ is a set of rules, $\mathcal{R}$ is a similarity relation, and
    $L$ is a complete lattice. $Let \lambda \in L$ be a cut value. The set of
    rules which are similar to the rules in $lin(\Pi)$, for a level $lambda$,
    $\mathcal{K}_\lambda(\Pi) = \{H \leftarrow \alpha \wedge \mahtcal{B}: H'
    \leftarrow \mathcal{B} \in lin(\Pi), \mathcal{R}(H,H') = \alpha \geq \lambda\}$
    are reflecting the meaning induced by the similarity relation $\mathcal{R}$
    into the set of rules $\Pi$. Note that the concept of extended program,
    $\mathcal{K}_\lambda(\Pi)$, is a purely instrumental notion, which does not
    take part in the definition of the operational semantics of the language.

    For more details see:

    Julián-Iranzo, Pascual, Ginés Moreno, and Jaime Penabad. "Thresholded
    semantic framework for a fully integrated fuzzy logic language." Journal of
    logical and algebraic methods in programming 93 (2017): 42-67.

    DOI: https://doi.org/10.1016/j.jlamp.2017.08.002
*/

% LINEARIZATION

%!  linearize_rename(+Expression, ?Renamed, ?Substitution)
%
%   This predicate renames the expression Expression, replacing the variables
%   of the expression by fresh variables. Renamed is the expression Expression
%   with fresh variables.

linearize_rename(X, Y, Subs) :-
	term:fasill_max_variable(X, 'V', N),
	succ(N, M),
	term:fasill_count_variables(X, Vars),
	linearize_rename(X, Y, Vars, M, _, [], Subs).

linearize_rename(var(X), var(Y), Vars, N, M, Subs, [Y/var(X)|Subs]) :-
	X \== '_',
	member(X-C, Vars),
	C > 1,
	!,
	succ(N, M),
	atom_number(Atom, N),
	atom_concat('V', Atom, Y).
linearize_rename(term(Name, Xs), term(Name, Ys), Vars, N, M, Subs, Subs_) :-
	!,
	linearize_rename(Xs, Ys, Vars, N, M, Subs, Subs_).
linearize_rename([], [], _, N, N, Subs, Subs) :- !.
linearize_rename([X|Xs], [Y|Ys], Vars, N, S, Subs, Subs3) :-
	!,
	linearize_rename(X, Y, Vars, N, M, Subs, Subs2),
	linearize_rename(Xs, Ys, Vars, M, S, Subs2, Subs3).
linearize_rename(X, X, _, N, N, Subs, Subs).

%!  linearize_substitution(?Substitution, ?Body)
%
%   This predicate succeeds when ?Substitution is a FASILL substitution of
%   variables and Body is the linearized body of the substitution.

linearize_substitution([], empty).
linearize_substitution([X/Y], term('~',[var(X), Y])).
linearize_substitution([X/Y|Subs], term('&', [term('~',[var(X), Y]), LinSubs])) :-
	linearize_substitution(Subs, LinSubs).

%!  linearize_head_rule(+Rule)
%
%   This predicate succeeds linearizing the FASILL rule Rule. This predicate
%   has the side effect of retracting the rule Rule and asserting the new
%   linearized rule.

linearize_head_rule(R1) :-
	linearize_head_rule(R1, R2),
	environment:once(retract(R1)),
	environment:assertz(R2),
	environment:sort_rules_by_id.

%!  linearize_head_rule(+Rule, ?Linearized)
%
%   This predicate succeeds when Rule is a FASILL rule and Linearized is a
%   linearized rule of Rule.

linearize_head_rule(R1, R2) :-
    R1 = fasill_rule(head(Head), Body, [id(Id)|Info]),
    linearize_rename(Head, Head2, Subs),
    reverse(Subs, Subs_),
    linearize_substitution(Subs_, LinBody),
    (Body == empty ->
        (LinBody == empty ->
			Body2 = empty ;
			Body2 = body(LinBody)) ;
        (LinBody == empty ->
			Body2 = Body ;
			Body = body(Body_),
			Body2 = body(term('&', [LinBody, Body_])))
    ),
    atom_concat(Id, 'L', IdL),
    R2 = fasill_rule(head(Head2), Body2, [id(IdL)|Info]).

%!  linearize_head_rule_by_id(?Id)
%
%   This predicate succeeds linearizing the FASILL rule with identifier Id.
%   This predicate has the side effect of retracting the rule and asserting the
%   new linearized rule.

linearize_head_rule_by_id(Id) :-
	environment:fasill_rule(Head, Body, Info),
	member(id(Id), Info), !,
	linearize_head_rule(fasill_rule(Head, Body, Info)).

%!  linearize_head_rule_by_id(?Id, ?Linearized)
%
%   This predicate succeeds when Id is the identifier of a FASILL rule and
%   Linearized is a linearized rule.

linearize_head_rule_by_id(Id, Rule) :-
    environment:fasill_rule(Head, Body, Info),
    member(id(Id), Info), !,
    linearize_head_rule(fasill_rule(Head, Body, Info), Rule).

%!  linearize_head_program
%
%   This predicate succeeds linearizing the FASILL rules of the current program.
%   This predicate has the side effect of retracting the rules and asserting the
%   new linearized rules.

linearize_head_program :-
	environment:fasill_rule(Head, Body, Info),
	linearize_head_rule(fasill_rule(Head, Body, Info)),
	fail ; true.

% EXTENDED PROGRAM

%!  extend_term(+Term, -ExtendedTerm, -TD)
%
%   This predicate succeeds when ExtendedTerm is an extended term of Term
%   with truth degree TD. It can be used to generate, by reevaluation, all
%   possible extended terms of a given term.

extend_term(Term1, Term2, TD) :-
	current_fasill_flag(lambda_unification, Lambda_),
	(Lambda_ == bot ->
		environment:lattice_call_bot(Lambda) ;
		(Lambda_ == top -> 
			environment:lattice_call_top(Lambda) ;
			Lambda = Lambda_)
	),
	environment:lattice_call_top(Top),
	extend_term(Term1, Term2, Lambda, Top, TD).
extend_term(var(X), var(X), _, TD, TD).
extend_term(num(X), num(X), _, TD, TD).
extend_term(term(X, Xs), term(Y, Ys), Lambda, CurrentTD, TD) :-
	length(Xs, Arity),
	(	X = Y,
		lattice_call_top(Sim)
	;
		environment:similarity_between(X, Y, Arity, Sim, _),
		nonvar(Y),
		X \== Y
	),
	environment:similarity_tnorm(Tnorm),
	environment:lattice_call_connective(Tnorm, [CurrentTD, Sim], TDnorm),
	environment:lattice_call_leq(Lambda, TDnorm),
	extend_term(Xs, Ys, Lambda, TDnorm, TD).
extend_term([], [], _, TD, TD).
extend_term([X|Xs], [Y|Ys], Lambda, TD1, TD3) :-
	extend_term(X, Y, Lambda, TD1, TD2),
	extend_term(Xs, Ys, Lambda, TD2, TD3).

%!  extend_rule(+Rule)
%
%   This predicate succeeds extending the FASILL rule Rule. This predicate has
%   the side effect of retracting the rule Rule and asserting the new extended
%   rules.

extend_rule(R1) :-
	environment:retract(R1),
	(	extend_rule(R1, R2),
		environment:assertz(R2),
		fail ; true ),
	environment:sort_rules_by_id.

%!  extend_rule(+Rule, ?Extended)
%
%   This predicate succeeds when Rule is a FASILL rule and Extended is an
%   extended rule of Rule.

extend_rule(R1, R2) :-
	environment:lattice_call_top(Top),
	linearize_head_rule(R1, Rl),
	Rl = fasill_rule(head(HeadL), Body, [id(Id)|Info]),
	extend_term(HeadL, HeadE, TD),
	atom_concat(Id, ex, IdEx),
	(Body == empty ->
		(TD == Top ->
			BodyE = empty ;
			BodyE = body(TD)) ;
		(TD == Top ->
			BodyE = Body ;
			Body = body(Body_),
			BodyE = body(term('&', [TD, Body_])))
	),
	R2 = fasill_rule(head(HeadE), BodyE, [id(IdEx)|Info]).

%!  extend_rule_by_id(?Id)
%
%   This predicate succeeds extending the FASILL rule with identifier Id. This
%   predicate has the side effect of retracting the rule and asserting the new
%   extended rules.

extend_rule_by_id(Id) :-
	environment:fasill_rule(Head, Body, Info),
	member(id(Id), Info),
	!,
	extend_rule(fasill_rule(Head, Body, Info)).

%!  extend_rule_by_id(?Id, ?Extended)
%
%   This predicate succeeds when Id is the identifier of a FASILL rule and
%   Extended is a extended rule.

extend_rule_by_id(Id, Rule) :-
	environment:fasill_rule(Head, Body, Info),
	member(id(Id), Info), !,
	extend_rule(fasill_rule(Head, Body, Info), Rule).

%!  extend_program
%
%   This predicate succeeds extending the FASILL rules of the current program.
%   This predicate has the side effect of retracting the rules and asserting the
%   new extended rules.

extend_program :-
	linearize_head_program,
	environment:fasill_rule(Head, Body, Info),
	extend_rule(fasill_rule(Head, Body, Info)),
	fail ; true.