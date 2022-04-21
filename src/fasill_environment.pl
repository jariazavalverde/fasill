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

:- module(fasill_environment, [
    % flags
    current_fasill_flag/2,
    is_fasill_flag_value/2,
    set_fasill_flag/2,
    % rules
    fasill_rule/3,
    program_clause/2,
    program_rule_id/2,
    program_consult/1,
    program_import_prolog/1,
    program_has_predicate/1,
    program_retractall/0,
    query_consult/2,
    sort_rules_by_id/0,
    fasill_print_rule/1,
    % lattices
    lattice_tnorm/1,
    lattice_tconorm/1,
    lattice_call_bot/1,
    lattice_call_top/1,
    lattice_call_member/1,
    lattice_call_members/1,
    lattice_call_members/2,
    lattice_call_exclude/1,
    lattice_call_leq/2,
    lattice_call_distance/3,
    lattice_call_supremum/3,
    lattice_call_connective/3,
    lattice_reduce_connective/3,
    lattice_consult/1,
    % similarities
    similarity_tnorm/1,
    similarity_between/5,
    similarity_consult/1,
    % test cases (tuning)
    testcases_consult/1,
    fasill_testcase/2,
    fasill_testcase_precondition/1,
    % variables
    fresh_variable/1
]).

:- use_module(fasill_parser).
:- use_module(fasill_exceptions).
:- use_module(fasill_inference).
:- use_module(fasill_term).

/** <module> Environment
    This library provides predicates for environment manipulation (consulting
    programs, lattices and similarity relations).
    
    A FASILL program is a tuple $\langle\Pi, \mathcal{R}, L\rangle$ where $\Pi$
    is a set of rules, $\mathcal{R}$ is a similarity relation between the
    elements of the signature $\Sigma$ of $\Pi$, and $L$ is a complete lattice.
    A rule has the form $A \leftarrow \mathcal{B}$, where $A$ is an atomic
    formula called head and $\mathcal{B}$, called body, is a well-formed
    formula (built from atomic formulas $B_1, \dots, B_n$, truth values of the
    lattice and connectives).

    All relevant components of each lattice can be encapsulated inside a Prolog
    file which must contain the definitions of a minimal set of predicates
    defining the set of valid elements, the full or partial ordering
    established among them, as well as the repertoire of fuzzy connectives
    which can be used for their subsequent manipulation.

    Given a domain $\mathcal{U}$ and a lattice $L$ with a fixed t-norm, a 
    similarity relation $\mathcal{R}$ is a fuzzy binary relation on
    $\mathcal{U}$ fulfilling the reflexive, symmetric and transitive properties.
    FASILL takes a set of similarity equations $f/n \sim g/n = r$, where $f$
    and $g$ are propositional variables or constants and $r$ is an element of
    $L$, and generates a valid similarity relation by applying the reflexive,
    symmetric and transitive closures over the initial scheme.
*/

% DYNAMIC

:- dynamic
    fasill_flag/3,
    fasill_rule/3,
    fasill_testcase/2,
    fasill_testcase_precondition/1,
    fasill_predicate/1,
    fasill_lattice_tnorm/1,
    fasill_similarity_tnorm/1,
    fasill_similarity_tconorm/1,
    fasill_similarity/4,
    fasill_warning/1,
    current_lattice_top/1,
    current_lattice_bot/1.

% FLAGS

%!  fasill_flag(?Flag, ?PossibleValues, ?CurrentValue)
%
%   This predicate succeeds when Flag is a FASILL flag, that can take the
%   serie of values PossibleValues and with CurrentValue as the current value
%   in the environment.

fasill_flag(trace, [term(false,[]), term(true,[])], term(false,[])).
fasill_flag(weak_unification, [term(false,[]), term(true,[])], term(true,[])).
fasill_flag(quoted_chars, [term(chars,[]), term(codes,[]), term(atom,[])], term(chars,[])).
fasill_flag(unknown, [term(error,[]), term(fail,[]), term(warning,[])], term(error,[])).
fasill_flag(occurs_check, [term(false,[]), term(true,[])], term(false,[])).
fasill_flag(depth_limit, [num(_)], num(0)).
fasill_flag(symbolic, [term(false,[]), term(true,[])], term(true,[])).
fasill_flag(failure_steps, [term(false,[]), term(true,[])], term(true,[])).
fasill_flag(interpretive_steps, [term(short,[]), term(long,[])], term(short,[])).
fasill_flag(simplification_steps, [term(false,[]), term(true,[])], term(false,[])).
fasill_flag(lambda_unification, [_], bot).
fasill_flag(operators, [term(false,[]), term(true,[])], term(true,[])).

%!  current_fasill_flag(?Flag, ?Value)
%
%   This predicate succeeds when Flag is a FASILL flag, and Value is the
%   current value of the flag in the environment.

current_fasill_flag(Flag, Value) :-
    fasill_flag(Flag, _, Value).

%!  is_fasill_flag_value(+Flag, +Value)
%
%   This predicate succeeds when Flag is a FASILL flag and Value is a possible
%   value for the flag.

is_fasill_flag_value(Flag, Value) :-
    atomic(Flag), nonvar(Value),
    fasill_flag(Flag, Values, _),
    is_list(Values),
    !,
    member(Value, Values),
    !.
is_fasill_flag_value(Flag, Value) :-
    atomic(Flag), nonvar(Value),
    fasill_flag(Flag, td, _),
    !,
    (Value == bot ; Value == top ; lattice_call_member(Value)),
    !.

%!  set_fasill_flag(+Flag, +Value)
%
%   This predicate succeeds when Flag is a FASILL flag and Value is a possible
%   value for the flag. This predicate has the side effect of changing the
%   current value for the flag.

set_fasill_flag(Flag, Value) :-
    atomic(Flag), nonvar(Value),
    is_fasill_flag_value(Flag, Value),
    fasill_flag(Flag, Values, _),
    retractall(fasill_flag(Flag, _, _)),
    assertz(fasill_flag(Flag, Values, Value)).

% RULES MANIPULATION

%!  program_clause(?Indicator, ?Rule)
%
%   This predicate succeeds when Rule is a rule loaded into the environment
%   whose indicator is Indicator.

program_clause(Name/Arity, fasill_rule(head(term(Name, Args)), Body, Info)) :-
    fasill_rule(head(term(Name, Args)), Body, Info),
    length(Args, Arity).

%!  program_rule_id(+Rule, ?Id)
%
%   This predicate succeeds when Id is the identifier of the rule Rule.

program_rule_id(fasill_rule(_,_,Info), Id) :- member(id(Id), Info).

%!  program_consult(+Path)
%
%   This predicate loads the FASILL program from the file +Path into the
%   environment. This predicate cleans the previous rules.

program_consult(Path) :-
    program_retractall,
    fasill_parser:file_program(Path, Rules),
    (   member(Rule, Rules),
        assertz(Rule),
        Rule = fasill_rule(head(term(Name,Args)),_,_),
        length(Args,Arity),
        (catch(fasill_predicate(Name/Arity), _, fail) ->
            true ;
            assertz(fasill_predicate(Name/Arity))),
        fail ; true).

%!  program_import_prolog(+Path)
%
%   This predicate loads the Prolog program from the file Path into the
%   environment. This predicate doesn't cleans the previous rules.

:- dynamic last_prolog_id/1.
last_prolog_id(0).

program_import_prolog(Path) :-
    set_prolog_flag(double_quotes, atom),
    open(Path, read, Stream),
    once(program_import_prolog_(Stream)).
program_import_prolog_(Stream) :-
    read(Stream, PrologTerm),
    PrologTerm \= end_of_file,
    from_prolog(PrologTerm, FasillTerm),
    (FasillTerm = term(':-', [Head,Body_]) ->
        Body = body(Body_) ;
        Head = FasillTerm, Body = empty),
    last_prolog_id(N),
    succ(N, M),
    retractall(last_prolog_id(_)),
    asserta(last_prolog_id(M)),
    atom_number(A, N),
    atom_concat('Pr', A, Id),
    Rule = fasill_rule(head(Head), Body, [id(Id), syntax(prolog)]),
    Head = term(Name, Args),
    assertz(Rule),
    length(Args, Arity),
    (catch(fasill_predicate(Name/Arity), _, fail) ->
        true ;
        assertz(fasill_predicate(Name/Arity))),
    program_import_prolog_(Stream).
program_import_prolog_(Stream) :-
    close(Stream).

%!  query_consult(+Path, ?State)
%
%   This predicate loads the FASILL goal from the file Path into the
%   environment and runs it.

query_consult(Path, State) :-
    fasill_parser:file_query(Path, Query),
    fasill_inference:query(Query, State).

%!  program_has_predicate(?Indicator)
%
%   This predicate succeeds when Indicator is the indicator of a predicate
%   asserted in the program loaded in the current environment.

program_has_predicate(Name/Arity) :-
    (fasill_predicate(Name/Arity) ;
    lattice_call_bot(Bot),
    similarity_between(Name, Other, Arity, TD, _),
    TD \= Bot,
    fasill_predicate(Other/Arity)),
    !.

%!  program_retractall
%
%   This predicate succeeds cleaning all the rules loaded in the current
%   environment.

program_retractall :-
    retractall(fasill_rule(_,_,_)),
    retractall(fasill_predicate(_)).

%!  sort_rules_by_id
%
%   This predicate retracts all the rules from the current environment and
%   asserts them ordered by the identifier.

sort_rules_by_id :-
    findall(fasill_rule(X,Y,Z), fasill_rule(X,Y,Z), Rules),
    predsort(compare_rule_id, Rules, Sorted),
    retractall(fasill_rule(_,_,_)),
    ( member(Rule, Sorted),
        assertz(Rule),
        fail ; true ).

%!  fasill_print_rule(+Rule)
% 
%   This predicate writes a FASILL rule for the standard output.

% Fact
fasill_print_rule(fasill_rule(head(Head), empty, _Info)) :-
    fasill_print_term(Head),
    write('.'), !.
% Rule
fasill_print_rule(fasill_rule(head(Head), body(Body), Info)) :-
    fasill_print_term(Head),
    (member(syntax(fasill), Info) ->
        write(' <- ') ;
        write(' :- ')),
    fasill_print_term(Body),
    write('.'), !.

%!  compare_rule_id(?Delta, +Rule1, +Rule2)
%
%   This predicate succeeds when Delta is the ordering relation (<, > or =) for
%   rules Rule1 and Rule2, compared by their identifiers.

compare_rule_id(Delta, X, Y) :-
    X = fasill_rule(_,_,[id(IdX)|_]),
    Y = fasill_rule(_,_,[id(IdY)|_]),
    atomic_list_concat(Xs, '-', IdX),
    atomic_list_concat(Ys, '-', IdY),
    maplist(atom_number, Xs, Xs_),
    maplist(atom_number, Ys, Ys_),
    compare(Delta, Xs_, Ys_).

% LATTICES

%!  lattice_tnorm(?Tnorm)
%
%   This predicate succeeds when Tnorm is the current t-norm asserted in the
%   environment.

lattice_tnorm(Tnorm) :-
    catch(tnorm(Tnorm), _, fail),
    !.
lattice_tnorm(Tnorm) :-
    current_predicate(Name/3),
    atom_concat(and_, Tnorm, Name),
    !.
lattice_tnorm(Tnorm) :-
    atom_concat(and_, Tnorm, Name),
    fasill_exceptions:existence_error(procedure, Name/3, lattice/0, Error),
    fasill_exceptions:throw_exception(Error).

%!  lattice_tconorm(?Tconorm)
%
%   This predicate succeeds when Tconorm is the current t-conorm asserted in
%   the environment.

lattice_tconorm(Tconorm) :-
    catch(tconorm(Tconorm), _, fail),
    !.
lattice_tconorm(Tconorm) :-
    current_predicate(Name/3),
    atom_concat(or_, Tconorm, Name),
    !.
lattice_tconorm(Tconorm) :-
    atom_concat(or_, Tconorm, Name),
    fasill_exceptions:existence_error(procedure, Name/3, lattice/0, Error),
    fasill_exceptions:throw_exception(Error).

%!  lattice_call_bot(-Bot)
%
%   This predicate succeeds when Bot is the bottom member of the lattice loaded
%   into the environment.

:- dynamic(current_lattice_bot/1).

lattice_call_bot(Bot) :-
    current_lattice_bot(Bot),
    !.
lattice_call_bot(Bot) :-
    current_predicate(bot/1),
    !,
    bot(Prolog),
    fasill_term:from_prolog(Prolog, Bot),
    asserta(current_lattice_bot(Bot)).
lattice_call_bot(_) :-
    fasill_exceptions:existence_error(procedure, bot/1, lattice/0, Error),
    fasill_exceptions:throw_exception(Error).

%!  lattice_call_top(-Top)
%
%   This predicate succeeds when Top is the top member of the lattice loaded
%   into the environment.

:- dynamic(current_lattice_top/1).

lattice_call_top(Top) :-
    current_lattice_top(Top),
    !.
lattice_call_top(Top) :-
    current_predicate(top/1),
    !,
    top(Prolog),
    fasill_term:from_prolog(Prolog, Top),
    asserta(current_lattice_top(Top)).
lattice_call_top(_) :-
    fasill_exceptions:existence_error(procedure, top/1, lattice/0, Error),
    fasill_exceptions:throw_exception(Error).

%!  lattice_call_member(+Member)
%
%   This predicate succeeds when Member is a member of the lattice loaded into
%   the environment.

lattice_call_member(var(_)) :-
    !,
    fail.
lattice_call_member(Member) :-
    current_predicate(member/1),
    !,
    fasill_term:to_prolog(Member, Prolog),
    member(Prolog).
lattice_call_member(_) :-
    fasill_exceptions:existence_error(procedure, member/1, lattice/0, Error),
    fasill_exceptions:throw_exception(Error).

%!  lattice_call_members(-Members)
%
%   This predicate succeeds when -Members is a list of members of the lattice
%   loaded into the environment.

lattice_call_members(Members) :-
    current_predicate(members/1),
    !,
    members(Prolog),
    fasill_term:maplist(from_prolog, Prolog, Members).
lattice_call_members(_) :-
    fasill_exceptions:existence_error(procedure, members/1, lattice/0, Error),
    fasill_exceptions:throw_exception(Error).

%!  lattice_call_members(+Constant, -Members)
%
%   This predicate succeeds when -Members is a list of members for a symbolic
%   constant Constant in the lattice loaded into the environment.

lattice_call_members(Constant, Members) :-
    current_predicate(members/2),
    members(Constant, Prolog),
    fasill_term:maplist(from_prolog, Prolog, Members),
    !.
lattice_call_members(_, Members) :-
    lattice_call_members(Members).

%!  lattice_call_exclude(+Exclude)
%
%   This predicate succeeds when -Exclude is a predicate indicator excluded
%   (for tuning) in the lattice loaded into the environment.

lattice_call_exclude(Exclude) :-
    current_predicate(exclude/1),
    exclude(Exclude),
    !.

%!  lattice_call_leq(+Member1, +Member2)
%
%   This predicate succeeds when Member1 is less of equal than Member2 with the
%   lattice loaded into the environment.

lattice_call_leq(Member1, Member2) :-
    current_predicate(leq/2),
    !,
    fasill_term:to_prolog(Member1, Prolog1),
    fasill_term:to_prolog(Member2, Prolog2),
    leq(Prolog1, Prolog2).
lattice_call_leq(_, _) :-
    fasill_exceptions:existence_error(procedure, leq/2, lattice/0, Error),
    fasill_exceptions:throw_exception(Error).

%!  lattice_call_supremum(+Member1, +Member2, -Supremum)
%
%   This predicate succeeds when Member1 and Member2 are members of the lattice
%   loaded into the environment, and Supremum is the supremum of both.

lattice_call_supremum(Member1, Member2, Supremum) :-
    current_predicate(supremum/3),
    !,
    fasill_term:to_prolog(Member1, Prolog1),
    fasill_term:to_prolog(Member2, Prolog2),
    supremum(Prolog1, Prolog2, Prolog3),
    fasill_term:from_prolog(Prolog3, Supremum).
lattice_call_supremum(_, _, _) :-
    fasill_exceptions:existence_error(procedure, supremum/3, lattice/0, Error),
    fasill_exceptions:throw_exception(Error).

%!  lattice_call_distance(+Member1, +Member2, -Distance)
%
%   This predicate succeeds when Member1 and Member2 are members of the lattice
%   loaded into the environment, and Distance is the distace between them.

lattice_call_distance(Member1, Member2, Distance) :-
    current_predicate(distance/3),
    !,
    lattice_call_member(Member1),
    lattice_call_member(Member2),
    fasill_term:to_prolog(Member1, Prolog1),
    fasill_term:to_prolog(Member2, Prolog2),
    distance(Prolog1, Prolog2, Prolog3),
    fasill_term:from_prolog(Prolog3, Distance).
lattice_call_distance(_, _, _) :-
    fasill_exceptions:existence_error(procedure, distance/3, lattice/0, Error),
    fasill_exceptions:throw_exception(Error).

%!  lattice_call_connective(+Name, +Arguments, ?Result)
%
%   This predicate succeeds when Result is the result of evaluate the
%   connective Name with the arguments Arguments of the lattice loaded into the
%   environment.

lattice_call_connective('&', Args, Result) :-
    !,
    lattice_tnorm(Name),
    lattice_call_connective('&'(Name), Args, Result).
lattice_call_connective('|', Args, Result) :-
    !,
    lattice_tconorm(Name),
    lattice_call_connective('|'(Name), Args, Result).
lattice_call_connective(Op, Args, Result) :-
    Op =.. [Type,Name],
    !,
    (   Type = '&', Pre = 'and_' ;
        Type = '|', Pre = 'or_' ;
        Type = '@', Pre = 'agr_'
    ),
    atom_concat(Pre, Name, Name_),
    lattice_call_connective2(Name_, Args, Result).
lattice_call_connective(Op, Args, Result) :-
    lattice_call_connective2(Op, Args, Result).
lattice_call_connective2(Name, Args, Result) :-
    length(Args, Arity),
    Arity_ is Arity + 1,
    (current_predicate(Name/Arity_) ->
        true ;
        fasill_exceptions:existence_error(procedure, Name/Arity_, lattice/0, Error),
        fasill_exceptions:throw_exception(Error)),
    fasill_term:maplist(to_prolog, Args, Args_),
    append(Args_, [Prolog], ArgsCall),
    Call =.. [Name|ArgsCall],
    fasill_environment:call(Call),
    fasill_term:from_prolog(Prolog, Result),
    !.

%!  lattice_reduce_connective(+Name, +TDs, ?Result)
%
%   This predicate succeeds when Result is the resulting value of reducing a
%   list of truth degrees TDs applying the connective Name loaded in the
%   lattice in the current environment.

lattice_reduce_connective(_, [X], X) :-
    !.
lattice_reduce_connective(Op, [H|T], Result) :-
    !,
    lattice_reduce_connective(Op, T, Result_),
    lattice_call_connective(Op, [H,Result_], Result).
lattice_reduce_connective(_, [], Bot) :-
    lattice_call_bot(Bot).

%!  lattice_consult(+Path)
%
%   This predicate loads the lattice of the file Path into the environment.
%   This predicate cleans the previous lattice.

lattice_consult(Path) :-
    abolish(member/1),
    abolish(members/1),
    abolish(distance/3),
    abolish(bot/1),
    abolish(top/1),
    abolish(leq/2),
    abolish(tnorm/1),
    abolish(tconorm/1),
    abolish(exclude/1),
    retractall(current_lattice_top(_)),
    retractall(current_lattice_bot(_)),
    ( current_predicate(X/3),
        ( atom_concat(and_, _, X) ;
        atom_concat(agr_, _, X) ;
        atom_concat(or_, _, X) ),
        abolish(X/3), fail ; true
    ),
    consult(Path).

% SIMILARITY RELATIONS

%!  similarity_tnorm(?Tnorm)
%
%   This predicate succeeds when Tnorm is the current t-norm asserted in the
%   environment.

similarity_tnorm(Tnorm) :-
    fasill_similarity_tnorm(Tnorm), !.
similarity_tnorm('&'(Tnorm)) :-
    lattice_tnorm(Tnorm).

%!  similarity_tconorm(?Tconorm)
%
%   This predicate succeeds when Tconorm is the current t-conorm asserted in 
%   the environment.

similarity_tconorm(Tconorm) :-
    fasill_similarity_tconorm(Tconorm), !.
similarity_tconorm('|'(Tconorm)) :-
    lattice_tconorm(Tconorm).

%!  similarity_between(?AtomA, ?AtomB, ?Arity, ?TD, ?Sym)
%
%   This predicate succeeds when AtomA/Arity is similar to AtomB/Arity with
%   truth degree TD, using the current similarity relation in the environment.

similarity_between(AtomA, AtomB, Arity, TD, Sym) :-
    fasill_similarity(AtomA/Arity, AtomB/Arity, TD, Sym).
similarity_between(AtomA, AtomB, Arity, Bot, no) :-
    \+fasill_similarity(AtomA/Arity, AtomB/Arity, _, _),
    lattice_call_bot(Bot).

%!  similarity_retract
%
%   This predicate succeeds and retracts all the clauses of similarity from the
%   current environment.

similarity_retract :-
    retractall(fasill_similarity(_, _, _, _)),
    retractall(fasill_similarity_tnorm(_)),
    retractall(fasill_similarity_tconorm(_)).

%!  similarity_consult(+Path)
%
%   This predicate loads the similarities equations of the file Path into the
%   environment. This predicate cleans the previous similarity relations.

similarity_consult(Path) :-
    similarity_retract,
    fasill_parser:file_similarity(Path, Equations),
    (   member(Eq, Equations),
        assertz(Eq),
        fail ; true),
    similarity_closure.

%!  similarity_closure
%
%   This predicate computes the reflexive, symmetric and  transitive closure of
%   the similarity scheme asserted into the current environment.

similarity_closure :-
    setof(Atom/Arity, Atom2^TD^Sym^(
        similarity_between(Atom, Atom2, Arity, TD, Sym);
        similarity_between(Atom2, Atom, Arity, TD, Sym)
    ), Dom),
    findall(sim(Atom1,Atom2,Arity,TD,Sym), similarity_between(Atom1,Atom2,Arity,TD,Sym), Scheme),
    similarity_tnorm(Tnorm),
    lattice_call_bot(Bot),
    lattice_call_top(Top),
    similarity_retract,
    (similarity_closure_check_equations(Dom, Scheme), false ; true),
    (similarity_closure_reflexive(Dom, Scheme, Tnorm, Bot, Top), false ; true),
    (similarity_closure_symmetric(Dom, Scheme, Tnorm, Bot, Top), false ; true),
    (similarity_closure_transitive(Dom, Scheme, Tnorm, Bot, Top), false ; true),
    assertz(fasill_similarity_tnorm(Tnorm)).

similarity_closure_check_equations(Dom, Scheme) :-
    member(X/Arity, Dom),
    member(Y/Arity, Dom),
    X @< Y,
    setof(TD, Sym^(
        member(sim(X,Y,Arity,TD,Sym), Scheme);
        member(sim(Y,X,Arity,TD,Sym), Scheme)
    ), Set),
    length(Set, Length),
    from_prolog_list(Set, FSet),
    (Length > 1 ->
        fasill_exceptions:throw_warning(term(warning, [term(conflicting_equations, [term('/', [term(X, []), num(Arity)]), term('/', [term(Y, []), num(Arity)]), FSet])]))).

similarity_closure_reflexive(Dom, _, _, _, Top) :-
    member(X/Arity, Dom),
    assertz(fasill_similarity(X/Arity,X/Arity,Top,no)).

similarity_closure_symmetric(Dom, Scheme, _, _, _) :-
    member(X/Arity, Dom),
    member(Y/Arity, Dom),
    \+(fasill_similarity(X/Arity,Y/Arity,_,_)),
    once(member(sim(X,Y,Arity,TD,Sym), Scheme) ; member(sim(Y,X,Arity,TD,Sym), Scheme)),
    assertz(fasill_similarity(X/Arity,Y/Arity,TD,Sym)),
    assertz(fasill_similarity(Y/Arity,X/Arity,TD,Sym)).

similarity_closure_transitive(Dom, _, Tnorm, Bot, Top) :-
    member(Y/Arity, Dom),
    member(X/Arity, Dom), X \= Y,
    member(Z/Arity, Dom), Z \= Y, X \= Z,
    once(fasill_similarity(X/Arity,Z/Arity,TDxz,Sxz) ; (TDxz = Bot, Sxz = no)),
    once(fasill_similarity(X/Arity,Y/Arity,TDxy,Sxy)),
    once(fasill_similarity(Y/Arity,Z/Arity,TDyz,Syz)),
    (TDxy == Top -> TDy = TDyz, Sy = Syz ;
        (TDyz == Top -> TDy = TDxy, Sy = Sxy ;
            ((Sxy == no, Syz == no, Tnorm = '&'(_)) ->
                (lattice_call_connective(Tnorm, [TDxy,TDyz], TDy), Sy = no) ;
                (TDy = term(Tnorm, [TDxy, TDyz]), Sy = yes)
            )
        )
    ),
    (TDxz == Bot -> TD = TDy, S = Sy ;
        (TDy == Bot -> TD = TDxz, S = Sxz ;
            ((Sxz == no, Sy == no, Tnorm = '&'(_)) ->
                (lattice_call_supremum(TDxz, TDy, TD), S = no) ;
                (TD = sup(TDxz, TDy), S = yes)
            )
        )
    ),
    retractall(fasill_similarity(X/Arity,Z/Arity,_,_)),
    assertz(fasill_similarity(X/Arity,Z/Arity,TD,S)).

% TEST CASES

%!  testcases_consult(+Path)
%
%   This predicate loads the set of FASILL test cases from the file Path into
%   the environment. This predicate cleans the previous test cases.

testcases_consult(Path) :-
    retractall(fasill_testcase(_,_)),
    retractall(fasill_testcase_precondition(_)),
    file_testcases(Path, Tests),
    ( member(Test, Tests),
        assertz(Test),
        fail ; true ).

% VARIABLES

%!  current_fresh_variable_id(?Identifier)
%
%   This predicate stores the current identifier Identifier to be used in a
%   fresh variable.
:- dynamic current_fresh_variable_id/1.
current_fresh_variable_id(0).

%!  fresh_variable(-Variable)
%
%   This predicate updates the current variable identifier and returns a fresh
%   variable Variable.

fresh_variable(var('$'(N))) :-
    current_fresh_variable_id(N),
    retract(current_fresh_variable_id(_)),
    succ(N, M),
    asserta(current_fresh_variable_id(M)).