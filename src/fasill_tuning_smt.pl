/*  Part of FASILL

    Author:        José Antonio Riaza Valverde
    E-mail:        riaza.valverde@gmail.com
    WWW:           https://dectau.uclm.es/fasill
    Copyright (c)  2018 - 2022, José Antonio Riaza Valverde
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

:- module(fasill_tuning_smt, [
    tuning_smt/4
]).

:- use_module(library(smtlib)).
:- use_module(fasill_tuning).
:- use_module(fasill_environment).
:- use_module(fasill_inference).
:- use_module(fasill_term).

/** <module> Tuning with SAT/SMT solvers
    This library provides predicates for tuning FASILL programs using SAT/SMT
    solvers.

    In order to increase the performance of the original tuning techniques, we
    make use of the powerful and well-known SAT/SMT solver Z3:

    1. Firstly, the lattice of truth degrees of the FASILL program to be tuned
       is translated to Z3 syntax.

    2. Next, the set of sfca's obtained after partially evaluating the test
       cases introduced a priori by the user are also automatically coded as a
       Z3 formula.

    3. Finally, the Z3 solver is launched in order to minimize the deviation of
       the solutions w.r.t. the set of test cases while checking the
       satisfiability of such formula.

    For more details see:

    * Riaza, José A., and Ginés Moreno. "Using SAT/SMT solvers for efficiently
      tuning fuzzy logic programs." 2020 IEEE International Conference on Fuzzy
      Systems (FUZZ-IEEE). IEEE, 2020.
      [https://doi.org/10.1109/FUZZ48607.2020.9177798](https://doi.org/10.1109/FUZZ48607.2020.9177798)
*/

%!  tuning_smt(+Domain, +LatFile, ?Substitution, ?Deviation)
%
%   This predicate succeeds when Substitution is the best symbolic substitution
%   for the set of test cases loaded into the current environment, with
%   deviation Deviation. LatFile is an SMT-LIB script representing the
%   corresponding Prolog lattice.

tuning_smt(Domain, LatFile, Substitution, Deviation) :-
    smtlib_read_script(LatFile, list(Lattice)),
    tuning_smt_sfcas(ListOfSFCA),
    fasill_findall_symbolic_cons(ListOfSFCA, ListCons),
    list_to_set(ListCons, Cons),
    tuning_smt_decl_const(Domain, Cons, Declarations),
    (member([reserved('define-fun'), symbol('lat!member')|_], Lattice) ->
        tuning_smt_members(Cons, Members);
        Members = []),
    tuning_smt_preconditions(Pre),
    tuning_smt_minimize(ListOfSFCA, Minimize),
    tuning_theory_options(Domain, TheoryOpts),
    GetModel = [[reserved('check-sat')], [reserved('get-model')]],
    append([Lattice, Declarations, Members, Pre, Minimize, TheoryOpts, GetModel], Script),
    smtlib_write_to_file('.tuning.smt2', list(Script)),
    shell('z3 -smt2 .tuning.smt2 > .result.tuning.smt2', _),
    smtlib_read_expressions('.result.tuning.smt2', Z3answer),
    tuning_smt_answer(Z3answer, Substitution, Deviation).

%!  tuning_smt_answer(+Z3answer, ?Substitution, ?Deviation)
%
%   This predicate succeeds when Z3answer is the answer of the Z3 solver and
%   Substitution is the best symbolic substitution of the tuning process with
%   deviation Deviation.

tuning_smt_answer([H|_], Substitution, Deviation) :-
    member([reserved('define-fun'), symbol('deviation!'), [], symbol('Real'), decimal(Deviation)|_], H), !,
    findall(sym(Con,Name,Arity_)/val(Con,Y,Arity_), (
        member([reserved('define-fun'), symbol(Symbol), [], symbol(_), Value|_], H),
        atomic_list_concat(['sym', Con, Arity, Name], '!', Symbol),
        atom_number(Arity, Arity_),
        Value =.. [_,X],
        (Con = td ->
            fasill_term:from_prolog(X, Y) ;
            (atomic_list_concat([_|X2], '_', X), atomic_list_concat(X2, '_', Y))
        )
    ), Substitution).
tuning_smt_answer([_|T], Substitution, Deviation) :-
    tuning_smt_answer(T, Substitution, Deviation).

%!  tuning_smt_decl_const(+Domain, +FASILL, ?SMTLIB)
%
%   This predicate succeeds when FASILL is a list of symbolic FASILL constants
%   and SMTLIB is a list of declarations of that constants in SMT-LIB.

tuning_smt_decl_const(_, [], [[reserved('declare-const'), symbol('deviation!'), symbol('Real')]]) :- !.
tuning_smt_decl_const(Domain, [X|Xs], [Y|Ys]) :-
    !,
    tuning_smt_decl_const(Domain, X, Y),
    tuning_smt_decl_const(Domain, Xs, Ys).
tuning_smt_decl_const(Domain, sym(td,Name,0), [reserved('declare-const'), symbol(Sym), symbol(Domain)]) :- !,
    atom_concat('sym!td!0!', Name, Sym).
tuning_smt_decl_const(_, sym(Type,Name,Arity), [reserved('declare-const'), symbol(Sym), symbol('String')]) :- !,
    atom_number(Arity_, Arity),
    atom_concat('sym!', Type, LatType),
    atom_concat(LatType, '!', LatType_),
    atom_concat(LatType_, Arity_, LatTypeArity),
    atom_concat(LatTypeArity, '!', LatTypeArity_),  
    atom_concat(LatTypeArity_, Name, Sym).

%!  tuning_smt_members(+Constants, ?Members)
%
%   This predicate succeeds when Constants is a list of symbolic FASILL
%   constants and Members is a list of membering assertions of that constants
%   in SMT-LIB.

tuning_smt_members([], []) :-
    !.
tuning_smt_members([sym(td,Name,0)|Cons], [[reserved('assert'), [symbol('lat!member'), symbol(Sym)]]|Members]) :-
    !,
    atom_concat('sym!td!0!', Name, Sym),
    tuning_smt_members(Cons, Members).
tuning_smt_members([sym(Type,Name,Arity)|Cons], [[reserved('assert'), [symbol(Dom), symbol(Sym)]]|Members]) :-
    !,
    atom_concat('sym!', Type, SymType),
    atom_concat(SymType, '!', SymType_),
    atom_number(Arity_, Arity),
    atom_concat(SymType_, Arity_, SymTypeArity),
    atom_concat('dom!', SymTypeArity, Dom),
    atom_concat(SymTypeArity, '!', SymTypeArity_),
    atom_concat(SymTypeArity_, Name, Sym),
    tuning_smt_members(Cons, Members).

%!  tuning_smt_sfcas(?ListOfSFCA)
%
%   This predicate succeeds when ListOfSFCA is the list of symbolic fuzzy 
%   computed answers.

tuning_smt_sfcas(ListOfSFCA) :-
    findall((SFCA,TD), (
        fasill_testcase(TD, Goal),
        ( query(Goal, state(SFCA, _)) ->
          true
        ; fasill_environment:lattice_call_bot(SFCA))
    ), ListOfSFCA).

%!  tuning_smt_preconditions(?Preconditions)
%
%   This predicate succeeds when Preconditions is the list of asserts to check
%   the preconditions of the current tuning problem.

tuning_smt_preconditions(Pre) :-
    fasill_environment:lattice_call_bot(Bot),
    sfca_to_smtlib(Bot, BotSMT),
    findall(Assert,
      ( fasill_environment:similarity_between(_, _, _, TD, yes),
        sfca_to_smtlib(TD, TDSMT),
        Assert = [symbol(assert), [symbol(not), [symbol('lat!leq'), [TDSMT, BotSMT]]]]
      ),
    Pre).

%!  tuning_smt(+ListOfSFCA, ?Minimize)
%
%   This predicate succeeds when Minimize is the command to minimize the set of
%   tests cases w.r.t. the expected truth degrees.

tuning_smt_minimize(ListOfSFCA, [Assert, Minimize]) :-
    findall([symbol('lat!distance'), TD_, SMT], (
        member((SFCA,TD), ListOfSFCA),
        sfca_to_smtlib(TD, TD_),
        sfca_to_smtlib(SFCA, SMT)
    ), Distances),
    Assert = [reserved(assert), [symbol(=), symbol('deviation!'), [symbol(+)|Distances]]],
    Minimize = [reserved(minimize), symbol('deviation!')].

%!  testcase_to_smtlib(+SFCA, ?SMTLIB)
%
%   This predicate succeeds when SFCA is a valid FASILL term representing a
%   symbolic fuzzy computed answer and SMTLIB is the corresponding answer in
%   SMT-LIB format.

sfca_to_smtlib(num(X), numeral(X)) :-
    integer(X),
    !.
sfca_to_smtlib(num(X), decimal(Y)) :-
    float(X),
    Y is ceil(X*100)/100,
    !.
sfca_to_smtlib(term('#'(X),[]), symbol(Y)) :-
    atom_concat('sym!td!0!', X, Y),
    !.
sfca_to_smtlib(term(X,[]), symbol(X)) :-
    atomic(X),
    !.
sfca_to_smtlib(sup(X,Y), [symbol('lat!supremum'), Ex, Ey]) :-
    !,
    sfca_to_smtlib(X, Ex),
    sfca_to_smtlib(Y, Ey).
sfca_to_smtlib(term(X,Xs), [symbol(Con2),symbol(Name4)|Xs2]) :-
    X =.. [Op,Name],
    member((Op,Pre), [('#&','and!'), ('#|','or!'), ('#@','agr!')]),
    !,
    length(Xs, Length),
    atom_number(Atom, Length),
    atom_concat(Pre, Atom, Con),
    atom_concat('call!sym!', Con, Con2),
    atom_concat('sym!', Con, Name2),
    atom_concat(Name2, '!', Name3),
    atom_concat(Name3, Name, Name4),
    maplist(sfca_to_smtlib, Xs, Xs2).
sfca_to_smtlib(term(X,Xs), [symbol(Con)|Xs2]) :-
    ( (X = '&', Op = '&', lattice_tnorm('&'(Name))) ;
        (X = '|', Op = '|', lattice_tconorm('|'(Name))) ;
        X =.. [Op,Name] ),
    !,
    member((Op,Pre), [
        ('&','lat!and!'), ('|','lat!or!'), ('@','lat!agr!'), ('#','sym!td!')
    ]),
    !,
    atom_concat(Pre, Name, Fun),
    length(Xs, Length),
    atom_number(Atom, Length),
    atom_concat(Fun, '!', Fun_),
    atom_concat(Fun_, Atom, Con),
    maplist(sfca_to_smtlib, Xs, Xs2).
sfca_to_smtlib(term(X,[]), symbol(X)).

%!  tuning_theory_options(+Theory, -Options)
%
%   This predicate succeeds when Options is a list of options in SMT-LIB format
%   for the theory Theroy.

tuning_theory_options('Bool', []).
tuning_theory_options('Real', [[reserved('set-option'), keyword('pp.decimal'), symbol(true)]]).