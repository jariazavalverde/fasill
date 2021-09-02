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

:- module(fasill_tuning, [
    findall_symbolic_cons/1,
    tuning_thresholded/2,
    tuning_thresholded/3,
    fasill_print_symbolic_substitution/1
]).

:- use_module(library(union_find_assoc)).
:- use_module(fasill_environment).
:- use_module(fasill_inference).
:- use_module(fasill_term).

/** <module> Tuning
    This library provides predicates for tuning FASILL programs.
    
    Typically, a programmer has a model in mind where some parameters have a
    clear value. For instance, the truth value of a rule might be statistically
    determined and, thus, its value is easy to obtain. In other cases, though,
    the most appropriate values and/or connectives depend on subjective notions
    and, thus, programmers do not know how to obtain these values. In a typical
    scenario, we have an extensive set of expected computed answers (i.e., test
    cases), so the programmer can follow a "try and test" strategy.
    Unfortunately, this is a tedious and time consuming operation. Actually, it
    might even be impractical when the program should correctly model a large
    number of test cases.

    For tuning a symbolic program, we don't follow an inefficient, basic method
    based on applying each symbolic substitution to the original symbolic
    program and then fully executing the resulting instantiated FASILL programs.
    Instead of it, we have implemented a thresholded symbolic strategy where
    symbolic substitutions are directly applied to sfca's (thus, only the
    interpretive stage is repeatedly executed) and many useless computations are
    prematurely disregarded by appropriately using dynamic thresholds.
*/

% DYNAMIC

%!  tuning_best_substitution(?Substitution, ?Deviation)
%
%   This predicate succeeds when Substitution is the best substitution found so
%   far and Deviation is the deviation with respect to the set of test cases.

:- dynamic
    tuning_best_substitution/2.

% UTILS

%!  findall_symbolic_cons(?Symbols)
%
%   This predicate succeeds when Symbols is the set of symbolic constants
%   contained in the FASILL rules asserted in the current environment.

findall_symbolic_cons(Set) :-
    findall([Head|BodyT], (
        fasill_rule(head(Head), Body_, _),
        (Body_ = body(Body) -> BodyT = [Body] ; BodyT = [])
    ), Rules),
    findall(Test, fasill_testcase(_, Test), Tests),
    append(Rules, Tests, Search),
    findall_symbolic_cons(Search, Symbols),
    list_to_set(Symbols, Set).

%!  findall_symbolic_cons(+Expression, ?Symbols)
%
%   This predicate succeeds when Symbols is the set of symbolic constants
%   contained in Expression.

findall_symbolic_cons([], []) :-
    !.
findall_symbolic_cons([H|T], Sym) :-
    !,
    findall_symbolic_cons(H, SymH),
    findall_symbolic_cons(T, SymT),
    append(SymH, SymT, Sym).
findall_symbolic_cons(sup(X, Y), Sym) :-
    !,
    findall_symbolic_cons(X, SymX),
    findall_symbolic_cons(Y, SymY),
    append(SymX, SymY, Sym).
findall_symbolic_cons(term('#'(Name),[]), [sym(td, Name, 0)]) :-
    !.
findall_symbolic_cons(term(Term, Args), [sym(Type, Name, Arity)|Sym]) :-
    Term =.. [Op,Name],
    member((Op,Type), [('#&',and),('#|',or),('#/',or),('#@',agr),('#?',con)]),
    !,
    length(Args, Arity),
    findall_symbolic_cons(Args, Sym).
findall_symbolic_cons(term(_, Args), Sym) :-
    !,
    findall_symbolic_cons(Args, Sym).
findall_symbolic_cons(_, []).

%!  symbolic_substitution(+Symbols, -Substitution)
%
%   This predicate succeeds when Symbols is a set of symbolic constants and
%   Substitution is a possible symbolic substitution for constants Symbols.
%   This predicate can be used for generating, by reevaluation, all possible
%   symbolic substitutions for the constants.

symbolic_substitution([], []).
symbolic_substitution([ground|T], T_) :-
    symbolic_substitution(T, T_).
symbolic_substitution([H|T], [H/H_|T_]) :-
    H \== ground,
    symbolic_substitution(H, H_),
    symbolic_substitution(T, T_).
symbolic_substitution(sym(td,Sym,0), val(td,Value,0)) :-
    fasill_environment:lattice_call_members(Sym, Members),
    member(Value, Members).
symbolic_substitution(sym(Type,_,Arity), val(Ty,Name,Arity)) :-
    Arity > 0,
    Arity_ is Arity + 1,
    (Type == con -> (Ty = and ; Ty = or ; Ty = agr) ; Ty = Type),
    atom_concat(Ty, '_', Type_),
    fasill_environment:current_predicate(Predicate/Arity_),
    atom_concat(Type_, Name, Predicate),
    \+fasill_environment:lattice_call_exclude(Predicate/Arity_).

%!  apply_symbolic_substitution(+ExpressionIn, +Substitution, -ExpressionOut)
%
%   This predicate succeeds when ExpressionOut is the resulting expression
%   after applying the symbolic substitution Substitution to the expression
%   ExpressionIn.

apply_symbolic_substitution(term('#'(Name),[]), Subs, Value) :-
    member(sym(td,Name,0)/val(td,Value,0), Subs),
    !.
apply_symbolic_substitution(term(Term,Args), Subs, term(Term2,Args_)) :-
    Term =.. [Op, Name],
    length(Args, Length),
    member((Op,Type), [('#&',and),('#|',or),('#/',or),('#@',agr),('#?',con)]),
    member(sym(Type,Name,Length)/val(Type2,Value,Length), Subs),
    member((Op2,Type2), [('&',and),('|',or),('@',agr)]),
    Term2 =.. [Op2, Value],
    apply_symbolic_substitution(Args, Subs, Args_),
    !.
apply_symbolic_substitution(term(Name,Args), Subs, term(Name,Args_)) :-
    apply_symbolic_substitution(Args, Subs, Args_),
    !.
apply_symbolic_substitution(sup(X, Y), Subs, sup(X_, Y_)) :-
    apply_symbolic_substitution(X, Subs, X_),
    apply_symbolic_substitution(Y, Subs, Y_),
    !.
apply_symbolic_substitution([H|T], Subs, [H_|T_]) :-
    apply_symbolic_substitution(H, Subs, H_),
    apply_symbolic_substitution(T, Subs, T_),
    !.
apply_symbolic_substitution(X, _, X).

%!  tuning_check_preconditions(+Preconditions, +Substitution)
%
%   This predicate succeeds when the lists of goals Preconditions is satisfied
%   for the symbolic substitution Substitution.

tuning_check_preconditions([], _).
tuning_check_preconditions([precondition(GoalS)|Preconditions], Subs) :-
    apply_symbolic_substitution(GoalS, Subs, Goal),
    fasill_inference:query(Goal, state(FCA, _)),
    fasill_environment:lattice_call_bot(Bot),
    \+fasill_environment:lattice_call_leq(FCA, Bot),
    tuning_check_preconditions(Preconditions, Subs).

%!  testcases_disjoint_sets(?Sets)
%
%   This predicate succeeds when ?Sets is the list of disjoint sets of test
%   cases loaded into the current environment, in form of pairs Symbols-SFCAs.

testcases_disjoint_sets(Sets, SetsCond) :-
    findall(S-testcase(TD, SFCA), (
        fasill_environment:fasill_testcase(TD, Goal),
        (fasill_inference:query(Goal, state(SFCA, _)) ->
            findall_symbolic_cons(SFCA, Symbols),
            (Symbols \== [] -> S = Symbols ; S = [ground] )
        )
    ), Tests),
    findall(S-precondition(X), (fasill_environment:fasill_testcase_precondition(X), findall_symbolic_cons(X, S)), PreconditionsUser),
    findall(S-precondition(TD), (fasill_environment:similarity_between(_, _, _, TD, yes), findall_symbolic_cons(TD, S)), PreconditionsSym),
    append(PreconditionsUser, PreconditionsSym, Preconditions),
    findall(Symbols, member(Symbols-_, Tests), ListSymbolsTests),
    findall(Symbols, member(Symbols-_, Preconditions), ListSymbolsCond),
    append(ListSymbolsTests, Symbols0),
    append(ListSymbolsCond, Symbols1),
    append(Symbols0, Symbols1, Symbols),
    union_find_assoc(UF0, Symbols),
    testcases_join_symbols(UF0, ListSymbolsTests, UF1),
    testcases_join_symbols(UF1, ListSymbolsCond, UF2),
    disjoint_sets_assoc(UF2, SymSets),
    findall(Set-[], member(Set, SymSets), Sets0),
    zip_symbols_testcases(Sets0, Tests, Sets),
    zip_symbols_testcases(Sets0, Preconditions, SetsCond).

%!  testcases_join_symbols(+UnionFindIn, +ListSymbols, ?UnionFindOut)
%
%   This predicate succeeds when ?UnionFindOut is the resulting union-find
%   structure of join all the sets in the list of symbols ListSymbols, starting
%   with the union-find structure UnionFindIn.

testcases_join_symbols(UF, [], UF).
testcases_join_symbols(UF0, [X|Xs], UF2) :-
    union_all_assoc(UF0, X, UF1),
    testcases_join_symbols(UF1, Xs, UF2).

%!  zip_symbols_testcases(+ItemsBySymbolsIn, +ItemsBySymbols, ?ItemsBySymbolsOut)
%
%   This predicate adds the items of the list ItemsBySymbols to the
%   ItemsBySymbolsIn list, producing the ItemsBySymbolsOut list. Items are pairs
%   of the form Symbols-Object, and are classified by Symbols.

zip_symbols_testcases(SymSets, [], SymSets).
zip_symbols_testcases(SymSets0, [Test|Tests], SymSets2) :-
    add_symbols_testcase(SymSets0, Test, SymSets1),
    zip_symbols_testcases(SymSets1, Tests, SymSets2).

%!  add_symbols_testcase(+ItemsBySymbolsIn, +ItemBySymbols, ?ItemsBySymbolsOut)
%
%   This predicate adds the item ItemBySymbols to the ItemsBySymbolsIn list,
%   producing the ItemsBySymbolsOut list. Item is a pair of the form
%   Symbols-Object, and is classified by Symbols.

add_symbols_testcase([Set-Tests|Sets], Symbols-Test, [Set-[Test|Tests]|Sets]) :-
    subset(Symbols, Set),
    !.
add_symbols_testcase([Set|Sets0], Test, [Set|Sets1]) :-
    add_symbols_testcase(Sets0, Test, Sets1).

% TUNING THRESHOLDED TECHNIQUE

%!  tuning_thresholded(?Substitution, ?Deviation)
%
%   This predicate succeeds when Substitution is the best symbolic substitution
%   for the set of test cases loaded into the current environment, with
%   deviation Deviation.

tuning_thresholded(Substitution, Deviation) :-
    tuning_thresholded(0.0, Substitution, Deviation).

%!  tuning_thresholded(+Cut, ?Substitution, ?Deviation)
%
%   This predicate succeeds when Substitution is the a symbolic substitution
%   for the set of test cases loaded into the current environment, with
%   deviation Deviation less than or equal to Cut. If Cut is set to 0.0,
%   Substitution is the best symbolic substitution.

tuning_thresholded(Cut, Substitution, Deviation) :-
    testcases_disjoint_sets(Tests, Preconditions),
    tuning_thresholded(Cut, Tests, Preconditions, Substitutions, _, 0.0, Deviation),
    append(Substitutions, Substitution).

%!  tuning_thresholded(+Cut, +Tests, +Preconditions, -Substitutions, -Deviations, +Initial, -Cumulative)
%
%   This predicate succeeds when Substitutions is the list of best symbolic
%   substitutions for the sets of test cases Test, with deviations Deviations.

tuning_thresholded(_, [], [], [], [], E, E).
tuning_thresholded(Cut, [Sym-T], [_-P], [S], [D], E0, E1) :-
    Margin is Cut - E0,
    retractall(tuning_best_substitution(_,_)),
    ( symbolic_substitution(Sym, Sub),
        tuning_check_preconditions(P, Sub),
        tuning_thresholded_do(T, Sub, 0.0),
        tuning_best_substitution(S, D),
        (D =< Margin -> ! ; fail) ; true ),
    tuning_best_substitution(S, D),
    E1 is E0 + D.
tuning_thresholded(Cut, [Sym-T,T2|Ts], [_-P,P2|Ps], [S|Ss], [D|Ds], E0, E2) :-
    retractall(tuning_best_substitution(_,_)),
    ( symbolic_substitution(Sym, Sub),
        tuning_check_preconditions(P, Sub),
        tuning_thresholded_do(T, Sub, 0.0),
        fail ; true ),
    tuning_best_substitution(S, D),
    E1 is E0 + D,
    tuning_thresholded(Cut, [T2|Ts], [P2|Ps], Ss, Ds, E1, E2).

%!  tuning_thresholded_do(+Tests, +Substitution, ?Error)
%
%   This predicate succeeds when Substitution is the best symbolic substitution
%   for the set of test cases loaded into the current environment, with
%   deviation Deviation. Tests is the set of test cases with goal partially
%   executed.

tuning_thresholded_do([], Sub, Error) :- !,
    (tuning_best_substitution(_, Best) -> Best > Error ; true),
    retractall(tuning_best_substitution(_,_)),
    asserta(tuning_best_substitution(Sub, Error)).
tuning_thresholded_do([testcase(TD,SFCA)|Tests], Sub, Error) :-
    (tuning_best_substitution(_, Best) -> Best > Error ; true),
    apply_symbolic_substitution(SFCA, Sub, FCA),
    fasill_inference:query(FCA, state(TD_, _)),
    fasill_environment:lattice_call_distance(TD, TD_, num(Distance)),
    Error_ is Error + Distance,
    tuning_thresholded_do(Tests, Sub, Error_).

%!  fasill_print_symbolic_substitution(+Substitution)
% 
%   This predicate writes a FASILL symbolic substitution Substitution for the 
%   standard output.

% Identity symbolic substitution
fasill_print_symbolic_substitution([]) :-
    write('{}'),
    !.
% Non-empty symbolic substitution
fasill_print_symbolic_substitution([X|Xs]) :-
    write('{'),
    fasill_print_symbolic_binding(X),
    fasill_print_symbolic_bindings(Xs),
    write('}'),
    !.
% Binding
fasill_print_symbolic_binding(sym(Type1,Cons,Arity)/val(Type2,Name,Arity)) :-
    Types = [(td,''),(and,'&'),(or,'|'),(agr,'@'),(con,'?')],
    member((Type1,Op1), Types),
    member((Type2,Op2), Types),
    write('#'),
    write(Op1),
    write_term(Cons, [quoted(true)]),
    write('/'),
    write(Op2),
    (Type1 = td ->
        fasill_term:fasill_print_term(Name) ;
        write(Name)).
% Bindings
fasill_print_symbolic_bindings([]).
fasill_print_symbolic_bindings([X|Xs]) :-
    write(','),
    fasill_print_symbolic_binding(X),
    fasill_print_symbolic_bindings(Xs).