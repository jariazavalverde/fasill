/**
  * 
  * FILENAME: tuning.pl
  * DESCRIPTION: This module contains predicates for tuning symbolic FASILL programs.
  * AUTHORS: José Antonio Riaza Valverde
  * UPDATED: 02.12.2019
  * 
  **/



:- module(tuning, [
    findall_symbolic_cons/1,
    tuning_thresholded/2
]).

:- use_module('environment').
:- use_module('semantics').
:- use_module(library(union_find_assoc)).



% tuning_best_substitution/2
% tuning_best_substitution(?Substitution, ?Deviation)
%
% This predicate succeeds when ?Substitution is the best
% substitution found so far and ?Deviation is the deviation
% with respect to the set of test cases.
:- dynamic(tuning_best_substitution/2).



% UTILS

% findall_symbolic_cons/1
% findall_symbolic_cons(?Symbols)
%
% This predicate succeeds when ?Symbols is the set of symbolic
% constants contained in the FASILL rules asserted in the current
% environment.
findall_symbolic_cons(Set) :-
    findall([Head|BodyT], (
        fasill_rule(head(Head), Body_, _),
        (Body_ = body(Body) -> BodyT = [Body] ; BodyT = [])
    ), Rules),
    findall(Test, fasill_testcase(_, Test), Tests),
    append(Rules, Tests, Search),
    findall_symbolic_cons(Search, Symbols),
    list_to_set(Symbols, Set).

% findall_symbolic_cons/2
% findall_symbolic_cons(+Expression, ?Symbols)
%
% This predicate succeeds when ?Symbols is the set of symbolic
% constants contained in +Expression.
findall_symbolic_cons([], []) :- !.
findall_symbolic_cons([H|T], Sym) :- !,
    findall_symbolic_cons(H, SymH),
    findall_symbolic_cons(T, SymT),
    append(SymH, SymT, Sym).
findall_symbolic_cons(term('#'(Name),[]), [sym(td, Name, 0)]) :- !.
findall_symbolic_cons(term(Term, Args), [sym(Type, Name, Arity)|Sym]) :-
    Term =.. [Op,Name],
    member((Op,Type), [('#&',and),('#|',or),('#@',agr),('#?',con)]),
    !, length(Args, Arity),
    findall_symbolic_cons(Args, Sym).
findall_symbolic_cons(term(_, Args), Sym) :- !, findall_symbolic_cons(Args, Sym).
findall_symbolic_cons(_, []).

% symbolic_substitution/2
% symbolic_substitution(+Symbols, -Substitution)
%
% This predicate succeeds when +Symbols is a set of symbolic
% constants and -Substitution is a possible symbolic substitution
% for constants +Symbols. This predicate can be used for generating,
% by reevaluation, all possible symbolic substitutions for the constants.
symbolic_substitution([], []).
symbolic_substitution([ground|T], T_) :-
    symbolic_substitution(T, T_).
symbolic_substitution([H|T], [H/H_|T_]) :-
    H \== ground,
    symbolic_substitution(H, H_),
    symbolic_substitution(T, T_).
symbolic_substitution(sym(td,_,0), val(td,Value,0)) :-
    lattice_call_members(Members),
    member(Value, Members).
symbolic_substitution(sym(Type,_,Arity), val(Type,Name,Arity)) :-
    Arity > 0,
    Arity_ is Arity + 1,
    atom_concat(Type, '_', Type_),
    current_predicate(environment:Predicate/Arity_),
    atom_concat(Type_, Name, Predicate).

% apply_symbolic_substitution/3
% apply_symbolic_substitution(+ExpressionIn, +Substitution, -ExpressionOut)
%
% This predicate succeeds when +ExpressionOut is the resulting
% expression after applying the symbolic substitution +Substitution
% to the expression +ExpressionIn.
apply_symbolic_substitution(term('#'(Name),[]), Subs, Value) :-
    member(sym(td,Name,0)/val(td,Value,0), Subs), !.
apply_symbolic_substitution(term(Term,Args), Subs, term(Term2,Args_)) :-
    Term =.. [Op, Name],
    length(Args, Length),
    member((Op,Type), [('#&',and),('#|',or),('#@',agr),('#?',con)]),
    member(sym(Type,Name,Length)/val(Type2,Value,Length), Subs),
    member((Op2,Type2), [('&',and),('|',or),('@',agr)]),
    Term2 =.. [Op2, Value],
    apply_symbolic_substitution(Args, Subs, Args_), !.
apply_symbolic_substitution(term(Name,Args), Subs, term(Name,Args_)) :-
    apply_symbolic_substitution(Args, Subs, Args_), !.
apply_symbolic_substitution([H|T], Subs, [H_|T_]) :-
    apply_symbolic_substitution(H, Subs, H_),
    apply_symbolic_substitution(T, Subs, T_), !.
apply_symbolic_substitution(X, _, X).

% testcases_disjoint_sets/1
% testcases_disjoint_sets(?Sets)
%
% This predicate succeeds when ?Sets is the list of disjoint
% sets of test cases loaded into the current environment, in form
% of pairs Symbols-SFCAs.
testcases_disjoint_sets(Sets) :-
	findall(S-testcase(TD, SFCA), (
        fasill_testcase(TD, Goal),
        (query(Goal, state(SFCA, _)) ->
            findall_symbolic_cons(SFCA, Symbols),
            (Symbols \== [] -> S = Symbols ; S = [ground] )
        )
    ), Tests),
    %findall(precondition(X), fasill_testcase_precondition(X), Preconditions),
    findall(Symbols, member(Symbols-_, Tests), ListSymbols),
    append(ListSymbols, Symbols),
    union_find_assoc(UF0, Symbols),
    testcases_join_symbols(UF0, ListSymbols, UF1),
    disjoint_sets_assoc(UF1, SymSets),
    findall(Set-[], member(Set, SymSets), PSymSets),
    zip_symbols_testcases(PSymSets, Tests, Sets).

% testcases_join_symbols/3
% testcases_join_symbols(+UnionFindIn, +ListSymbols, ?UnionFindOut)
%
% This predicate succeeds when ?UnionFindOut is the resulting union-find structure
% of join all the sets in the list of symbols +ListSymbols, starting with the 
% union-find structure +UnionFindIn.
testcases_join_symbols(UF, [], UF).
testcases_join_symbols(UF0, [X|Xs], UF2) :-
    union_all_assoc(UF0, X, UF1),
    testcases_join_symbols(UF1, Xs, UF2).

% zip_symbols_testcases/3
% zip_symbols_testcases(+ItemsBySymbolsIn, +ItemsBySymbols, ?ItemsBySymbolsOut)
%
% This predicate adds the items of the list +ItemsBySymbols to the +ItemsBySymbolsIn
% list, producing the ?ItemsBySymbolsOut list. Items are pairs of the form Symbols-Object,
% and are classified by Symbols.
zip_symbols_testcases(SymSets, [], SymSets).
zip_symbols_testcases(SymSets0, [Test|Tests], SymSets2) :-
    add_symbols_testcase(SymSets0, Test, SymSets1),
    zip_symbols_testcases(SymSets1, Tests, SymSets2).

% add_symbols_testcase/3
% add_symbols_testcase(+ItemsBySymbolsIn, +ItemBySymbols, ?ItemsBySymbolsOut)
%
% This predicate adds the item +ItemBySymbols to the +ItemsBySymbolsIn list,
% producing the ?ItemsBySymbolsOut list. Item is a pair of the form Symbols-Object,
% and is classified by Symbols.
add_symbols_testcase([Set-Tests|Sets], Symbols-Test, [Set-[Test|Tests]|Sets]) :-
    subset(Symbols, Set), !.
add_symbols_testcase([Set|Sets0], Test, [Set|Sets1]) :-
    add_symbols_testcase(Sets0, Test, Sets1).



% TUNING THRESHOLDED TECHNIQUE

% tuning_thresholded/2
% tuning_thresholded(?Substitution, ?Deviation)
%
% This predicate succeeds when ?Substitution is the best
% symbolic substitution for the set of test cases loaded
% into the current environment, with deviation ?Deviation.
tuning_thresholded(Best, Deviation) :-
	testcases_disjoint_sets(Tests),
    tuning_thresholded(Tests, Bests, Deviations),
    append(Bests, Best),
    sum_list(Deviations, Deviation).


% tuning_thresholded/3
% tuning_thresholded(+TestSets, ?Substitutions, ?Deviations)
%
% This predicate succeeds when ?Substitutions is the list of best
% symbolic substitutions for the sets of tests cases +TestSets, with
% deviations ?Deviations.
tuning_thresholded([], [], []).
tuning_thresholded([Symbols-Test|Tests], [Best|Bests], [Deviation|Deviations]) :-
    retractall(tuning_best_substitution(_,_)),
    ( symbolic_substitution(Symbols, Subs),
	  tuning_thresholded_do(Test, Subs, 0.0),
      fail ; true ),
    tuning_best_substitution(Best, Deviation),
    tuning_thresholded(Tests, Bests, Deviations).


% tuning_thresholded_do/3
% tuning_thresholded_do(+Tests, +Substitution, ?Error)
%
% This predicate succeeds when ?Substitution is the best
% symbolic substitution for the set of test cases loaded
% into the current environment, with deviation ?Deviation.
% +Tests is the set of test cases with goal partially executed.
tuning_thresholded_do([], Subs, Error) :- !,
    (tuning_best_substitution(_, Best) -> Best > Error ; true),
	retractall(tuning_best_substitution(_,_)),
	asserta(tuning_best_substitution(Subs, Error)).
tuning_thresholded_do([testcase(TD,SFCA)|Tests], Subs, Error) :-
    (tuning_best_substitution(_, Best) -> Best > Error ; true),
    apply_symbolic_substitution(SFCA, Subs, FCA),
    query(FCA, state(TD_, _)),
	lattice_call_distance(TD, TD_, num(Distance)),
	Error_ is Error + Distance,
    tuning_thresholded_do(Tests, Subs, Error_).