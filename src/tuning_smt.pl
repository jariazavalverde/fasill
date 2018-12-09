/**
  * 
  * FILENAME: tuning_smt.pl
  * DESCRIPTION: This module contains predicates for tuning symbolic FASILL programs with the Z3 SMT solver.
  * AUTHORS: José Antonio Riaza Valverde
  * UPDATED: 09.12.2018
  * 
  **/



:- module(tuning_smt, [
    tuning_smt/3
]).

:- use_module(library(smtlib)).
:- use_module('tuning', [findall_symbolic_cons/1]).
:- use_module('environment').
:- use_module('semantics').



% tuning_smt/3
% tuning_smt(+Domain, ?Substitution, ?Deviation)
%
% This predicate succeeds when ?Substitution is the best
% symbolic substitution for the set of test cases loaded
% into the current environment, with deviation ?Deviation.
% +Domain is an SMT-LIB script representing the corresponding
% Prolog lattice.
tuning_smt(Domain, _, _) :-
    downcase_atom(Domain, DomName),
    (prolog_load_context(directory, Dir_) ; Dir_ = '.'), !,
    atom_concat(Dir_, '/../lattices/', Dir),
    atom_concat(Dir, DomName, DirName),
    atom_concat(DirName, '.lat.smt2', Path),
    smtlib_read_script(Path, list(Lattice)),
    findall_symbolic_cons(Cons),
    tuning_smt_decl_const(Domain, Cons, Declarations),
    (member([reserved('define-fun'), symbol('lat!member')|_], Lattice) ->
        tuning_smt_members(Cons, Members);
        Members = []),
    tuning_smt_minimize(Minimize),
    tuning_theory_options(Domain, TheoryOpts),
    GetModel = [[reserved('check-sat')], [reserved('get-model')]],
    append([Lattice, Declarations, Members, Minimize, TheoryOpts, GetModel], Script),
    smtlib_write_to_file('tuning.smt2', list(Script)),
    shell('z3 -smt2 tuning.smt2', _).

% tuning_smt_decl_const/2
% tuning_smt_decl_const(+Domain, +FASILL, ?SMTLIB)
%
% This predicate succeeds when +FASILL is a list
% of symbolic FASILL constants and ?SMTLIB is a
% list of declarations of that constants in SMT-LIB.
tuning_smt_decl_const(_, [], [[reserved('declare-const'), symbol('deviation!'), symbol('Real')]]) :- !.
tuning_smt_decl_const(Domain, [X|Xs], [Y|Ys]) :- !,
    tuning_smt_decl_const(Domain, X, Y),
    tuning_smt_decl_const(Domain, Xs, Ys).
tuning_smt_decl_const(Domain, sym(td,Name,0), [reserved('declare-const'), symbol(Sym), symbol(Domain)]) :- !,
    atom_concat('sym!td!0!', Name, Sym).
tuning_smt_decl_const(_, sym(Type,Name,Arity), [reserved('declare-const'), symbol(Sym), symbol('String')]) :- !,
    atom_number(Arity_, Arity),
    atom_concat('lat!', Type, LatType),
    atom_concat(LatType, Arity_, LatTypeArity),
    atom_concat(LatTypeArity, Name, Sym).

% tuning_smt_members/2
% tuning_smt_members(+Constants, ?Members)
%
% This predicate succeeds when +Constants is a list
% of symbolic FASILL constants and ?Members is a list
% of membering assertions of that constants in SMT-LIB.
tuning_smt_members([], []) :- !.
tuning_smt_members([sym(td,Name,0)|Cons], [[reserved('assert'), [symbol('lat!member'), symbol(Sym)]]|Members]) :- !,
    atom_concat('sym!td!0!', Name, Sym),
    tuning_smt_members(Cons, Members).
tuning_smt_members([_|Cons], Members) :- !,
    tuning_smt_members(Cons, Members).

% tuning_smt_minimize/1
% tuning_smt(?Minimize)
%
% This predicate succeeds when ?Minimize is the command
% to minimize the set of tests cases w.r.t. the expected
% truth degrees.
tuning_smt_minimize([Assert, Minimize]) :-
    findall([symbol('lat!distance'), TD_, SMT], (
        fasill_testcase(TD, Goal),
        query(Goal, state(SFCA,_)),
        sfca_to_smtlib(TD, TD_),
        sfca_to_smtlib(SFCA, SMT)
    ), Distances),
    Assert = [reserved(assert), [symbol(=), symbol('deviation!'), [symbol(+)|Distances]]],
    Minimize = [reserved(minimize), symbol('deviation!')].

% testcase_to_smtlib/2
% testcase_to_smtlib(+SFCA, ?SMTLIB)
%
% This predicate succeeds when +SFCA is a valid FASILL term
% representing a symbolic fuzzy computed answer and ?SMTLIB
% is the corresponding answer in SMT-LIB format.
sfca_to_smtlib(num(X), numeral(X)) :- number(X), !.
sfca_to_smtlib(num(X), decimal(X)) :- float(X), !.
sfca_to_smtlib(term('#'(X),[]), symbol(Y)) :- atom_concat('sym!td!0!', X, Y), !.
sfca_to_smtlib(term(X,[]), symbol(X)) :- atomic(X), !.
sfca_to_smtlib(term(X,Xs), [symbol(Con2),symbol(Name4)|Xs2]) :-
    X =.. [Op,Name],
    member((Op,Pre), [('#&','and!'), ('#|','or!'), ('#@','agr!')]), !,
    length(Xs, Length),
    atom_number(Atom, Length),
    atom_concat(Pre, Atom, Con),
    atom_concat('call!', Con, Con2),
    atom_concat('sym!', Con, Name2),
    atom_concat(Name2, '!', Name3),
    atom_concat(Name3, Name, Name4),
    maplist(sfca_to_smtlib, Xs, Xs2).
sfca_to_smtlib(term(X,Xs), [symbol(Con)|Xs2]) :-
    ( (X = '&', Op = '&', lattice_tnorm(Name)) ;
      (X = '|', Op = '|', lattice_tconorm(Name)) ;
       X =.. [Op,Name] ), !,
    member((Op,Pre), [
      ('&','lat!and!'), ('|','lat!or!'), ('@','lat!agr!'), ('#','sym!td!')
    ]), !,
    atom_concat(Pre, Name, Fun),
    length(Xs, Length),
    atom_number(Atom, Length),
    atom_concat(Fun, '!', Fun_),
    atom_concat(Fun_, Atom, Con),
    maplist(sfca_to_smtlib, Xs, Xs2).
sfca_to_smtlib(term(X,[]), symbol(X)).

% tuning_theory_options/2
% tuning_theory_options(+Theory, -Options)
%
% This predicate succeeds when -Options is a list of
% options in SMT-LIB format for the theory +Theroy.
tuning_theory_options('Bool', []).
tuning_theory_options('Real', [[reserved('set-option'), keyword('pp.decimal'), symbol(true)]]).