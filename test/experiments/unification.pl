/**
  * 
  * FILENAME: test/experiments/unification.pl
  * DESCRIPTION: This file performs statistics of the different unification algorithms.
  * AUTHORS: José Antonio Riaza Valverde
  * UPDATED: 03.02.2020
  * 
  **/

:- use_module(library(random)).
:- use_module('../../src/semantics').



% TESTS

test_mgu(Symbols, Repeat, min(time(MinT), inferences(MinI)),
average(time(AverT), inferences(AverI)), max(time(MaxT), inferences(MaxI))) :-
    test_mgu(Symbols, Repeat, Times, Inferences),
    max_list(Times, MaxT), max_list(Inferences, MaxI),
    min_list(Times, MinT), min_list(Inferences, MinI),
    sum_list(Times, TotalT), sum_list(Inferences, TotalI),
    AverT is TotalT/Repeat, AverI is TotalI/Repeat.

test_mgu(_, 0, [], []) :- !.
test_mgu(Symbols, N, [T|Ts], [I|Is]) :-
    succ(M, N),
    arbitrary_fasill_term(Symbols, TermA),
    modify_fasill_term(TermA, TermB),
    statistics(runtime, [_,_]),
    statistics(inferences, I0),
    mgu(TermA, TermB, term(false, []), _),
    statistics(inferences, If),
    statistics(runtime, [_,T]),
    I is If-I0,
    test_mgu(Symbols, M, Ts, Is).



% GENERATION OF TERMS

:- dynamic(current_variable_id/1).
current_variable_id(0).

% arbitrary_fasill_atom/1
% arbitrary_fasill_atom(?Atom)
%
% This predicate returns an arbitrary FASILL atom ?Atom (from a to z).
arbitrary_fasill_atom(term(X, [])) :-
    random_member(X, [a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z]).

% arbitrary_fasill_var/1
% arbitrary_fasill_var(?Var)
%
% This predicate returns an arbitrary (fresh) FASILL variable ?Var.
arbitrary_fasill_var(var(X)) :-
    current_variable_id(N),
    retract(current_variable_id(N)),
    succ(N, M),
    asserta(current_variable_id(M)),
    atom_number(A, N),
    atom_concat('Var', A, X).

% arbitrary_fasill_term/2
% arbitrary_fasill_term(+Symbols, ?Term)
%
% This predicate returns an arbitrary FASILL term ?Term with +Symbols symbols.
arbitrary_fasill_term(1, X) :- maybe, arbitrary_fasill_var(X), !.
arbitrary_fasill_term(1, X) :- arbitrary_fasill_atom(X), !.
arbitrary_fasill_term(N, term(Functor, Args)) :-
    N > 1,
    succ(M, N),
    P is ceil(M/2),
    random_between(1, P, Arity),
    Max is floor(P/Arity),
    arbitrary_fasill_atom(term(Functor, [])),
    arbitrary_fasill_term(Max, M, Arity, Args).

% arbitrary_fasill_term/4
% arbitrary_fasill_term(+Max, +Symbols, +Samples, ?Terms)
%
% This predicate returns a list ?Terms containing +Samples arbitrary FASILL terms
% with at most +Max symbols per term, being +Symbols the total number of symbols
% among all the generated terms.
arbitrary_fasill_term(_, _, 0, []) :- !.
arbitrary_fasill_term(_, Left, 1, [Term]) :- !,
    arbitrary_fasill_term(Left, Term).
arbitrary_fasill_term(Max, Left, N, [Term|Terms]) :-
    succ(M, N),
    random_between(1, Max, Symbols),
    Left2 is Left-Symbols,
    arbitrary_fasill_term(Symbols, Term),
    arbitrary_fasill_term(Max, Left2, M, Terms).

% modify_fasill_term/2
% modify_fasill_term(+TermIn, ?TermOut)
%
% This predicate succeeds when ?TermIn is a term that subsumes to ?TermOut.
modify_fasill_term(var(_), T) :- arbitrary_fasill_term(1, T).
modify_fasill_term(term(X, Xs), term(X, Ys)) :- maplist(modify_fasill_term, Xs, Ys).