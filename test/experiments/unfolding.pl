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

:- use_module('../../src/fasill_term').
:- use_module('../../src/fasill_inference').
:- use_module('../../src/fasill_environment').
:- use_module('../../src/fasill_unfolding').

/** <test> Unfolding
    This library provides predicates for testing unfolding.
*/

%! test_unfolding(+Repeat, +Program, +Goal, ?Min, ?Aver, ?Max)
%
%  This predicate performs a test of the classic unfolding algorithm
%  Repeat times returning the minimum Min, average Aver and maximum Max
%  runtime and number of inferences. Program is a callable term that loads
%  the program to be unfolded. Goal is a callable term that generates the goal
%  to be tested.

test_unfolding(Repeat, Program, Unfold, Goal, Min, Aver, Max) :-
    call(Program),
    call(Unfold),
    call(Goal, G),
    test_unfolding_loop(Repeat, G, [], [], Times, Inferences),
    max_list(Times, MaxT),
    max_list(Inferences, MaxI),
    min_list(Times, MinT),
    min_list(Inferences, MinI),
    sum_list(Times, TotalT),
    sum_list(Inferences, TotalI),
    AverT is TotalT/Repeat,
    AverI is TotalI/Repeat,
    Min = min(time(MinT), inferences(MinI)),
    Aver = average(time(AverT), inferences(AverI)),
    Max = max(time(MaxT), inferences(MaxI)), !.

test_unfolding_loop(0, _, Ts, Is, Ts, Is) :- !.
test_unfolding_loop(N, G, Ts, Is, Times, Inferences) :- 
    succ(M, N),
    statistics(runtime, [_,_]),
    statistics(inferences, I0),
    forall(fasill_inference:query(G, A), A = state(_,_)),
    statistics(inferences, If),
    statistics(runtime, [_,T]),
    I is If-I0,
    (T >= 0 ->
        N_ = M, Ts_ = [T|Ts], Is_ = [I|Is] ;
        N_ = N, Ts_ = Ts, Is_ = Is),
    test_unfolding_loop(N_, G, Ts_, Is_, Times, Inferences).

program(Program, Sim) :-
    fasill_environment:lattice_consult('../../sample/lat/unit.lat.pl'),
    tmp_file(fpl, FileProgram),
    open(FileProgram, write, StreamProgram),
    write(StreamProgram, Program),
    close(StreamProgram),
    fasill_environment:program_consult(FileProgram),
    tmp_file(sim, FileSim),
    open(FileSim, write, StreamSim),
    write(StreamSim, Sim),
    close(StreamSim),
    fasill_environment:similarity_consult(FileSim).

%! tests for append/3
%
%  append([], X, X).
%  append([H|T], X, [H|S]) <- append(T, X, S).

program_append :-
    program('
        append([], X, X).
        append([H|T], X, [H|S]) <- append(T, X, S).
    ', '
        a/0 ~ b/0 = 0.5. ~tnorm = godel.
    ').

unfold_append(0).
unfold_append(N) :-
    succ(M, N),
    once(fasill_environment:fasill_rule(_, body(term(append, _)), [id(Id)|_])),
    fasill_unfolding:classic_unfold_by_id(Id),
    unfold_append(M).

% ?- append([a,...,a], [], [b,...,b]).
goal_append(N, Append) :-
    length(L1, N),
    length(L2, N),
    maplist(=(term(a, [])), L1),
    maplist(=(term(b, [])), L2),
    fasill_term:from_prolog(append(L1, [], L2), Append).

%! double_append
%
%  append([], X, X).
%  append([H|T], X, [H|S]) <- append(T, X, S).
%  double_append(X, Y, Z, W) <- append(X, Y, U) & append(U, Z, W).

program_double_append :-
    program('
        append([], X, X).
        append([H|T], X, [H|S]) <- append(T, X, S).
        double_append(X, Y, Z, W) <- append(X, Y, U) & append(U, Z, W).
    ', '
        a/0 ~ b/0 = 0.5. ~tnorm = godel.
    ').

unfold_double_append(0).
unfold_double_append(N) :-
    succ(M, N),
    once(fasill_environment:fasill_rule(_, body(term(append, _)), [id(Id)|_])),
    fasill_unfolding:classic_unfold_by_id(Id),
    unfold_append(M).

% ?- double_append([a,...,a], [a,...,a], [], [b,b,...,b,b]).
goal_double_append(N, DoubleAppend) :-
    N2 is N*2,
    length(L1, N),
    length(L2, N2),
    maplist(=(term(a, [])), L1),
    maplist(=(term(b, [])), L2),
    fasill_term:from_prolog(double_append(L1, L1, [], L2), DoubleAppend).

%! palindrome
%
%  reverse(Xs, Ys) <- reverse(Xs, [], Ys).
%  reverse([], Ys, Ys).
%  reverse([X|Xs], Ys, Zs) <- reverse(Xs, [X|Ys], Zs).
%  palindrome(Xs) <- reverse(Xs, Xs).

program_palindrome :-
    program('
        reverse(Xs, Ys) <- reverse(Xs, [], Ys).
        reverse([], Ys, Ys).
        reverse([X|Xs], Ys, Zs) <- reverse(Xs, [X|Ys], Zs).
        palindrome(Xs) <- reverse(Xs, Xs).
    ', '
        a/0 ~ b/0 = 0.5. ~tnorm = godel.
    ').

unfold_palindrome(0).
unfold_palindrome(N) :-
    succ(M, N),
    once(fasill_environment:fasill_rule(_, body(term(reverse, [_, term('.', _), _])), [id(Id)|_])),
    fasill_unfolding:classic_unfold_by_id(Id),
    unfold_palindrome(M).

% ?- palindorme([a,...,a,c,b,...,b]).
goal_palindrome(N, Palindrome) :-
    length(L1, N),
    length(L2, N),
    maplist(=(term(a, [])), L1),
    maplist(=(term(b, [])), L2),
    append(L1, [c|L2], L3),
    fasill_term:from_prolog(palindrome(L3), Palindrome).

%! flip
%
%  flip(tree(X,Xs), tree(X,Ys)) <- flip(Xs, [], Ys).
%  flip([], Ys, Ys).
%  flip([X|Xs], Ys, Zs) <- flip(X, Y) &godel flip(Xs, [Y|Ys], Zs).

program_flip :-
    program('
        flip(tree(X,Xs), tree(X,Ys)) <- flip(Xs, [], Ys).
        flip([], Ys, Ys).
        flip([X|Xs], Ys, Zs) <- flip(X, Y) & flip(Xs, [Y|Ys], Zs).
    ', '
        a/0 ~ b/0 = 0.5. ~tnorm = godel.
    ').

unfold_flip :-
    once(fasill_environment:fasill_rule(_, body(term(flip, _)), [id(Id)|_])),
    fasill_unfolding:classic_unfold_by_id(Id).

% ?- flip(tree(a, [...]), tree(b, [...])).
goal_flip(B, N, Flip) :-
    tree(a, B, N, T1),
    tree(b, B, N, T2),
    fasill_term:from_prolog(flip(T1, T2), Flip).

tree(X, _, 1, tree(X, [])).
tree(X, B, N, tree(X,L)) :-
    N > 1,
    succ(M, N),
    length(L, B),
    maplist(=(Xs), L),
    tree(X, B, M, Xs).

%! peano
%
%  add(z, N, N).
%  add(s(M), N, s(P)) <- add(M, N, P).
%  mul(z, _, z).
%  mul(s(M), N, Y) <- mul(M, N, X) & add(N, X, Y).

program_peano :-
    program('
        add(z, N, N).
        add(s(M), N, s(P)) <- add(M, N, P).
        mul(z, _, z).
        mul(s(M), N, Y) <- mul(M, N, X) & add(N, X, Y).
    ', '
        s/1 ~ p/1 = 1.0. ~tnorm = godel.
    ').

unfold_peano(0).
unfold_peano(N) :-
    succ(M, N),
    once(fasill_environment:fasill_rule(_, body(term(add, _)), [id(Id)|_])),
    fasill_unfolding:classic_unfold_by_id(Id),
    unfold_peano(M).

% ?- mul([p(p(...)), p(p(...)), p(p(...))]).
goal_peano(N, Peano) :-
    NN is N*N,
    peano(N, P),
    peano(NN, PP),
    fasill_term:from_prolog(mul(P, P, PP), Peano).

peano(0, z).
peano(N, p(P)) :- succ(M, N), peano(M, P).

%! fibonacci
%
%  add(z, N, N).
%  add(s(M), N, s(P)) <- add(M, N, P).
%  fibonacci(z, z).
%  fibonacci(s(z), s(z)).
%  fibonacci(s(s(N)), Z) <- fibonacci(N, X) & fibonacci(s(N), Y) & add(X, Y, Z).

program_fibonacci :-
    program('
        add(z, N, N).
        add(s(M), N, s(P)) <- add(M, N, P).
        fibonacci(z, z).
        fibonacci(s(z), s(z)).
        fibonacci(s(s(N)), Z) <- fibonacci(N, X) & fibonacci(s(N), Y) & add(X, Y, Z).
    ', '
        s/1 ~ p/1 = 1.0. ~tnorm = godel.
    ').

unfold_fibonacci(0).
unfold_fibonacci(N) :-
    succ(M, N),
    once(fasill_environment:fasill_rule(_, body(term(add, _)), [id(Id)|_])),
    fasill_unfolding:classic_unfold_by_id(Id),
    unfold_fibonacci(M).

% ?- fibonacci(p(p(...)), _).
goal_fibonacci(N, Fibonacci) :-
    peano(N, P),
    fasill_term:from_prolog(fibonacci(P, _), Fibonacci).

%! inorder
%
%  append([], X, X).
%  append([H|T], X, [H|S]) <- append(T, X, S). % (*)
%  inorder(empty, []).
%  inorder(tree(X, L, R), Xs) <- inorder(L, Ls) & inorder(R, Rs) & append(Ls, [X|Rs], Xs).

program_inorder :-
    program('
        append([], X, X).
        append([H|T], X, [H|S]) <- append(T, X, S). % (*)
        inorder(empty, []).
        inorder(tree(X, L, R), Xs) <- inorder(L, Ls) & inorder(R, Rs) & append(Ls, [X|Rs], Xs).
    ', '
        a/0 ~ b/0 = 0.5. ~tnorm = godel.
    ').

unfold_inorder(0).
unfold_inorder(N) :-
    succ(M, N),
    once(fasill_environment:fasill_rule(_, body(term(append, _)), [id(Id)|_])),
    fasill_unfolding:classic_unfold_by_id(Id),
    unfold_inorder(M).

% ?- inorder(tree(a, tree(a, ...), tree(a, ...)), [b,...,b]).
goal_inorder(N, Inorder) :-
    binary_tree(a, N, T),
    length(L, N),
    maplist(=(b), L),
    fasill_term:from_prolog(inorder(T, L), Inorder).

binary_tree(_, 0, empty).
binary_tree(X, N, tree(X, T, T)) :-
    succ(M, N),
    binary_tree(X, M, T).

%! selection sort
%
%  minlist([X], X, []).
%  minlist([X,H|Xs], Z, [W|Ys]) <- minlist([H|Xs], Y, Ys) & minmax(X, Y, Z, W).
%  minmax(z, s(N), z, s(N)).
%  minmax(s(M), z, z, s(M)).
%  minmax(s(M), s(N), s(P), s(Q)) <- minmax(M, N, P, Q).
%  selsort([], []).
%  selsort([X|Xs], [Y|Zs]) <- minlist([X|Xs], Y, Ys) & selsort(Ys, Zs).

program_selsort :-
    program('
        minlist([X], X, []).
        minlist([X,H|Xs], Z, [W|Ys]) <- minlist([H|Xs], Y, Ys) & minmax(X, Y, Z, W).
        minmax(z, s(N), z, s(N)).
        minmax(s(M), z, z, s(M)).
        minmax(s(M), s(N), s(P), s(Q)) <- minmax(M, N, P, Q).
        selsort([], []).
        selsort([X|Xs], [Y|Zs]) <- minlist([X|Xs], Y, Ys) & selsort(Ys, Zs).
    ', '
        s/1 ~ p/1 = 1.0. ~tnorm = godel.
    ').

unfold_selsort(0).
unfold_selsort(N) :-
    succ(M, N),
    once(fasill_environment:fasill_rule(_, body(term(minmax, _)), [id(Id)|_])),
    fasill_unfolding:classic_unfold_by_id(Id),
    unfold_selsort(M).

% ?- selsort([p(p(p(...))), p(p(...)), ..., p(z), z], [z, p(z), ..., p(p(...)), p(p(p(...)))]).
goal_selsort(N, Selsort) :-
    findall(P, (between(0, N, X), peano(X, P)), L),
    reverse(L, R),
    fasill_term:from_prolog(selsort(R, L), Selsort).