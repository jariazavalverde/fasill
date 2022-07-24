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

:- use_module('../../src/fasill_environment').
:- use_module('../../src/fasill_tuning').

/** <test> Tuning
    This library provides predicates for testing tuning techniques.
*/

test_tuning(Repeat, Method, Steps, Substitutions, Min, Aver, Max) :-
    fasill_environment:lattice_consult('../../sample/lat/unit.lat.pl'),
    gen_program(Steps),
    gen_members(Substitutions),
    gen_testcases,
    test_tuning_loop(Repeat, Method, [], [], Times, Inferences),
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

test_tuning_loop(0, _G, Ts, Is, Ts, Is).
test_tuning_loop(N, G, Ts, Is, Times, Inferences) :- 
    succ(M, N),
    statistics(runtime, [_,_]),
    statistics(inferences, I0),
    fasill_tuning:call(G, [sym(td,s,0)/val(td,num(1.0),0)], 0.0),
    statistics(inferences, If),
    statistics(runtime, [_,T]),
    I is If-I0,
    (T > 0 ->
        N_ = M, Ts_ = [T|Ts], Is_ = [I|Is] ;
        N_ = N, Ts_ = Ts, Is_ = Is),
    test_tuning_loop(N_, G, Ts_, Is_, Times, Inferences).

gen_program(Inferences) :-
    fasill_environment:program_retractall,
    fasill_environment:asserta(fasill_predicate(p/0)),
    fasill_environment:asserta(fasill_predicate(q/0)),
    gen_body(Inferences, Body),
    fasill_environment:asserta(fasill_rule(head(term(p, [])), body(Body), [id(1), syntax(fasill)])),
    fasill_environment:asserta(fasill_rule(head(term(q, [])), empty, [id(2), syntax(fasill)])).

gen_body(0, term('#'(s), [])).
gen_body(N, term('&'(godel), [term(q, []), Body])) :-
    succ(M, N),
    gen_body(M, Body).

gen_members(N) :-
    fasill_environment:abolish(members/1),
    gen_list(N, Members),
    fasill_environment:asserta(members(Members)).

gen_list(0, [1.0]).
gen_list(N, [0.0|L]) :-
    succ(M, N),
    gen_list(M, L).

gen_testcases :-
    fasill_environment:retractall(fasill_testcase(_,_)),
    fasill_environment:retractall(fasill_testcase_precondition(_)),
    fasill_environment:asserta(fasill_testcase(num(1.0), term(p, []))).