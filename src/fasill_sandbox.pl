/*  Part of FASILL

    Author:        José Antonio Riaza Valverde
    E-mail:        riaza.valverde@gmail.com
    WWW:           https://dectau.uclm.es/fasill
    Copyright (c)  2018 - 2023, José Antonio Riaza Valverde
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

:- module(fasill_sandbox, [
    sandbox_run/6,
    sandbox_listing/1,
    sandbox_classic_unfold/4,
    sandbox_unfold/4,
    sandbox_tune/6,
    sandbox_tune_smt/8,
    sandbox_linearize_heads/1,
    sandbox_extend/4
]).

:- use_module(library(assoc)).
:- use_module(fasill_exceptions).
:- use_module(fasill_environment).
:- use_module(fasill_inference).
:- use_module(fasill_parser).
:- use_module(fasill_unfolding).
:- use_module(fasill_linearization).
:- use_module(fasill_tuning).
:- use_module(fasill_tuning_smt).
:- use_module(fasill_term).

/** <module> Sandbox
    This library provides predicates for running FASILL actions (goals,
    unfolding, tuning, etc.) in a simple way.

    This library is mainly used in the online sandbox freely available at:
    https://dectau.uclm.es/fasill/sandbox in order to show all the features of
    FASILL.
*/

%!  sandbox_run(+Program, +Lattice, +Sim, +Goal, +Limit, +Options)
% 
%   This predicate loads the program <Program, Lattice, Sim> into the
%   environment and runs the goal Goal, with a depth limit Limit,
%   and writes in the standard output the resulting derivations.

sandbox_run(Program, Lattice, Sim, Goal, Limit, Options) :-
    (member(notrace, Options) ->
        true ;
        fasill_environment:set_fasill_flag(trace, term(true,[]))),
    fasill_environment:set_fasill_flag(depth_limit, num(Limit)),
    (member(cut(LambdaPl), Options) ->
        fasill_term:from_prolog(LambdaPl, Lambda),
        fasill_environment:set_fasill_flag(lambda_unification, Lambda) ;
        true),
    fasill_environment:lattice_consult(Lattice),
    catch(fasill_environment:program_consult(Program), Error1, (
        write('uncaught exception in program: '),
        fasill_term:fasill_print_term(Error1),
        nl)),
    fasill_exceptions:clear_warnings,
    catch(fasill_environment:similarity_consult(Sim), Error2, (
        write('uncaught exception in similarities: '), 
        fasill_term:fasill_print_term(Error2),
        nl)),
    (	fasill_environment:fasill_warning(Warning),
        write('warning in similarities: '),
        fasill_term:fasill_print_term(Warning),
        nl,
        fail ; true),
    statistics(runtime,[_,_]),
    (	catch(fasill_environment:query_consult(Goal, State), Error3, (
            write('uncaught exception in goal: '),
            fasill_term:fasill_print_term(Error3),
            nl)),
        fasill_inference:fasill_print_fca(State),
        nl,
        fail ; true ),
    statistics(runtime,[_,T1]),
    (member(runtime, Options) ->
        write('execution time: '),
        write(T1),
        writeln(' milliseconds') ;
        true),
    nl,
    (	fasill_inference:trace_derivation(Trace),
        fasill_inference:fasill_print_trace(Trace),
        nl,
        fail ; true).

%!  sandbox_listing(+Program)
% 
%   This predicate loads the program Program into the environment, and writes
%   in the standard output the loaded rules.

sandbox_listing(Program) :-
    catch(fasill_environment:program_consult(Program), Error1, (
        write('uncaught exception in program: '),
        fasill_term:fasill_print_term(Error1),
        nl)),
    (	fasill_environment:fasill_rule(Head, Body, Info),
        member(id(Id), Info),
        write(Id),
        write(' '),
        fasill_environment:fasill_print_rule(fasill_rule(Head, Body, Info)),
        nl,
        fail ; true).

%!  sandbox_classic_unfold(+Program, +Lattice, +Sim, +Rule)
% 
%   This predicate loads the program <Program, Lattice, Sim> into the
%   environment and runs the classic unfolding of the rule Rule.

sandbox_classic_unfold(Program, Lattice, Sim, Rule) :-
    fasill_environment:lattice_consult(Lattice),
    catch(fasill_environment:program_consult(Program), Error1, (
        write('uncaught exception in program: '),
        fasill_term:fasill_print_term(Error1),
        nl)),
    catch(fasill_environment:similarity_consult(Sim), Error2, (
        write('uncaught exception in similarities: '),
        fasill_term:fasill_print_term(Error2),
        nl)),
    (fasill_unfolding:bound_similarity_by_id(Rule) ->
        BoundSimilarity = yes ; BoundSimilarity = no),
    (fasill_unfolding:head_preserving_by_id(Rule) ->
        HeadPreserving = yes ; HeadPreserving = no),
    (fasill_unfolding:body_overriding_by_id(Rule) ->
        BodyOverriding = yes ; BodyOverriding = no),
    fasill_unfolding:classic_unfold_by_id(Rule),
    (	fasill_environment:fasill_rule(Head, Body, Info),
        fasill_environment:fasill_print_rule(fasill_rule(Head, Body, Info)),
        nl,
        fail ; true),
    write('% bound-similarity condition: '), writeln(BoundSimilarity),
    write('% head-preserving condition: '), writeln(HeadPreserving),
    write('% body-overriding condition: '), writeln(BodyOverriding).

%!  sandbox_unfold(+Program, +Lattice, +Sim, +Rule)
% 
%   This predicate loads the program <Program, Lattice, Sim> into the
%   environment and runs the similarity-based unfolding of the rule Rule.

sandbox_unfold(Program, Lattice, Sim, Rule) :-
    fasill_environment:lattice_consult(Lattice),
    catch(fasill_environment:program_consult(Program), Error1, (
        write('uncaught exception in program: '),
        fasill_term:fasill_print_term(Error1),
        nl)),
    catch(fasill_environment:similarity_consult(Sim), Error2, (
        write('uncaught exception in similarities: '),
        fasill_term:fasill_print_term(Error2),
        nl)),
    fasill_unfolding:unfold_by_id(Rule),
    (	fasill_environment:fasill_rule(Head, Body, Info),
        fasill_environment:fasill_print_rule(fasill_rule(Head, Body, Info)),
        nl,
        fail ; true).

%!  sandbox_tune(+Program, +Lattice, +Sim, +Tests, +Limit, +Options)
% 
%   This predicate loads the program <Program, Lattice, Sim> into the
%   environment and tune the program w.r.t. the set of test cases Tests, with a
%   limit of derivations Limit, and writes in the standard output the resulting
%   substitution.

sandbox_tune(Program, Lattice, Sim, Tests, Limit, Options) :-
    fasill_environment:set_fasill_flag(depth_limit, num(Limit)),
    (member(cut(LambdaPl), Options) ->
        fasill_term:from_prolog(LambdaPl, Lambda),
        fasill_environment:set_fasill_flag(lambda_unification, Lambda) ;
        true),
    fasill_environment:lattice_consult(Lattice),
    catch(fasill_environment:program_consult(Program), Error1, (
        write('uncaught exception in program: '),
        fasill_term:fasill_print_term(Error1),
        nl)),
    catch(fasill_environment:testcases_consult(Tests), Error2, (
        write('uncaught exception in testcases: '),
        fasill_term:fasill_print_term(Error2),
        nl)),
    catch(fasill_environment:similarity_consult(Sim), Error3, (
        write('uncaught exception in similarities: '),
        fasill_term:fasill_print_term(Error3),
        nl)),
    (member(prolog(PathPl), Options) ->
        fasill_environment:program_import_prolog(PathPl) ;
        true),
    statistics(runtime,[_,_]),
    (member(tuning_cut(Cut), Options) ->
        true ;
        Cut = 0.0),
    (member(basic, Options) ->
        fasill_tuning:fasill_basic_tuning(Cut, Subs, Deviation)
    ;   fasill_tuning:fasill_tuning(Cut, Subs, Deviation)),
    statistics(runtime,[_,T1]),
    write('best symbolic substitution: '),
    fasill_tuning:fasill_print_symbolic_substitution(Subs),
    nl,
    write('deviation: '), write(Deviation),
    (member(runtime, Options) ->
        nl,
        write('execution time: '),
        write(T1),
        write(' milliseconds') ;
        true),
    (member(check_substitution, Options) ->
        nl,
        writeln('checking deviation for the best symbolic substitution:'),
        fasill_tuning:fasill_test_substitution_deviation(Subs) ;
        true).

%!  sandbox_tune_smt(+Program, +Lattice, +Sim, +Tests, +Domain, +Limit, +Options)
% 
%   This predicate loads the program <Program, Lattice, Sim> into the
%   environment and tune the program w.r.t. the set of test cases Tests, using
%   an SMT solver with theory of Domain, with a limit of derivations Limit, and
%   writes in the standard output the resulting substitution.

sandbox_tune_smt(Program, Lattice, Sim, Tests, Domain, LatticeSMT, Limit, Options) :-
    fasill_environment:set_fasill_flag(depth_limit, num(Limit)),
    (member(cut(LambdaPl), Options) ->
        fasill_term:from_prolog(LambdaPl, Lambda),
        fasill_environment:set_fasill_flag(lambda_unification, Lambda) ;
        true),
    fasill_environment:lattice_consult(Lattice),
    catch(fasill_environment:program_consult(Program), Error1, (
        write('uncaught exception in program: '),
        fasill_term:fasill_print_term(Error1),
        nl)),
    catch(fasill_environment:testcases_consult(Tests), Error2, (
        write('uncaught exception in testcases: '),
        fasill_term:fasill_print_term(Error2),
        nl)),
    catch(fasill_environment:similarity_consult(Sim), Error3, (
        write('uncaught exception in similarities: '),
        fasill_term:fasill_print_term(Error3),
        nl)),
    statistics(runtime,[_,_]),
    fasill_tuning_smt:tuning_smt(Domain, LatticeSMT, Subs, Deviation),
    statistics(runtime,[_,T1]),
    write('best symbolic substitution: '),
    fasill_tuning:fasill_print_symbolic_substitution(Subs),
    nl,
    write('deviation: '),
    write(Deviation),
    (member(runtime, Options) ->
        nl,
        write('execution time: '),
        write(T1),
        write(' milliseconds') ;
        true).

%!  sandbox_linearize_heads(+Program)
% 
%   This predicate loads the program Program into the environment, and writes
%   in the standard output the loaded rules after linearizing the heads.

sandbox_linearize_heads(Program) :-
    catch(fasill_environment:program_consult(Program), Error, (
        write('uncaught exception in program: '),
        fasill_term:fasill_print_term(Error),
        nl)),
    fasill_linearization:linearize_head_program,
    (	fasill_environment:fasill_rule(Head, Body, Info),
        fasill_environment:fasill_print_rule(fasill_rule(Head, Body, Info)),
        nl,
        fail ; true).

%!  sandbox_extend(+Program, +Lattice, +Sim, +Options)
% 
%   This predicate loads the program <Program, Lattice, Sim> into the
%   environment, and writes in the standard output the loaded rules after
%   extending the program.

sandbox_extend(Program, Lattice, Sim, Options) :-
    (member(cut(LambdaPl), Options) ->
        fasill_term:from_prolog(LambdaPl, Lambda),
        fasill_environment:set_fasill_flag(lambda_unification, Lambda) ;
        true),
    fasill_environment:lattice_consult(Lattice),
    catch(fasill_environment:program_consult(Program), Error1, (
        write('uncaught exception in program: '),
        fasill_term:fasill_print_term(Error1),
        nl)),
    catch(fasill_environment:similarity_consult(Sim), Error2, (
        write('uncaught exception in similarities: '),
        fasill_term:fasill_print_term(Error2),
        nl)),
    fasill_linearization:extend_program,
    (	fasill_environment:fasill_rule(Head, Body, Info),
        fasill_environment:fasill_print_rule(fasill_rule(Head, Body, Info)),
        nl,
        fail ; true).