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

:- module(sandbox, [
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
:- use_module(exceptions).
:- use_module(environment).
:- use_module(parser).
:- use_module(unfolding).
:- use_module(linearization).
:- use_module(tuning).
:- use_module(tuning_smt).
:- use_module(term).

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
		environment:set_fasill_flag(trace, term(true,[]))),
	environment:set_fasill_flag(depth_limit, num(Limit)),
	(member(cut(LambdaPl), Options) ->
		term:from_prolog(LambdaPl, Lambda),
		environment:set_fasill_flag(lambda_unification, Lambda) ;
		true),
	environment:lattice_consult(Lattice),
	catch(environment:program_consult(Program), Error1, (
		write('uncaught exception in program: '),
		term:fasill_print_term(Error1),
		nl)),
	exceptions:clear_warnings,
	catch(environment:similarity_consult(Sim), Error2, (
		write('uncaught exception in similarities: '), 
		term:fasill_print_term(Error2),
		nl)),
	(	environment:fasill_warning(Warning),
		write('warning in similarities: '),
		term:fasill_print_term(Warning),
		nl,
		fail ; true),
	statistics(runtime,[_,_]),
	(	catch(query_consult(Goal, State), Error3, (
			write('uncaught exception in goal: '),
			term:fasill_print_term(Error3),
			nl)),
		resolution:fasill_print_fca(State),
		nl,
		fail ; true ),
	statistics(runtime,[_,T1]),
	(member(runtime, Options) ->
		write('execution time: '),
		write(T1),
		writeln(' milliseconds') ;
		true),
	nl,
	(	resolution:trace_derivation(Trace),
		resolution:fasill_print_trace(Trace),
		nl,
		fail ; true).

%!  sandbox_listing(+Program)
% 
%   This predicate loads the program Program into the environment, and writes
%   in the standard output the loaded rules.

sandbox_listing(Program) :-
	catch(environment:program_consult(Program), Error1, (
		write('uncaught exception in program: '),
		term:fasill_print_term(Error1),
		nl)),
	(	environment:fasill_rule(Head, Body, Info),
		member(id(Id), Info),
		write(Id),
		write(' '),
		environment:fasill_print_rule(fasill_rule(Head, Body, Info)),
		nl,
		fail ; true).

%!  sandbox_classic_unfold(+Program, +Lattice, +Sim, +Rule)
% 
%   This predicate loads the program <Program, Lattice, Sim> into the
%   environment and runs the classic unfolding of the rule Rule.

sandbox_classic_unfold(Program, Lattice, Sim, Rule) :-
	environment:lattice_consult(Lattice),
	catch(environment:program_consult(Program), Error1, (
		write('uncaught exception in program: '),
		term:fasill_print_term(Error1),
		nl)),
	catch(environment:similarity_consult(Sim), Error2, (
		write('uncaught exception in similarities: '),
		term:fasill_print_term(Error2),
		nl)),
	unfolding:classic_unfold_by_id(Rule),
	(	environment:fasill_rule(Head, Body, Info),
		environment:fasill_print_rule(fasill_rule(Head, Body, Info)),
		nl,
		fail ; true).

%!  sandbox_unfold(+Program, +Lattice, +Sim, +Rule)
% 
%   This predicate loads the program <Program, Lattice, Sim> into the
%   environment and runs the similarity-based unfolding of the rule Rule.

sandbox_unfold(Program, Lattice, Sim, Rule) :-
	environment:lattice_consult(Lattice),
	catch(environment:program_consult(Program), Error1, (
		write('uncaught exception in program: '),
		term:fasill_print_term(Error1),
		nl)),
	catch(environment:similarity_consult(Sim), Error2, (
		write('uncaught exception in similarities: '),
		term:fasill_print_term(Error2),
		nl)),
	unfolding:unfold_by_id(Rule),
	(	environment:fasill_rule(Head, Body, Info),
		environment:fasill_print_rule(fasill_rule(Head, Body, Info)),
		nl,
		fail ; true).

%!  sandbox_tune(+Program, +Lattice, +Sim, +Tests, +Limit, +Options)
% 
%   This predicate loads the program <Program, Lattice, Sim> into the
%   environment and tune the program w.r.t. the set of test cases Tests, with a
%   limit of derivations Limit, and writes in the standard output the resulting
%   substitution.

sandbox_tune(Program, Lattice, Sim, Tests, Limit, Options) :-
	environment:set_fasill_flag(depth_limit, num(Limit)),
	(member(cut(LambdaPl), Options) ->
		term:from_prolog(LambdaPl, Lambda),
		environment:set_fasill_flag(lambda_unification, Lambda) ;
		true),
	environment:lattice_consult(Lattice),
	catch(environment:program_consult(Program), Error1, (
		write('uncaught exception in program: '),
		term:fasill_print_term(Error1),
		nl)),
	catch(environment:testcases_consult(Tests), Error2, (
		write('uncaught exception in testcases: '),
		term:fasill_print_term(Error2),
		nl)),
	catch(environment:similarity_consult(Sim), Error3, (
		write('uncaught exception in similarities: '),
		term:fasill_print_term(Error3),
		nl)),
	(member(prolog(PathPl), Options) ->
		environment:program_import_prolog(PathPl) ;
		true),
	statistics(runtime,[_,_]),
	(member(tuning_cut(Cut), Options) ->
		true ;
		Cut = 0.0),
	tuning:tuning_thresholded(Cut, Subs, Deviation),
	statistics(runtime,[_,T1]),
	write('best symbolic substitution: '),
	tuning:fasill_print_symbolic_substitution(Subs),
	nl,
	write('deviation: '), write(Deviation),
	(member(runtime, Options) ->
		nl,
		write('execution time: '),
		write(T1),
		write(' milliseconds') ;
		true).

%!  sandbox_tune_smt(+Program, +Lattice, +Sim, +Tests, +Domain, +Limit, +Options)
% 
%   This predicate loads the program <Program, Lattice, Sim> into the
%   environment and tune the program w.r.t. the set of test cases Tests, using
%   an SMT solver with theory of Domain, with a limit of derivations Limit, and
%   writes in the standard output the resulting substitution.

sandbox_tune_smt(Program, Lattice, Sim, Tests, Domain, LatticeSMT, Limit, Options) :-
	environment:set_fasill_flag(depth_limit, num(Limit)),
	(member(cut(LambdaPl), Options) ->
		term:from_prolog(LambdaPl, Lambda),
		environment:set_fasill_flag(lambda_unification, Lambda) ;
		true),
	environment:lattice_consult(Lattice),
	catch(environment:program_consult(Program), Error1, (
		write('uncaught exception in program: '),
		term:fasill_print_term(Error1),
		nl)),
	catch(environment:testcases_consult(Tests), Error2, (
		write('uncaught exception in testcases: '),
		term:fasill_print_term(Error2),
		nl)),
	catch(environment:similarity_consult(Sim), Error3, (
		write('uncaught exception in similarities: '),
		term:fasill_print_term(Error3),
		nl)),
	statistics(runtime,[_,_]),
	tuning_smt:tuning_smt(Domain, LatticeSMT, Subs, Deviation),
	statistics(runtime,[_,T1]),
	write('best symbolic substitution: '),
	tuning:fasill_print_symbolic_substitution(Subs),
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
	catch(environment:program_consult(Program), Error, (
		write('uncaught exception in program: '),
		term:fasill_print_term(Error),
		nl)),
	linearization:linearize_head_program,
	(	environment:fasill_rule(Head, Body, Info),
		environment:fasill_print_rule(fasill_rule(Head, Body, Info)),
		nl,
		fail ; true).

%!  sandbox_extend(+Program, +Lattice, +Sim, +Options)
% 
%   This predicate loads the program <Program, Lattice, Sim> into the
%   environment, and writes in the standard output the loaded rules after
%   extending the program.

sandbox_extend(Program, Lattice, Sim, Options) :-
	(member(cut(LambdaPl), Options) ->
		term:from_prolog(LambdaPl, Lambda),
		environment:set_fasill_flag(lambda_unification, Lambda) ;
		true),
	environment:lattice_consult(Lattice),
	catch(environment:program_consult(Program), Error1, (
		write('uncaught exception in program: '),
		term:fasill_print_term(Error1),
		nl)),
	catch(environment:similarity_consult(Sim), Error2, (
		write('uncaught exception in similarities: '),
		term:fasill_print_term(Error2),
		nl)),
	linearization:extend_program,
	(	environment:fasill_rule(Head, Body, Info),
		environment:fasill_print_rule(fasill_rule(Head, Body, Info)),
		nl,
		fail ; true).