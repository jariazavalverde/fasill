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

:- module(directives, [
	is_directive/1,
	eval_directive/1
]).

:- use_module(environment).
:- use_module(exceptions).
:- use_module(term).

/** <module> Directives
    This library provides predicates for running FASILL directives.
	
    FASILL directives are annotations inserted in FASILL source files for the
    compiler.
*/

%!  is_directive(?Indicator)
%
%   This predicate succeeds when Indicator is the indicator of a directive of
%   FASILL. An indicator is a term of the form Name/Arity, where Name is an
%   atom and Arity is a non-negative integer.
is_directive(Name/Arity) :-
	member(Name/Arity, [
		set_fasill_flag/2
	]).

%!  eval_directive(+Directive)
%
%   This predicate succeeds when Directive is a valid FASILL directive and it
%   can be executed.

%%%!  set_fasill_flag(+atom, +term)
%%%
%%%   set_fasill_flag(Flag, Value) sets the value of the Flag to Value.

% Instantiation error
eval_directive(term(set_fasill_flag, [Flag,Value])) :-
	(\+term:fasill_ground(Flag) ; \+term:fasill_ground(Value)),
	exceptions:instantiation_error(set_fasill_flag/2, Error),
	exceptions:throw_exception(Error),
	!.
% Type error (Flag must be an atom)
eval_directive(term(set_fasill_flag, [Flag, _Value])) :-
	\+term:fasill_atom(Flag),
	exceptions:type_error(Flag, atom, set_fasill_flag/2, Error),
	exceptions:throw_exception(Error),
	!.
% Domain error (Flag must be a valid flag)
eval_directive(term(set_fasill_flag, [term(FlagName,[]), _Value])) :-
	\+environment:current_fasill_flag(FlagName, _),
	exceptions:domain_error(fasill_flag, set_fasill_flag/2, Error),
	exceptions:throw_exception(Error),
	!.
% Domain error (Value must be a valid flag value)
eval_directive(term(set_fasill_flag, [term(FlagName,[]),Value])) :-
	\+environment:is_fasill_flag_value(FlagName, Value),
	exceptions:domain_error(flag_value+(FlagName,Value), set_fasill_flag/2, Error),
	exceptions:throw_exception(Error),
	!.
% Ok
eval_directive(term(set_fasill_flag, [term(FlagName,[]),Value])) :-
	environment:set_fasill_flag(FlagName, Value).