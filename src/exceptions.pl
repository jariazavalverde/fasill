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

:- module(exceptions, [
	% handle exceptions
	throw_exception/1,
	throw_warning/1,
	clear_warnings/0,
	% make errors
	instantiation_error/2,
	type_error/4,
	evaluation_error/3,
	existence_error/4,
	domain_error/3,
	syntax_error/4
]).

:- use_module(environment).
:- use_module(term).

/** <module> Exceptions
    This library provides basic predicates for making and throwing errors.

    FASILL provides an exception handling mechanism, based on the builtin
    control constructs `catch/3` and `throw/1`. When an error occurs the
    current goal is replaced by a goal:

    `throw(error(ErrorTerm, ImplementationDefinedTerm))`

    * `instantiation_error`: an argument or one of its components is a variable,
       and an instantiated argument or component is required.

    * `type_error`: the type of an argument or of one of its components is
       incorrect, but not a variable.

    * `evaluation_error`: the operands of an evaluable functor has an
       exceptional value.

    * `existence_error`: the object on which an operation is to be performed
       does not exist.

    * `domain_error`: the type of an argument is correct but the value is
      outside the domain for which the procedure is defined. 

    * `syntax_error`: a sequence of incorrect characters are being input as a
      read term.
*/

% HANDLE EXCEPTIONS

%!  throw_exception(+Exception)
%
%   This predicate throws the exception Exception.
throw_exception(Exception) :-
	resolution:retractall(check_success),
	throw(Exception).

%!  clear_warnings
%
%   This predicate clears all the current warning.

clear_warnings :-
	environment:retractall(fasill_warning(_)).

%!  throw_warning(+Warning)
%
%   This predicate throws the warning +Warning.

throw_warning(Warning) :-
	environment:assertz(fasill_warning(Warning)).

% MAKE ERRORS

%!  instantiation_error(+Indicator, ?Error)
%
%   This predicate succeeds when Error is the instantiation error produced by
%   the predicate Indicator. This error is produced when an argument or one of
%   its components is a variable, and an instantiated argument or component is
%   required.

instantiation_error(Indicator, term(error, [term(instantiation_error,[]), Indicator_])) :-
	term:from_prolog(Indicator, Indicator_).

%!  type_error(+Type, +Term, +Indicator, ?Error)
%
%   This predicate succeeds when Error is the type error produced by the type 
%   Type of the term Term in the predicate Indicator. This error is produced
%   when the type of an argument or of one of its components is incorrect, but
%   not a variable.

type_error(Type, Term, Indicator, term(error, [term(type_error, [Type_, Term]), Indicator_])) :-
	term:from_prolog(Type, Type_),
	term:from_prolog(Indicator, Indicator_).

%!  evaluation_error(+Cause, +Indicator, ?Error)
%
%   This predicate succeeds when Error is the evaluation error produced by the
%   cause Cause in the predicate Indicator. This error is produced when the
%   operands of an evaluable functor has an exceptional value. 

evaluation_error(Cause, Indicator, term(error, [term(evaluation_error,[Cause_]), Indicator_])) :-
	term:from_prolog(Cause, Cause_),
	term:from_prolog(Indicator, Indicator_).

%!  existence_error(+Cause, +Term, +Indicator, ?Error)
%
%   This predicate succeeds when Error is the existence error produced by the
%   term Term in the predicate Indicator. This error is produced when the object
%   on which an operation is to be performed does not exist.

existence_error(Cause, Term, Indicator, term(error, [term(existence_error,[Cause_,Term_]), Indicator_])) :-
	term:from_prolog(Cause, Cause_),
	term:from_prolog(Term, Term_),
	term:from_prolog(Indicator, Indicator_).

%!  domain_error(+Domain, +Indicator, ?Error)
%
%   This predicate succeeds when Error is the domain error produced by the
%   term Term in the predicate Indicator. This error is produced when the type
%   of an argument is correct but the value is outside the domain for which the
%   procedure is defined. 

domain_error(Domain, Indicator, term(error, [term(domain_error,[Domain_]), Indicator_])) :-
	term:from_prolog(Domain, Domain_),
	term:from_prolog(Indicator, Indicator_).

%!  syntax_error(+Line, +Columns, +Message, ?Error)
%
%   This predicate succeeds when Error is the syntax error produced in line
%   Line and Column Column with message Message. This error is produced when a
%   sequence of incorrect characters are being input as a read term.

syntax_error(Line, Column, Message, term(error, [term(syntax_error,[Line_, Column_, Message_])])) :-
	term:from_prolog(line(Line), Line_),
	term:from_prolog(column(Column), Column_),
	term:from_prolog(message(Message), Message_).