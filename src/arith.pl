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

:- module(arith, [
	arithmetic_evaluation/3,
	arithmetic_comparison/3
]).

:- use_module(exceptions).
:- use_module(term).

/** <module> Arithmetic
    This library provides basic predicates for arithmetic comparison and
    arithmetic evaluation.

    The general arithmetic predicates all handle expressions. An expression is
    either a number or a function. The arguments of a function are expressions.
	FASILL defines the following numeric types:

    * `integer`: depending on the Prolog system on which FASILL is executed,
       integers can be bounded or not. The type of integer support can be
       detected using the FASILL flags `bounded`, `min_integer` and
       `max_integer`.

    * `float`: floating point numbers. On most of today's platforms these are
      64-bit IEEE floating point numbers.
*/

%!  arithmetic_evaluation(+Indicator, +Expression, ?Result)
%
%   This predicate succeeds when Result is the result of evaluating the
%   expression Expression. This predicate throws an arithmetical exception if
%   there is any problem.

arithmetic_evaluation(Indicator, var(_), _) :-
	!,
	exceptions:instantiation_error(Indicator, Error),
	exceptions:throw_exception(Error).
arithmetic_evaluation(_, num(X), num(X)) :-
	!.
arithmetic_evaluation(Indicator, term(Op,Args), Result) :-
	catch(
		(   maplist(arithmetic_evaluation(Indicator), Args, Args_),
			maplist(arithmetic_type, Args_, Types),
			term:maplist(to_prolog, Args_, Prolog),
			arithmetic_op(Op, Prolog, Types, Result),
			!
		), Error,
		(Error = type(Type, From) ->
			(term:from_prolog(From, From_),
			exceptions:type_error(Type, From_, Indicator, Exception),
			exceptions:throw_exception(Exception)) ;
			(Error = evaluation(Cause) ->
				(exceptions:evaluation_error(Cause, Indicator, Exception),
				exceptions:throw_exception(Exception)) ;
				(Error = exception(Exception) ->
					exceptions:throw_exception(Exception) ;
					exceptions:throw_exception(Error))))).

%!  arithmetic_comparison(+Op, +Expression1, +Expression2)
%
%   This predicate succeeds when expressions Expression1 and Expression2,
%   evaluated as much as possible, fulfill the ordering relation Op.

arithmetic_comparison(Name/2, Expr1, Expr2) :-
	arithmetic_evaluation(Name/2, Expr1, Result1),
	arithmetic_evaluation(Name/2, Expr2, Result2),
	term:to_prolog(Result1, Result1_),
	term:to_prolog(Result2, Result2_),
	call(Name, Result1_, Result2_).

%!  arithmetic_type(+Number, ?Type)
%
%   This predicate succeeds when Number has the type Type (`integer` or
%   `float`).

arithmetic_type(num(X), integer) :-
	integer(X).
arithmetic_type(num(X), float) :-
	float(X).

%!  arithmetic_op(+Operator, +Arguments, +Types, ?Result)
%
%   This predicate succeeds when Result is the result of evaluating the
%   operator Operator with the arguments Arguments with types Types.

% Pi (constant)
arithmetic_op(pi, [], _, num(Z)) :-
	Z is pi.
% E (constant)
arithmetic_op(e, [], _, num(Z)) :-
	Z is e.
% Addition
arithmetic_op('+', [X,Y], _, num(Z)) :-
	Z is X+Y.
% Subtraction
arithmetic_op('-', [X,Y], _, num(Z)) :-
	Z is X-Y.
% Multiplication
arithmetic_op('*', [X,Y], _, num(Z)) :-
	Z is X*Y.
% Exponentiation
arithmetic_op('**', [X,Y], _, num(Z)) :-
	Z is float(X**Y).
% Division
arithmetic_op('/', [_,0], _, _) :-
	!,
	throw(evaluation(zero_division)).
arithmetic_op('/', [_,0.0], _, _) :-
	!,
	throw(evaluation(zero_division)).
arithmetic_op('/', [X,Y], _, num(Z)) :-
	Z is float(X/Y).
% Integer division
arithmetic_op('//', [X,_], [float,_], _) :-
	throw(type(integer, X)).
arithmetic_op('//', [_,Y], [_,float], _) :-
	throw(type(integer, Y)).
arithmetic_op('//', [_,0], _, _) :-
	!,
	throw(evaluation(zero_division)).
arithmetic_op('//', [_,0.0], _, _) :-
	!,
	throw(evaluation(zero_division)).
arithmetic_op('//', [X,Y], _, num(Z)) :-
	Z is X//Y.
% Unary addition
arithmetic_op('+', [X], _, num(Z)) :-
	Z is X.
% Negation
arithmetic_op('-', [X], _, num(Z)) :-
	Z is -X.
% Exp
arithmetic_op(exp, [X], _, num(Z)) :-
	Z is exp(X).
% Square root
arithmetic_op(sqrt, [X], _, num(Z)) :-
	Z is sqrt(X).
% Logarithm
arithmetic_op(log, [X], _, num(Z)) :-
	X =< 0 ->
		throw(evaluation(undefined)) ;
		Z is log(X).
% Trigonometric functions
arithmetic_op(sin, [X], _, num(Z)) :-
	Z is sin(X).
arithmetic_op(cos, [X], _, num(Z)) :-
	Z is cos(X).
arithmetic_op(tan, [X], _, num(Z)) :-
	Z is tan(X).
arithmetic_op(asin, [X], _, num(Z)) :-
	Z is asin(X).
arithmetic_op(acos, [X], _, num(Z)) :-
	Z is acos(X).
arithmetic_op(atan, [X], _, num(Z)) :-
	Z is atan(X).
% Sign
arithmetic_op(sign, [X], _, num(Z)) :-
	Z is sign(X).
% Float
arithmetic_op(float, [X], _, num(Z)) :-
	Z is float(X).
% Floor
arithmetic_op(floor, [X], [integer], _) :-
	throw(type(float, X)).
arithmetic_op(floor, [X], _, num(Z)) :-
	Z is floor(X).
% Round
arithmetic_op(round, [X], [integer], _) :-
	throw(type(float, X)).
arithmetic_op(round, [X], _, num(Z)) :-
	Z is round(X).
% Truncate
arithmetic_op(truncate, [X], [integer], _) :-
	throw(type(float, X)).
arithmetic_op(truncate, [X], _, num(Z)) :-
	Z is truncate(X).
% Ceiling
arithmetic_op(ceiling, [X], [integer], _) :-
	throw(type(float, X)).
arithmetic_op(ceiling, [X], _, num(Z)) :-
	Z is ceiling(X).
% Integer part
arithmetic_op(float_integer_part, [X], [integer], _) :-
	throw(type(float, X)).
arithmetic_op(float_integer_part, [X], _, num(Z)) :-
	Z is float_integer_part(X).
% Fractional part
arithmetic_op(float_fractional_part, [X], [integer], _) :-
	throw(type(float, X)).
arithmetic_op(float_fractional_part, [X], _, num(Z)) :-
	Z is float_fractional_part(X).
% Absolute value
arithmetic_op(abs, [X], _, num(Z)) :-
	Z is abs(X).
% Remainder
arithmetic_op(rem, [X,_], [float,_], _) :-
	throw(type(integer, X)).
arithmetic_op(rem, [_,Y], [_,float], _) :-
	throw(type(integer, Y)).
arithmetic_op(rem, [_,0], _, _) :-
	!,
	throw(evaluation(zero_division)).
arithmetic_op(rem, [X,Y], _, num(Z)) :-
	Z is rem(X,Y).
% Modulus
arithmetic_op(mod, [X,_], [float,_], _) :-
	throw(type(integer, X)).
arithmetic_op(mod, [_,Y], [_,float], _) :-
	throw(type(integer, Y)).
arithmetic_op(mod, [_,0], _, _) :-
	!,
	throw(evaluation(zero_division)).
arithmetic_op(mod, [X,Y], _, num(Z)) :-
	Z is mod(X,Y).
% Minimum
arithmetic_op(min, [X,Y], _, num(Z)) :-
	Z is min(X,Y).
% Maximum
arithmetic_op(max, [X,Y], _, num(Z)) :-
	Z is max(X,Y).
% Bitwise operators
arithmetic_op('<<', [X,_], [float,_], _) :-
	throw(type(integer, X)).
arithmetic_op('<<', [_,Y], [_,float], _) :-
	throw(type(integer, Y)).
arithmetic_op('<<', [X,Y], _, num(Z)) :-
	Z is X << Y.
arithmetic_op('>>', [X,_], [float,_], _) :-
	throw(type(integer, X)).
arithmetic_op('>>', [_,Y], [_,float], _) :-
	throw(type(integer, Y)).
arithmetic_op('>>', [X,Y], _, num(Z)) :-
	Z is X >> Y.
arithmetic_op('\\/', [X,_], [float,_], _) :-
	throw(type(integer, X)).
arithmetic_op('\\/', [_,Y], [_,float], _) :-
	throw(type(integer, Y)).
arithmetic_op('\\/', [X,Y], _, num(Z)) :-
	Z is '\\/'(X,Y).
arithmetic_op('/\\', [X,_], [float,_], _) :-
	throw(type(integer, X)).
arithmetic_op('/\\', [_,Y], [_,float], _) :-
	throw(type(integer, Y)).
arithmetic_op('/\\', [X,Y], _, num(Z)) :-	
	Z is '/\\'(X,Y).
arithmetic_op('\\', [X], [float], _) :-
	throw(type(integer, X)).
arithmetic_op('\\', [X], _, num(Z)) :-
	Z is '\\'(X).
arithmetic_op(Op, Args, _, _) :-
	length(Args, Length),
	throw(type(evaluable, Op/Length)).