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

:- module(term, [
	fasill_show/1,
	fasill_show/2,
	fasill_term_variables/2,
    to_prolog/2,
    to_prolog_list/2,
    from_prolog/2,
    from_prolog_list/2,
    fasill_atom/1,
    fasill_float/1,
    fasill_integer/1,
    fasill_number/1,
    fasill_term/1,
    fasill_var/1,
    fasill_ground/1,
    fasill_callable/1,
    fasill_list/1,
    fasill_connective/1
]).

:- use_module(library(assoc)).
:- use_module(environment).

/** <module> Term
    This library provides basic predicates for terms manipulation.

    Here, we use a ground representation to store and manipulate FASILL terms
    with Prolog, where:

    * variables are tagged as `var/1` terms, whose only argument is an atom
      representing its identifier (e.g. a variable with identifier X is
      represented as `var('X')`);

    * numbers are tagged as `num/1` terms, whose only argument is a number
      representing its value (e.g. a number with value `1` is represented as
      `num(1)`);

    * and atoms and compound terms are tagged as `term/2` terms, whose first
      argument is a term representing its functor and the second one is a list
      containing its tagged arguments (e.g. an atom `p(a,X)` is represented as
      `term(p, [term(a,[]), var('X')])`).
*/

%!  fasill_show(+Term, ?Representation)
%
% This predicate succeeds when Term is a valid FASILL term and Representation is
% the Prolog term which represent the literal FASILL term Term.

fasill_show(Term, Output) :-
	with_output_to(atom(Output), fasill_show(Term)).

fasill_show([]) :-
	!.
fasill_show(X) :-
	is_assoc(X),
	!,
	assoc_to_list(X, Subs),
	fasill_show(Subs).
fasill_show(top) :-
	write(top).
fasill_show(bot) :-
	write(bot).
fasill_show(sup(X, Y)) :-
	write('sup('),
	fasill_show(X),
	write(', '),
	fasill_show(Y),
	write(')').
fasill_show(num(X)) :-
	write(X).
fasill_show(var('$'(X))) :-
	!,
	write('V'),
	write(X).
fasill_show(var(X)) :-
	write(X).
fasill_show(X-Y) :-
	write(X),
	write('/'),
	fasill_show(Y).
fasill_show(X/Y) :-
	write(X),
	write('/'),
	fasill_show(Y).
fasill_show(term('#'(Name),[])) :-
	!,
	write('#'),
	write(Name).
fasill_show(term('#@'(Name),Args)) :-
	!,
	write('#@'),
	write(Name),
	write('('),
	fasill_show(Args),
	write(')').
fasill_show(term('#&'(Name),[X,Y])) :-
	!,
	write('('),
	fasill_show(X),
	write(' #&'),
	write(Name),
	write(' '),
	fasill_show(Y),
	write(')'). 
fasill_show(term('#|'(Name),[X,Y])) :-
	!,
	write('('),
	fasill_show(X),
	write(' #|'),
	write(Name),
	write(' '),
	fasill_show(Y),
	write(')'). 
fasill_show(term('&'(Name),[X,Y])) :-
	!,
	write('('),
	fasill_show(X),
	write(' &'), write(Name),
	write(' '),
	fasill_show(Y),
	write(')'). 
fasill_show(term('|'(Name),[X,Y])) :-
	!,
	write('('),
	fasill_show(X),
	write(' |'),
	write(Name),
	write(' '),
	fasill_show(Y),
	write(')'). 
fasill_show(term('.',[X,Y])) :-
	!,
	fasill_show_list(list(term('.',[X,Y]))). 
fasill_show(term(X,[])) :-
	write(X).
fasill_show(term(X,Y)) :-
	Y \= [],
	write(X),
	write('('),
	fasill_show(Y),
	write(')').
fasill_show(exception(X)) :-
	write('uncaught exception in derivation: '),
	fasill_show(X).
fasill_show(state(Goal,Subs)) :-
	write('<'),
	fasill_show(Goal),
	write(', {'),
	fasill_show(Subs),
	write('}>').
fasill_show([X|Y]) :-
	Y \= [],
	fasill_show(X),
	write(', '),
	fasill_show(Y).
fasill_show([X]) :-
	fasill_show(X).

fasill_show_list(term('[]',[])) :-
	!.
fasill_show_list(term([],[])) :-
	!.
fasill_show_list(term('.',[X,Y])) :-
	!,
	write(','),
	fasill_show(X),
	fasill_show_list(Y).
fasill_show_list(list(term('.',[X,Y]))) :-
	!,
	write('['),
	fasill_show(X),
	fasill_show_list(Y),
	write(']').
fasill_show_list(X) :-
	write('|'),
	fasill_show(X).

%!  fasill_term_variables(+Term, ?Variables)
%
%   This predicate succeeds when Variables is the list of variables in the term
%   Term.

fasill_term_variables(var(X), [var(X)]) :-
	!.
fasill_term_variables(term(_,Args), Vars) :-
	!,
	fasill_term_variables(Args, Vars).
fasill_term_variables([H|T], Vars) :-
	!,
	fasill_term_variables(H, Vh),
	fasill_term_variables(T, Vt),
	append(Vh, Vt, Vars).
fasill_term_variables(_, []).

%!  to_prolog(+FASILL, ?Prolog)
%
%   This predicate takes the FASILL object FASILL and returns the object Prolog
%   in Prolog notation.

to_prolog(num(X), X) :-
	!.
to_prolog(var(_), _) :-
	!.
to_prolog(term('[]',[]), []) :-
	!.
to_prolog(term('.',[X,Y]), [X_|Y_]) :-
	!,
	to_prolog(X, X_),
	to_prolog(Y, Y_).
to_prolog(term(X,Xs), Term) :-
	atom(X),
	!,
	maplist(to_prolog, Xs, Ys),
	Term =.. [X|Ys].

%!  from_prolog(+Prolog, ?FASILL)
%
%   This predicate takes the Prolog object Prolog and returns the object FASILL
%   in FASILL notation.

from_prolog(X, var(X)) :-
	var(X),
	!.
from_prolog(X, num(X)) :-
	number(X),
	!.
from_prolog(X, term(X, [])) :-
	atom(X),
	!.
from_prolog([], term('[]', [])) :-
	!.
from_prolog([X|Xs], term('.', [Y,Ys])) :-
	!,
	from_prolog(X,Y),
	from_prolog(Xs,Ys).
from_prolog(X, term(H,Args)) :-
	compound(X),
	!,
	X =.. [H|T],
	maplist(from_prolog, T, Args).

%!  to_prolog_list(+FASILL, ?Prolog)
%
%   This predicate takes the FASILL list FASILL and returns the list Prolog in
%   Prolog notation.

to_prolog_list(term('[]', []), []).
to_prolog_list(term('.',[H,S]), [H|T]) :-
	to_prolog_list(S, T).

%!  from_prolog_list(+Prolog, ?FASILL)
%
%  This predicate takes the Prolog list Prolog and returns the list FASILL in
%  FASILL notation.

from_prolog_list([], term('[]', [])).
from_prolog_list([H|T], term('.',[H,S])) :-
	from_prolog_list(T, S).

%!  fasill_number(+Term)
%
%   This predicate succeeds when Term is a FASILL number.

fasill_number(num(_)).

%!  fasill_integer(+Term)
%
%   This predicate succeeds when Term is a FASILL integer.

fasill_integer(num(X)) :-
	integer(X).

%!  fasill_float(+Term)
%
%   This predicate succeeds when Term is a FASILL float.

fasill_float(num(X)) :-
	float(X).

%!  fasill_atom(+Term)
%
%   This predicate succeeds when Term is a FASILL atom.

fasill_atom(term(_,[])).

%!  fasill_term(+Term)
%
%   This predicate succeeds when Term is a FASILL term.

fasill_term(term(_,_)).

%!  fasill_var(+Term)
%
%   This predicate succeeds when Term is a FASILL variable.

fasill_var(var(_)).

%!  fasill_ground(+Term)
%
%   This predicate succeeds when Term is a FASILL ground term.

fasill_ground(num(_)).
fasill_ground(str(_)).
fasill_ground(term(_,Xs)) :-
	maplist(fasill_ground, Xs).

%!  fasill_callable(+Term)
%
%   This predicate succeeds when Term is a callable term.

fasill_callable(term(_, _)) :-
	!.
fasill_callable(X) :-
	environment:lattice_call_member(X).

%!  fasill_list(+Term)
%
%   This predicate succeeds when Term is a list or variable.

fasill_list(term('[]',[])) :-
	!.
fasill_list(var(_)) :-
	!.
fasill_list(term('.',[_,T])) :-
	fasill_list(T).

%!  fasill_connective(+Term)
%
%   This predicate succeeds when Term is a connective.

fasill_connective(term(Type,Arg)) :-
    (Type = '&' ; Type = '|' ; Type = '@'),
    (Arg = [] ; Arg = [_]).