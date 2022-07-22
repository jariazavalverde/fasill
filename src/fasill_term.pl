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

:- module(fasill_term, [
    % Prolog conversion
    to_prolog/2,
    to_prolog_list/2,
    from_prolog/2,
    from_prolog_list/2,
    % FASILL type testing
    fasill_atom/1,
    fasill_float/1,
    fasill_integer/1,
    fasill_number/1,
    fasill_term/1,
    fasill_var/1,
    fasill_ground/1,
    fasill_callable/1,
    fasill_list/1,
    fasill_connective/1,
    fasill_member/2,
    % variables
    fasill_term_variables/2,
    fasill_count_variables/2,
    fasill_max_variable/3,
    % format
    fasill_print_term/1
]).

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

% PROLOG CONVERSION

%!  to_prolog(+FASILL, ?Prolog)
%
%   This predicate takes the ground object FASILL and returns the object Prolog
%   in Prolog representation.

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
%   in ground representation.

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
%   This predicate takes a FASILL list FASILL and returns the list Prolog in
%   Prolog representation.

to_prolog_list(term('[]', []), []).
to_prolog_list(term('.',[H,S]), [H|T]) :-
    to_prolog_list(S, T).

%!  from_prolog_list(+Prolog, ?FASILL)
%
%  This predicate takes a Prolog list Prolog and returns the list FASILL in
%  FASILL ground representation.

from_prolog_list([], term('[]', [])).
from_prolog_list([H|T], term('.',[H,S])) :-
    from_prolog_list(T, S).

% FASILL TYPE TESTING

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
fasill_ground(term(_,Xs)) :-
    maplist(fasill_ground, Xs).

%!  fasill_callable(+Term)
%
%   This predicate succeeds when Term is a callable term.

fasill_callable(var(_)) :-
    !, fail.
fasill_callable(_).

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

%!  fasill_member(?Member, +Term)
%
%   This predicate succeeds when Member is an element into Term.

fasill_member(X, term('.',[X,_])).
fasill_member(X, term('.',[_,T])) :- fasill_member(X, T).

% VARIABLES

%!  fasill_term_variables(+Term, ?Variables)
%
%   This predicate succeeds when Variables is a list made up by the variables
%   of Term, in order of appearance and with repetition.

fasill_term_variables(Term, Vars) :-
    fasill_term_variables(Term, [], Vars).

% Variable
fasill_term_variables(var(X), Xs, [var(X)|Xs]) :-
    !.
% Term
fasill_term_variables(term(_, Args), Xs, Vars) :-
    !,
    fasill_term_variables(Args, Xs, Vars).
% List
fasill_term_variables([H|T], Xs, Vars) :-
    !,
    fasill_term_variables(H, Xs, Ys),
    fasill_term_variables(T, Ys, Vars).
% Other
fasill_term_variables(_, Xs, Xs).

%!  fasill_count_variables(+Term, ?Variables)
%
%   This predicate succeeds when Variables is a list of pairs Var-N where Var
%   is a variable and N is the number of occurrences of Var in the term Term.

fasill_count_variables(Term, Vars) :-
    fasill_count_variables(Term, [], Vars).

% New variable
fasill_count_variables(var(X), Vars, [X-1|Vars]) :-
    \+member(X-_, Vars),
    !.
% Repeated variable
fasill_count_variables(var(X), Vars, [X-M|Vars2]) :-
    !,
    select(X-N, Vars, Vars2),
    succ(N, M).
% Term
fasill_count_variables(term(_, Xs), Vars, Vars2) :-
    !,
    fasill_count_variables(Xs, Vars, Vars2).
% List
fasill_count_variables([], Vars, Vars) :-
    !.
fasill_count_variables([X|Xs], Vars, Vars3) :-
    !,
    fasill_count_variables(X, Vars, Vars2),
    fasill_count_variables(Xs, Vars2, Vars3).
% Other
fasill_count_variables(_, Vars, Vars).

%!  max_variable(+Expression, +Variable, ?Max)
%
%   This predicate succeeds when Max is the maximum natural number for wich 
%   Variable{Max} occurs in the expression Expression.

fasill_max_variable(Expr, Variable, Max) :-
    fasill_max_variable(Expr, Variable, 0, Max).
fasill_max_variable(var(V), Variable, N, Max) :-
    atom(V),
    atom_length(Variable, Length),
    sub_atom(V, 0, Length, _, Variable),
    !,
    sub_atom(V, Length, _, 0, Rest),
    atom_codes(Rest, Codes),
    catch((number_codes(M, Codes), Max is max(N,M)), _, Max = N).
fasill_max_variable(term(_, Xs), Variable, N, Max) :-
    !,
    fasill_max_variable(Xs, Variable, N, Max).
fasill_max_variable([], _, N, N) :- !.
fasill_max_variable([X|Xs], Variable, N, Max) :-
    !,
    fasill_max_variable(X, Variable, N, M),
    fasill_max_variable(Xs, Variable, M, Max).
fasill_max_variable(_, _, N, N).

% FORMAT

%!  fasill_print_term(+Term)
% 
%   This predicate writes a FASILL term for the standard output.

% Fresh variable
fasill_print_term(var($(N))) :-
    write('V'),
    write(N), !.
% Variable
fasill_print_term(var(V)) :-
    write(V), !.
% Number
fasill_print_term(num(N)) :-
    write(N), !.
% List
fasill_print_term(term('[]', [])) :-
    write('[]'), !.
fasill_print_term(term('.', [H,T])) :-
    write('['),
    fasill_print_term(H),
    fasill_print_list(T),
    write(']'), !.
% Symbolic constant
fasill_print_term(term('#'(K), [])) :-
    write('#'),
    write(K), !.
% Labelled connective
fasill_print_term(term(Con, [])) :-
    Con =.. [Type, Label],
    write(Type),
    write(Label), !.
fasill_print_term(term(Con, [X|Xs])) :-
    Con =.. [Type, Label],
    write(Type),
    write(Label),
    write('('),
    fasill_print_term(X),
    fasill_print_term(Xs),
    write(')'), !.
% Supremum
fasill_print_term(sup(X,Y)) :-
    write('sup('),
    fasill_print_term(X),
    write(','),
    fasill_print_term(Y),
    write(')'), !.
% Atom
fasill_print_term(term(Atom, [])) :-
    write_term(Atom, [quoted(true)]), !.
% Compound term
fasill_print_term(term(Atom, [X|Xs])) :-
    write_term(Atom, [quoted(true)]),
    write('('),
    fasill_print_term(X),
    fasill_print_term(Xs),
    write(')'), !.
% Arguments
fasill_print_term([]) :-
    !.
fasill_print_term([X|Xs]) :-
    write(','),
    fasill_print_term(X),
    fasill_print_term(Xs), !.
% Other
fasill_print_term(X) :-
    write(X).
% List (elements)
fasill_print_list(term('.', [H,T])) :-
    write(','),
    fasill_print_term(H),
    fasill_print_list(T), !.
fasill_print_list(term('[]', [])) :-
    !.
fasill_print_list(X) :-
    write('|'),
    fasill_print_term(X).