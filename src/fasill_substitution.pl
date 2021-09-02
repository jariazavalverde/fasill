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

:- module(fasill_substitution, [
    empty_substitution/1,
    substitution_to_list/2,
    list_to_substitution/2,
    put_substitution/4,
    get_substitution/3,
    init_substitution/2,
    apply/3,
    compose/3,
    fasill_print_substitution/1
]).

:- use_module(library(assoc)).
:- use_module(fasill_term).

/** <module> Substitutions
    This library provides basic predicates for substitutions manipulation.
    A substitution is a mapping from variables to FASILL terms.

    The implementation of this library uses association lists (`library(assoc)`)
    to represent substitutions.
*/

%!  empty_substitution(?Substitution)
%
%   This predicate succeeds when Substitution is an empty substitution.

empty_substitution(Sub) :-
    empty_assoc(Sub).

%!  substitution_to_list(+Substitution, ?List)
%
%   This predicate translates Substitution to a list List of Variable-Value
%   pairs.

substitution_to_list(Sub, List) :-
    assoc_to_list(Sub, List).

%!  list_to_substitution(+List, ?Substitution)
%
%   This predicate translates List of Variable-Value pairs into a substitution
%   Substitution.

list_to_substitution(List, Sub) :-
    list_to_assoc(List, Sub).

%!  put_substitution(+SubstitutionIn, +Var, +Term, ?SubtitutionOut)
%
%   This predicate adds a new binding Var/Term to the substitution
%   SubstitutionIn, producing the new substitution SubtitutionOut.

put_substitution(SubIn, Var, Term, SubOut) :-
    put_assoc(Var, SubIn, Term, SubOut).

%!  get_substitution(+Substitution, +Var, ?Term)
%
%   This predicate succeeds if Var-Term is a binding in Substitution. 

get_substitution(Sub, Var, Term) :-
    get_assoc(Var, Sub, Term).

%!  init_substitution(+Goal, ?Substitution)
%
%   This predicate succeeds when Substitution is the initial substitution for 
%   the goal Goal, where each variable X in goal Goal is binded to itself (X/X).

init_substitution(Goal, Sub) :-
    empty_substitution(Id),
    init_substitution(Goal, Id, Sub).

% Variable
init_substitution(var(X), Sub0, Sub1) :-
    !,
    (get_substitution(Sub0, X, _) ->
        Sub1 = Sub0 ;
        put_substitution(Sub0, X, var(X), Sub1)).
% Term
init_substitution(term(_,Args), Sub0, Sub1) :-
    !,
    init_substitution(Args, Sub0, Sub1).
% List
init_substitution([H|T], Sub0, Sub2) :-
    !,
    init_substitution(H, Sub0, Sub1),
    init_substitution(T, Sub1, Sub2).
% Others
init_substitution(_, Sub, Sub).

%!  compose(+Substitution1, +Substitution2, ?SubstitutionOut)
%
%   This predicate composes both substitutions, Substitution1 and Substitution2
%   in SubstitutionOut.

compose(Sub0, Sub1, Sub2) :-
    map_assoc(apply(Sub1), Sub0, Sub2).

%!  apply(+Substitution, +ExpressionIn, ?ExpressionOut)
%
% This predicate applies the substitution Substitution to the expression
% ExpressionIn. ExpressionOut is the resulting expression.

apply(_, X, X) :-
    var(X),
    !.
apply(Sub, term(T,Args), term(T,Args_)) :-
    !,
    apply(Sub, Args, Args_).
apply(Sub, var(X), Y) :-
    !,
    (get_assoc(X, Sub, Y) ->
        true ;
        Y = var(X)).
apply(Sub, [X|Xs], [Y|Ys]) :-
    !,
    apply(Sub, X, Y),
    apply(Sub, Xs, Ys).
apply(_, X, X).

%!  fasill_print_substitution(+Substitution)
% 
%   This predicate writes a FASILL substitution Substitution for the standard
%   output.

% Bindings
fasill_print_substitution([]) :-
    !.
fasill_print_substitution([V-X|Xs]) :-
    write(', '),
    write(V),
    write('/'),
    fasill_term:fasill_print_term(X),
    fasill_print_substitution(Xs), !.
% Identity substitution
fasill_print_substitution(Sub) :-
    empty_substitution(Sub), !,
    write('{}').
% Non-empty substitution
fasill_print_substitution(Sub) :-
    substitution_to_list(Sub, [V-X|Xs]),
    write('{'),
    write(V),
    write('/'),
    fasill_term:fasill_print_term(X),
    fasill_print_substitution(Xs),
    write('}').