/**
  * 
  * FILENAME: directives.pl
  * DESCRIPTION: This module contains the definition of the FASILL directives.
  * AUTHORS: José Antonio Riaza Valverde
  * UPDATED: 13.12.2018
  * 
  **/



:- module(directives, [
    is_directive/1,
    eval_directive/2
]).

:- use_module('environment').
:- use_module('exceptions').



% is_directive/1
% is_directive(?Indicator)
%
% This predicate succeeds when ?Indicator is the
% indicator of a directive of FASILL. An indicator
% is a term of the form Name/Arity, where Name is an atom
% and Arity is a non-negative integer.
is_directive(Name/Arity) :-
    member(Name/Arity, [
        set_fasill_flag/2
    ]).



% eval_directive/2
% eval_directive(+Indicator, +Directive)
%
% This predicate succeeds when +Indicator is the
% indicator of a directive of FASILL, and +Directive
% is a FASILL term.

%%% set_fasill_flag/2
%%% set_fasill_flag( +atom, +term )
%%%
%%% set_fasill_flag(Flag, Value) sets the value of the Flag to Value.
eval_directive(set_fasill_flag/2, term(set_fasill_flag, [Flag,Value])) :-
    ((\+fasill_ground(Flag) ; \+fasill_ground(Value) ) -> instantiation_error(set_fasill_flag/2, Error), throw_error(Error) ;
     (\+fasill_atom(Flag) -> type_error(Flag, atom, set_fasill_flag/2), throw_error(Error) ;
     (\+current_fasill_flag(Flag, _) -> domain_error(fasill_flag, set_fasill_flag/2) ; 
     (\+is_fasill_flag_value(Flag, Value) -> domain_error(flag_value+(Flag,Value), set_fasill_flag/2) ; 
     set_fasill_flag(Flag, Value)
    )))).