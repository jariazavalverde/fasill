/**
  * 
  * FILENAME: exceptions.pl
  * DESCRIPTION: This module contains predicates for manipulating errors.
  * AUTHORS: José Antonio Riaza Valverde
  * UPDATED: 02.05.2018
  * 
  **/



:- module(exceptions, [
    throw_exception/1,
    instantiation_error/2,
    type_error/4,
    evaluation_error/3,
    existence_error/4,
    domain_error/3,
    syntax_error/4
]).

:- use_module('environment').



% HANDLE EXCEPTIONS

% throw_exception/1
% throw_exception(+Exception)
%
% This predicate throws the exception +Exception.
throw_exception(Exception) :- retractall(semantics:check_success), throw(Exception).



% FORMAT ERRORS

% instantiation_error/2
% instantiation_error(+Indicator, ?Error)
%
% This predicate succeeds when ?Error is the instantiation
% error produced by the predicate +Indicator. This error
% is produced when an argument or one of its components
% is a variable, and an instantiated argument or component
% is required.
instantiation_error(Indicator, term(error, [term(instantiation_error,[]), Indicator_])) :-
    from_prolog(Indicator, Indicator_).

% type_error/4
% type_error(+Type, +Term, +Indicator, ?Error)
%
% This predicate succeeds when ?Error is the type error
% produced by the type +Type of the term +Term in the
% predicate +Indicator. This error is produced when the
% type of an argument or of one of its components is
% incorrect, but not a variable.
type_error(Type, Term, Indicator, term(error, [term(type_error, [Type_, Term]), Indicator_])) :-
    from_prolog(Type, Type_),
    from_prolog(Indicator, Indicator_).

% evaluation_error/3
% evaluation_error(+Cause, +Indicator, ?Error)
%
% This predicate succeeds when ?Error is the evaluation
% error produced by the cause +Cause in the predicate
% +Indicator. This error is produced when the operands
% of an evaluable functor has an exceptional value. 
evaluation_error(Cause, Indicator, term(error, [term(evaluation_error,[Cause_]), Indicator_])) :-
    from_prolog(Cause, Cause_),
    from_prolog(Indicator, Indicator_).

% existence_error/4
% existence_error(+Cause, +Term, +Indicator, ?Error)
%
% This predicate succeeds when ?Error is the existence
% error produced by the term +Term in the predicate
% +Indicator. This error is produced when the object
% on which an operation is to be performed does not exist. 
existence_error(Cause, Term, Indicator, term(error, [term(existence_error,[Cause_,Term_]), Indicator_])) :-
    from_prolog(Cause, Cause_),
    from_prolog(Term, Term_),
    from_prolog(Indicator, Indicator_).

% domain_error/3
% domain_error(+Domain, +Indicator, ?Error)
%
% This predicate succeeds when ?Error is the domain
% error produced by the term +Term in the predicate
% +Indicator.
domain_error(Domain, Indicator, term(error, [term(domain_error,[Domain_]), Indicator_])) :-
    from_prolog(Domain, Domain_),
    from_prolog(Indicator, Indicator_).

% syntax_error/3
% syntax_error(+Line, +Columns, +Message, ?Error)
%
% This predicate succeeds when ?Error is the syntax
% error produced in line +Line and Column +Column
% with message +Message.
syntax_error(Line, Column, Message, term(error, [term(syntax_error,[Line_, Column_, Message_])])) :-
    from_prolog(line(Line), Line_),
    from_prolog(column(Column), Column_),
    from_prolog(message(Message), Message_).