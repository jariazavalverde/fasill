:- module(exceptions, [
    throw_exception/1,
    instantiation_error/2,
    type_error/4
]).



% HANDLE EXCEPTIONS

% throw_exception/1
% throw_exception(+Exception)
%
% This predicate throws the exception +Exception.
throw_exception(Exception) :- throw(Exception).



% FORMAT ERRORS

% instantiation_error/2
% instantiation_error(+Indicator, ?Error)
%
% This predicate succeeds when ?Error is the instantiation
% error produced by the predicate +Indicator. This error
% is produced when an argument or one of its components
% is a variable, and an instantiated argument or component
% is required.
instantiation_error(Indicator, error(instantiation_error, Indicator)).

% type_error/4
% type_error(+Type, +Term, +Indicator, ?Error)
%
% This predicate succeeds when ?Error is the type error
% produced by the type +Type of the term +Term in the
% predicate +Indicator. This error is produced when the
% type of an argument or of one of its components is
% incorrect, but not a variable.
type_error(Type, Term, Indicator, error(type_error(Type, Term), Indicator)).