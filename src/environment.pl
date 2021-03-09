/**
  * 
  * FILENAME: environment.pl
  * DESCRIPTION: This module contains predicates for manipulating programs, lattices and similarity relations.
  * AUTHORS: José Antonio Riaza Valverde
  * UPDATED: 09.09.2020
  * 
  **/



:- module(environment, [
    to_prolog/2,
    to_prolog_list/2,
    from_prolog/2,
    from_prolog_list/2,
    current_fasill_flag/2,
    is_fasill_flag_value/2,
    set_fasill_flag/2,
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
    fasill_rule/3,
    fasill_testcase/2,
    fasill_show/1,
    fasill_show/2,
    program_clause/2,
    program_rule_id/2,
    program_consult/1,
    program_import_prolog/1,
    program_has_predicate/1,
    query_consult/2,
    sort_rules_by_id/0,
    max_variable/3,
    count_variables/2,
    lattice_tnorm/1,
    lattice_tconorm/1,
    lattice_call_bot/1,
    lattice_call_top/1,
    lattice_call_member/1,
    lattice_call_members/1,
    lattice_call_members/2,
    lattice_call_exclude/1,
    lattice_call_leq/2,
    lattice_call_distance/3,
    lattice_call_connective/3,
    lattice_reduce_connective/3,
    lattice_consult/1,
    similarity_tnorm/1,
    similarity_between/5,
    similarity_consult/1,
    testcases_consult/1,
    fasill_testcase/2,
    fasill_testcase_precondition/1
]).

:- use_module(library(assoc)).
:- use_module(parser).
:- use_module(exceptions).
:- use_module(semantics).

:- dynamic
    fasill_rule/3,
    fasill_testcase/2,
    fasill_testcase_precondition/1,
    fasill_predicate/1,
    fasill_lattice_tnorm/1,
    fasill_similarity_tnorm/1,
    fasill_similarity_tconorm/1,
    fasill_similarity/4,
    fasill_warning/1,
    current_lattice_top/1,
    current_lattice_bot/1.



% FLAGS

% fasill_flag/3
% fasill_flag(?Flag, ?PossibleValues, ?CurrentValue)
%
% This predicate succeeds when ?Flag is a FASILL flag,
% that can take the serie of values ?PossibleValues and
% with ?CurrentValue as the current value in the environment.
:- dynamic(fasill_flag/3).
fasill_flag(trace, [term(false,[]), term(true,[])], term(false,[])).
fasill_flag(weak_unification, [term(false,[]), term(true,[])], term(true,[])).
fasill_flag(quoted_chars, [term(chars,[]), term(codes,[]), term(atom,[])], term(chars,[])).
fasill_flag(unknown, [term(error,[]), term(fail,[]), term(warning,[])], term(error,[])).
fasill_flag(occurs_check, [term(false,[]), term(true,[])], term(false,[])).
fasill_flag(max_inferences, [term(false,[]), num(_)], term(false,[])).
fasill_flag(symbolic, [term(false,[]), term(true,[])], term(true,[])).
fasill_flag(failure_steps, [term(false,[]), term(true,[])], term(true,[])).
fasill_flag(interpretive_steps, [term(short,[]), term(long,[])], term(short,[])).
fasill_flag(simplification_steps, [term(false,[]), term(true,[])], term(false,[])).
fasill_flag(lambda_unification, [_], bot).
fasill_flag(operators, [term(false,[]), term(true,[])], term(true,[])).

% current_fasill_flag/2
% current_fasill_flag(?Flag, ?Value)
%
% This predicate succeeds when ?Flag is a FASILL flag,
% and ?Value is the current value of the flag in the
% environment.
current_fasill_flag(Flag, Value) :- fasill_flag(Flag, _, Value).

% is_fasill_flag_value/2
% is_fasill_flag_value(+Flag, +Value)
%
% This predicate succeeds when +Flag is a FASILL flag
% and +Value is a possible value for the flag.
is_fasill_flag_value(Flag, Value) :-
    atomic(Flag), nonvar(Value),
    fasill_flag(Flag, Values, _),
    is_list(Values), !,
    member(Value, Values), !.
is_fasill_flag_value(Flag, Value) :-
    atomic(Flag), nonvar(Value),
    fasill_flag(Flag, td, _), !,
    (Value == bot ; Value == top ; lattice_call_member(Value)), !.

% set_fasill_flag/2
% set_fasill_flag(+Flag, +Value)
%
% This predicate succeeds when +Flag is a FASILL flag
% and +Value is a possible value for the flag. This predicate
% has the side effect of changing the current value for the flag.
set_fasill_flag(Flag, Value) :-
    atomic(Flag), nonvar(Value),
    is_fasill_flag_value(Flag, Value),
    fasill_flag(Flag, Values, _),
    retractall(fasill_flag(Flag, _, _)),
    assertz(fasill_flag(Flag, Values, Value)).



% OBJECT MANIPULATION

% to_prolog/2
% to_prolog(+FASILL, ?Prolog)
%
% This predicate takes the FASILL object +FASILL
% and returns the object ?Prolog in Prolog notation.
to_prolog(num(X), X) :- !.
to_prolog(var(_), _) :- !.
to_prolog(term('[]',[]), []) :- !.
to_prolog(term('.',[X,Y]), [X_|Y_]) :- !,
    to_prolog(X, X_),
    to_prolog(Y, Y_).
to_prolog(term(X,Xs), Term) :-
    atom(X), !,
    maplist(to_prolog, Xs, Ys),
    Term =.. [X|Ys].

% from_prolog/2
% from_prolog(+Prolog, ?FASILL)
%
% This predicate takes the Prolog object +Prolog
% and returns the object ?FASILL in FASILL notation.
from_prolog(X, var(X)) :- var(X), !.
from_prolog(X, num(X)) :- number(X), !.
from_prolog(X, term(X, [])) :- atom(X), !.
from_prolog([], term('[]', [])) :- !.
from_prolog([X|Xs], term('.', [Y,Ys])) :-
    !, from_prolog(X,Y),
    from_prolog(Xs,Ys).
from_prolog(X, term(H,Args)) :-
    compound(X), !,
    X =.. [H|T],
    maplist(from_prolog, T, Args).

% to_prolog_list/2
% to_prolog_list(+FASILL, ?Prolog)
%
% This predicate takes the FASILL list +FASILL
% and returns the list ?Prolog in Prolog notation.
to_prolog_list(term('[]', []), []).
to_prolog_list(term('.',[H,S]), [H|T]) :- to_prolog_list(S, T).

% from_prolog_list/2
% from_prolog_list(+Prolog, ?FASILL)
%
% This predicate takes the Prolog list +Prolog
% and returns the list ?FASILL in FASILL notation.
from_prolog_list([], term('[]', [])).
from_prolog_list([H|T], term('.',[H,S])) :- from_prolog_list(T, S).

% fasill_number/1
% fasill_number(+Term)
%
% This predicate succeeds when +Term is a FASILL number.
fasill_number(num(_)).

% fasill_integer/1
% fasill_integer(+Term)
%
% This predicate succeeds when +Term is a FASILL integer.
fasill_integer(num(X)) :- integer(X).

% fasill_float/1
% fasill_float(+Term)
%
% This predicate succeeds when +Term is a FASILL float.
fasill_float(num(X)) :- float(X).

% fasill_atom/1
% fasill_atom(+Term)
%
% This predicate succeeds when +Term is a FASILL atom.
fasill_atom(term(_,[])).

% fasill_term/1
% fasill_term(+Term)
%
% This predicate succeeds when +Term is a FASILL term.
fasill_term(term(_,_)).

% fasill_var/1
% fasill_var(+Term)
%
% This predicate succeeds when +Term is a FASILL variable.
fasill_var(var(_)).

% fasill_ground/1
% fasill_ground(+Term)
%
% This predicate succeeds when +Term is a FASILL ground term.
fasill_ground(num(_)).
fasill_ground(str(_)).
fasill_ground(term(_,Xs)) :- maplist(fasill_ground, Xs).

% fasill_callable/1
% fasill_callable(+Term)
%
% This predicate succeeds when +Term is a callable term.
fasill_callable(term(_, _)) :- !.
fasill_callable(X) :- lattice_call_member(X).

% fasill_list/1
% fasill_list(+Term)
%
% This predicate succeeds when +Term is a list or variable.
fasill_list(term('[]',[])) :- !.
fasill_list(var(_)) :- !.
fasill_list(term('.',[_,T])) :- fasill_list(T).

% fasill_connective/1
% fasill_connective(+Term)
%
% This predicate succeeds when +Term is a connective.
fasill_connective(term(Type,Arg)) :-
    (Type = '&' ; Type = '|' ; Type = '@'),
    (Arg = [] ; Arg = [_]).

% fasill_show/2
% fasill_show(+Term, ?Representation)
%
% This predicate succeeds when +Term is a valid FASILL term
% and ?Representation is the Prolog term which represent the
% literal FASILL term +Term.
fasill_show(Term, Output) :- with_output_to(atom(Output), fasill_show(Term)).

fasill_show([]) :- !.
fasill_show(X) :- is_assoc(X), !, assoc_to_list(X, Subs), fasill_show(Subs).
fasill_show(top) :- write(top).
fasill_show(bot) :- write(bot).
fasill_show(sup(X, Y)) :- write('sup('), fasill_show(X), write(', '), fasill_show(Y), write(')').
fasill_show(num(X)) :- write(X).
fasill_show(var('$'(X))) :- !, write('V'), write(X).
fasill_show(var(X)) :- write(X).
fasill_show(X-Y) :- write(X), write('/'), fasill_show(Y).
fasill_show(X/Y) :- write(X), write('/'), fasill_show(Y).
fasill_show(term('#'(Name),[])) :- !, write('#'), write(Name).
fasill_show(term('#@'(Name),Args)) :- !, write('#@'), write(Name), write('('), fasill_show(Args), write(')').
fasill_show(term('#&'(Name),[X,Y])) :- !, write('('), fasill_show(X), write(' #&'), write(Name), write(' '), fasill_show(Y), write(')'). 
fasill_show(term('#|'(Name),[X,Y])) :- !, write('('), fasill_show(X), write(' #|'), write(Name), write(' '), fasill_show(Y), write(')'). 
fasill_show(term('&'(Name),[X,Y])) :- !, write('('), fasill_show(X), write(' &'), write(Name), write(' '), fasill_show(Y), write(')'). 
fasill_show(term('|'(Name),[X,Y])) :- !, write('('), fasill_show(X), write(' |'), write(Name), write(' '), fasill_show(Y), write(')'). 
fasill_show(term('.',[X,Y])) :- !, fasill_show_list(list(term('.',[X,Y]))). 
fasill_show(term(X,[])) :- write(X).
fasill_show(term(X,Y)) :- Y \= [], write(X), write('('), fasill_show(Y), write(')').
fasill_show(exception(X)) :- write('uncaught exception in derivation: '), fasill_show(X).
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

fasill_show_list(term('[]',[])) :- !.
fasill_show_list(term([],[])) :- !.
fasill_show_list(term('.',[X,Y])) :- !,
    write(','), fasill_show(X), fasill_show_list(Y).
fasill_show_list(list(term('.',[X,Y]))) :- !,
    write('['), fasill_show(X), fasill_show_list(Y), write(']').
fasill_show_list(X) :- write('|'), fasill_show(X).



% RULES MANIPULATION

% program_clause/2
% program_clause(?Indicator, ?Rule)
%
%
program_clause(Name/Arity, fasill_rule(head(term(Name, Args)), Body, Info)) :-
    fasill_rule(head(term(Name, Args)), Body, Info),
    length(Args, Arity).

% program_rule_id/2
% program_rule_id(+Rule, ?Id)
%
% This predicate succeeds when ?Id is the identifier
% of the rule +Rule.
program_rule_id(fasill_rule(_,_,Info), Id) :- member(id(Id), Info).

% program_consult/1
% program_consult(+Path)
%
% This predicate loads the FASILL program from
% the file +Path into the environment. This
% predicate cleans the previous rules.
program_consult(Path) :-
    retractall(fasill_rule(_,_,_)),
    retractall(fasill_predicate(_)),
    file_program(Path, Rules),
    (   member(Rule, Rules),
        assertz(Rule),
        Rule = fasill_rule(head(term(Name,Args)),_,_),
        length(Args,Arity),
        (catch(fasill_predicate(Name/Arity), _, fail) -> true ; assertz(fasill_predicate(Name/Arity))),
        fail ; true).

% program_import_prolog/1
% program_import_prolog(+Path)
%
% This predicate loads the Prolog program from
% the file +Path into the environment. This
% predicate doesn't cleans the previous rules.
:- dynamic(last_prolog_id/1).
last_prolog_id(0).
program_import_prolog(Path) :-
    set_prolog_flag(double_quotes, atom),
    open(Path, read, Stream),
    once(program_import_prolog_(Stream)).
program_import_prolog_(Stream) :-
    read(Stream, PrologTerm),
    PrologTerm \= end_of_file,
    from_prolog(PrologTerm, FasillTerm),
    (FasillTerm = term(':-', [Head,Body_]) -> Body = body(Body_) ; Head = FasillTerm, Body = empty),
    last_prolog_id(N),
    succ(N, M),
    retractall(last_prolog_id(_)),
    asserta(last_prolog_id(M)),
    atom_number(A, N),
    atom_concat('Pr', A, Id),
    Rule = fasill_rule(head(Head), Body, [id(Id), syntax(prolog)]),
    Head = term(Name, Args),
    assertz(Rule),
    length(Args, Arity),
    (catch(fasill_predicate(Name/Arity), _, fail) -> true ; assertz(fasill_predicate(Name/Arity))),
    program_import_prolog_(Stream).
program_import_prolog_(Stream) :-
    close(Stream).


% query_consult/2
% program_consult(+Path, ?State)
%
% This predicate loads the FASILL goal from the
% file +Path into the environment and runs it.
query_consult(Path, State) :-
    file_query(Path, Query),
    query(Query, State).

% program_has_predicate/1
% program_has_predicate(?Indicator)
%
% This predicate succeeds when ?Indicator is the indicator
% of a predicate asserted in the program loaded in the current
% environment.
program_has_predicate(Name/Arity) :-
    (fasill_predicate(Name/Arity) ;
    lattice_call_bot(Bot),
    similarity_between(Name, Other, Arity, TD, _),
    TD \= Bot,
    fasill_predicate(Other/Arity)), !.

% sort_rules_by_id/0
% sort_rules_by_id
%
% This predicate retracts all the rules from the current
% environment and asserts them ordered by the identifier.
sort_rules_by_id :-
    findall(fasill_rule(X,Y,Z), fasill_rule(X,Y,Z), Rules),
    predsort(compare_rule_id, Rules, Sorted),
    retractall(fasill_rule(_,_,_)),
    ( member(Rule, Sorted),
      assertz(Rule),
      fail ; true ).

% count_variables/2
% count_variables(+Expression, ?Variables)
%
% This predicate succeeds when ?Variables is a 
% list of pairs (Var-N) where Var is a varaible
% and N is the number of occurrences of Var in 
% the expression +Expression.
count_variables(Expr, Vars) :-
    count_variables(Expr, [], Vars).
count_variables(var(X), Vars, [X-1|Vars]) :- \+member(X-_, Vars), !.
count_variables(var(X), Vars, [X-M|Vars2]) :- !, select(X-N, Vars, Vars2), succ(N, M).
count_variables(term(_, Xs), Vars, Vars2) :- !,
    count_variables(Xs, Vars, Vars2).
count_variables([], Vars, Vars) :- !.
count_variables([X|Xs], Vars, Vars3) :- !,
    count_variables(X, Vars, Vars2),
    count_variables(Xs, Vars2, Vars3).
count_variables(_, Vars, Vars).

% max_variable/3
% max_variable(+Expression, +Variable, ?Max)
%
% This predicate succeeds when ?Max is the maximum
% natural number for wich +Variable?Max occurs in
% the expression +Expression.
max_variable(Expr, Variable, Max) :-
    max_variable(Expr, Variable, 0, Max).
max_variable(var(V), Variable, N, Max) :-
    atom(V),
    atom_length(Variable, Length),
    sub_atom(V, 0, Length, _, Variable), !,
    sub_atom(V, Length, _, 0, Rest),
    atom_codes(Rest, Codes),
    catch((number_codes(M, Codes), Max is max(N,M)), _, Max = N).
max_variable(term(_, Xs), Variable, N, Max) :- !,
    max_variable(Xs, Variable, N, Max).
max_variable([], _, N, N) :- !.
max_variable([X|Xs], Variable, N, Max) :- !,
    max_variable(X, Variable, N, M),
    max_variable(Xs, Variable, M, Max).
max_variable(_, _, N, N).

% compare_rule_id/3
% compare_rule_id(?Delta, +Rule1, +Rule2)
%
% This predicate succeeds when ?Delta is the ordering relation
% (<, > or =) for rules +Rule1 and +Rule2, compared by their
% identifiers.
compare_rule_id(Delta, X, Y) :-
    X = fasill_rule(_,_,[id(IdX)|_]),
    Y = fasill_rule(_,_,[id(IdY)|_]),
    atomic_list_concat(Xs, '-', IdX),
    atomic_list_concat(Ys, '-', IdY),
    maplist(atom_number, Xs, Xs_),
    maplist(atom_number, Ys, Ys_),
    compare(Delta, Xs_, Ys_).



% LATTICES

% lattice_tnorm/1
% lattice_tnorm(?Tnorm)
%
% This predicate succeeds when ?Tnorm is the
% current t-norm asserted in the environment.
lattice_tnorm(Tnorm) :- catch(tnorm(Tnorm), _, fail), !.
lattice_tnorm(Tnorm) :-
    current_predicate(Name/3),
    atom_concat(and_, Tnorm, Name), !.
lattice_tnorm(Tnorm) :-
    atom_concat(and_, Tnorm, Name),
    existence_error(procedure, Name/3, lattice/0, Error),
    throw_exception(Error).

% lattice_tconorm/1
% lattice_tconorm(?Tconorm)
%
% This predicate succeeds when ?Tconorm is the
% current t-conorm asserted in the environment.
lattice_tconorm(Tconorm) :- catch(tconorm(Tconorm), _, fail), !.
lattice_tconorm(Tconorm) :-
    current_predicate(Name/3),
    atom_concat(or_, Tconorm, Name), !.
lattice_tconorm(Tconorm) :-
    atom_concat(or_, Tconorm, Name),
    existence_error(procedure, Name/3, lattice/0, Error),
    throw_exception(Error).

% lattice_call_bot/1
% lattice_call_bot(-Bot)
%
% This predicate succeeds when -Bot is the
% bottom member of the lattice loaded into
% the environment.
:- dynamic(current_lattice_bot/1).
lattice_call_bot(Bot) :-
    current_lattice_bot(Bot), !.
lattice_call_bot(Bot) :-
    current_predicate(bot/1), !,
    bot(Prolog),
    from_prolog(Prolog, Bot),
    asserta(current_lattice_bot(Bot)).
lattice_call_bot(_) :-
    existence_error(procedure, bot/1, lattice/0, Error),
    throw_exception(Error).

% lattice_call_top/1
% lattice_call_top(-Bot)
%
% This predicate succeeds when -Bot is the
% bottom member of the lattice loaded into
% the environment.
:- dynamic(current_lattice_top/1).
lattice_call_top(Top) :-
    current_lattice_top(Top), !.
lattice_call_top(Top) :-
    current_predicate(top/1), !,
    top(Prolog),
    from_prolog(Prolog, Top),
    asserta(current_lattice_top(Top)).
lattice_call_top(_) :-
    existence_error(procedure, top/1, lattice/0, Error),
    throw_exception(Error).

% lattice_call_member/1
% lattice_call_member(+Member)
%
% This predicate succeeds when +Member is a member
% of the lattice loaded into the environment.
lattice_call_member(Member) :-
    current_predicate(member/1), !,
    to_prolog(Member, Prolog),
    member(Prolog).
lattice_call_member(_) :-
    existence_error(procedure, member/1, lattice/0, Error),
    throw_exception(Error).

% lattice_call_members/1
% lattice_call_members(-Members)
%
% This predicate succeeds when -Members is a list of
% members of the lattice loaded into the environment.
lattice_call_members(Members) :-
    current_predicate(members/1), !,
    members(Prolog),
    maplist(from_prolog, Prolog, Members).
lattice_call_members(_) :-
    existence_error(procedure, members/1, lattice/0, Error),
    throw_exception(Error).

% lattice_call_members/2
% lattice_call_members(+Constant, -Members)
%
% This predicate succeeds when -Members is a list of
% members for a symbolic constant Constant in the lattice
% loaded into the environment.
lattice_call_members(Constant, Members) :-
    current_predicate(members/2),
    members(Constant, Prolog),
    maplist(from_prolog, Prolog, Members), !.
lattice_call_members(_, Members) :- lattice_call_members(Members).

% lattice_call_exclude/1
% lattice_call_exclude(+Exclude)
%
% This predicate succeeds when -Exclude is a predicate indicator
% excluded (for tuning) in the lattice loaded into the environment.
lattice_call_exclude(Exclude) :-
    current_predicate(exclude/1),
    exclude(Exclude), !.

% lattice_call_leq/2
% lattice_call_leq(+Member1, +Member2)
%
% This predicate succeeds when +Member1 is less
% of equal than +Member2 with the lattice loaded
% into the environment.
lattice_call_leq(Member1, Member2) :-
    current_predicate(leq/2), !,
    to_prolog(Member1, Prolog1),
    to_prolog(Member2, Prolog2),
    leq(Prolog1, Prolog2).
lattice_call_leq(_, _) :-
    existence_error(procedure, leq/2, lattice/0, Error),
    throw_exception(Error).

% lattice_call_supremum/3
% lattice_call_supremum(+Member1, +Member2, -Supremum)
%
% This predicate succeeds when +Member1 and +Member2 are
% members of the lattice loaded into the environment, and
% -Supremum is the supremum of both.
lattice_call_supremum(Member1, Member2, Supremum) :-
    current_predicate(supremum/3), !,
    to_prolog(Member1, Prolog1),
    to_prolog(Member2, Prolog2),
    supremum(Prolog1, Prolog2, Prolog3),
    from_prolog(Prolog3, Supremum).
lattice_call_supremum(_, _, _) :-
    existence_error(procedure, supremum/3, lattice/0, Error),
    throw_exception(Error).

% lattice_call_distance/3
% lattice_call_distance(+Member1, +Member2, -Distance)
%
% This predicate succeeds when +Member1 and +Member2 are
% members of the lattice loaded into the environment, and
% -Distance is the distace between them.
lattice_call_distance(Member1, Member2, Distance) :-
    current_predicate(distance/3), !,
    lattice_call_member(Member1),
    lattice_call_member(Member2),
    to_prolog(Member1, Prolog1),
    to_prolog(Member2, Prolog2),
    distance(Prolog1, Prolog2, Prolog3),
    from_prolog(Prolog3, Distance).
lattice_call_distance(_, _, _) :-
    existence_error(procedure, distance/3, lattice/0, Error),
    throw_exception(Error).

% lattice_call_connective/3
% lattice_call_connective(+Name, +Arguments, ?Result)
%
% This predicate succeeds when ?Result is the result
% of evaluate the connective ?Name with the arguments
% +Arguments of the lattice loaded into the environment.
lattice_call_connective('&', Args, Result) :- !,
    lattice_tnorm(Name),
    lattice_call_connective('&'(Name), Args, Result).
lattice_call_connective('|', Args, Result) :- !,
    lattice_tconorm(Name),
    lattice_call_connective('|'(Name), Args, Result).
lattice_call_connective(Op, Args, Result) :-
    Op =.. [Type,Name], !,
    (   Type = '&', Pre = 'and_' ;
        Type = '|', Pre = 'or_' ;
        Type = '@', Pre = 'agr_'
    ),
    atom_concat(Pre, Name, Name_),
    lattice_call_connective2(Name_, Args, Result).
lattice_call_connective(Op, Args, Result) :-
    lattice_call_connective2(Op, Args, Result).
lattice_call_connective2(Name, Args, Result) :-
    length(Args, Arity),
    Arity_ is Arity + 1,
    (current_predicate(Name/Arity_) -> true ;
        existence_error(procedure, Name/Arity_, lattice/0, Error), throw_exception(Error)),
    maplist(to_prolog, Args, Args_),
    append(Args_, [Prolog], ArgsCall),
    Call =.. [Name|ArgsCall],
    call(environment:Call),
    from_prolog(Prolog, Result), !.

% lattice_reduce_connective/3
% lattice_reduce_connective(+Name, +TDs, ?Result)
%
% This predicate succeeds when ?Result is the resulting value of
% reducing a list of truth degrees +TDs applying the connective
% +Name loaded in the lattice in the current environment.
lattice_reduce_connective(_, [X], X) :- !.
lattice_reduce_connective(Op, [H|T], Result) :-
    !, lattice_reduce_connective(Op, T, Result_),
    lattice_call_connective(Op, [H,Result_], Result).
lattice_reduce_connective(_, [], Bot) :- lattice_call_bot(Bot).

% lattice_consult/1
% lattice_consult(+Path)
%
% This predicate loads the lattice of the file +Path into
% the environment. This predicate cleans the previous lattice.
lattice_consult(Path) :-
    abolish(member/1),
    abolish(members/1),
    abolish(distance/3),
    abolish(bot/1),
    abolish(top/1),
    abolish(leq/2),
    abolish(tnorm/1),
    abolish(tconorm/1),
    retractall(current_lattice_top(_)),
    retractall(current_lattice_bot(_)),
    ( current_predicate(X/3),
      ( atom_concat(and_, _, X) ;
        atom_concat(agr_, _, X) ;
        atom_concat(or_, _, X) ),
      abolish(X/3), fail ; true
    ),
    consult(Path).



% SIMILARITY RELATIONS



% similarity_tnorm/1, similarity_tconorm/1
% similarity_tnorm(?Tnorm)
% similarity_tconorm(?Tconorm)
%
% This predicate succeeds when ?Tnorm is the current
% t-norm asserted in the environment.
similarity_tnorm(Tnorm) :- fasill_similarity_tnorm(Tnorm), !.
similarity_tnorm('&'(Tnorm)) :- lattice_tnorm(Tnorm).
similarity_tconorm(Tconorm) :- fasill_similarity_tconorm(Tconorm), !.
similarity_tconorm('|'(Tconorm)) :- lattice_tconorm(Tconorm).

% similarity_between/5
% similarity_between(?AtomA, ?AtomB, ?Arity, ?TD, ?Sym)
%
% This predicate succeeds when ?AtomA/?Arity is similar
% to ?AtomB/?Arity with truth degree ?TD, using the current
% similarity relation in the environment.
similarity_between(AtomA, AtomB, Arity, TD, Sym) :-
    fasill_similarity(AtomA/Arity, AtomB/Arity, TD, Sym).
similarity_between(AtomA, AtomB, Arity, Bot, no) :-
    \+fasill_similarity(AtomA/Arity, AtomB/Arity, _, _),
    lattice_call_bot(Bot).

% similarity_retract/0
% similarity_retract
%
% This predicate succeeds and retracts all the clauses
% of similarity from the current environment.
similarity_retract :-
    retractall(fasill_similarity(_, _, _, _)),
    retractall(fasill_similarity_tnorm(_)),
    retractall(fasill_similarity_tconorm(_)).

% similarity_consult/1
% similarity_consult(+Path)
%
% This predicate loads the similarities equations of the
% file +Path into the environment. This predicate cleans
% the previous similarity relations.
similarity_consult(Path) :-
    similarity_retract,
    file_similarity(Path, Equations),
    (   member(Eq, Equations),
        assertz(Eq),
        fail ; true),
    similarity_closure.

% similarity_closure/0
% similarity_closure
%
% This predicate computes the reflexive, symmetric and 
% transitive closure of the similarity scheme asserted
% into the current environment.
similarity_closure :-
    setof(Atom/Arity, Atom2^TD^Sym^(
        similarity_between(Atom, Atom2, Arity, TD, Sym);
        similarity_between(Atom2, Atom, Arity, TD, Sym)
    ), Dom),
    findall(sim(Atom1,Atom2,Arity,TD,Sym), similarity_between(Atom1,Atom2,Arity,TD,Sym), Scheme),
    similarity_tnorm(Tnorm),
    lattice_call_bot(Bot),
    lattice_call_top(Top),
    similarity_retract,
    (similarity_closure_check_equations(Dom, Scheme), false ; true),
    (similarity_closure_reflexive(Dom, Scheme, Tnorm, Bot, Top), false ; true),
    (similarity_closure_symmetric(Dom, Scheme, Tnorm, Bot, Top), false ; true),
    (similarity_closure_transitive(Dom, Scheme, Tnorm, Bot, Top), false ; true),
    assertz(fasill_similarity_tnorm(Tnorm)).

similarity_closure_check_equations(Dom, Scheme) :-
    member(X/Arity, Dom),
    member(Y/Arity, Dom),
    X @< Y,
    setof(TD, Sym^(
        member(sim(X,Y,Arity,TD,Sym), Scheme);
        member(sim(Y,X,Arity,TD,Sym), Scheme)
    ), Set),
    length(Set, Length),
    from_prolog_list(Set, FSet),
    (Length > 1 -> throw_warning(term(warning, [term(conflicting_equations, [term('/', [term(X, []), num(Arity)]), term('/', [term(Y, []), num(Arity)]), FSet])]))).

similarity_closure_reflexive(Dom, _, _, _, Top) :-
    member(X/Arity, Dom),
    assertz(fasill_similarity(X/Arity,X/Arity,Top,no)).

similarity_closure_symmetric(Dom, Scheme, _, _, _) :-
    member(X/Arity, Dom),
    member(Y/Arity, Dom),
    \+(fasill_similarity(X/Arity,Y/Arity,_,_)),
    once(member(sim(X,Y,Arity,TD,Sym), Scheme) ; member(sim(Y,X,Arity,TD,Sym), Scheme)),
    assertz(fasill_similarity(X/Arity,Y/Arity,TD,Sym)),
    assertz(fasill_similarity(Y/Arity,X/Arity,TD,Sym)).

similarity_closure_transitive(Dom, _, Tnorm, Bot, Top) :-
    member(Y/Arity, Dom),
    member(X/Arity, Dom), X \= Y,
    member(Z/Arity, Dom), Z \= Y, X \= Z,
    once(fasill_similarity(X/Arity,Z/Arity,TDxz,Sxz) ; (TDxz = Bot, Sxz = no)),
    once(fasill_similarity(X/Arity,Y/Arity,TDxy,Sxy)),
    once(fasill_similarity(Y/Arity,Z/Arity,TDyz,Syz)),
    (TDxy == Top -> TDy = TDyz, Sy = Syz ;
        (TDyz == Top -> TDy = TDxy, Sy = Sxy ;
            ((Sxy == no, Syz == no, Tnorm = '&'(_)) ->
                (lattice_call_connective(Tnorm, [TDxy,TDyz], TDy), Sy = no) ;
                (TDy = term(Tnorm, [TDxy, TDyz]), Sy = yes)
            )
        )
    ),
    (TDxz == Bot -> TD = TDy, S = Sy ;
        (TDy == Bot -> TD = TDxz, S = Sxz ;
            ((Sxz == no, Sy == no, Tnorm = '&'(_)) ->
                (lattice_call_supremum(TDxz, TDy, TD), S = no) ;
                (TD = sup(TDxz, TDy), S = yes)
            )
        )
    ),
    retractall(fasill_similarity(X/Arity,Z/Arity,_,_)),
    assertz(fasill_similarity(X/Arity,Z/Arity,TD,S)).



% TEST CASES

% testcases_consult/1
% testcases_consult(+Path)
%
% This predicate loads the set of FASILL test cases
% from the file +Path into the environment. This
% predicate cleans the previous test cases.
testcases_consult(Path) :-
    retractall(fasill_testcase(_,_)),
    retractall(fasill_testcase_precondition(_)),
    file_testcases(Path, Tests),
    ( member(Test, Tests),
      assertz(Test),
      fail ; true ).