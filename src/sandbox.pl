/**
  * 
  * FILENAME: sandbox.pl
  * DESCRIPTION: This module contains predicates for the web interface.
  * AUTHORS: José Antonio Riaza Valverde
  * UPDATED: 03.05.2019
  * 
  **/



:- module(sandbox, [
    sandbox_run/6,
    sandbox_listing/1,
    sandbox_unfold/4,
    sandbox_tune/6,
    sandbox_tune_smt/8,
    sandbox_linearize_heads/1,
    sandbox_extend/4
]).

:- use_module('environment').
:- use_module('parser').
:- use_module('unfolding').
:- use_module('linearization').
:- use_module('tuning').
:- use_module('tuning_smt').



sandbox_write([]).
sandbox_write(level(0)).
sandbox_write(level(N)) :- N > 0, write('  '), M is N-1, sandbox_write(level(M)).
sandbox_write(trace(Level, Info, State)) :- sandbox_write(level(Level)), write(Info), write(' '), sandbox_write(State).
sandbox_write(rule(head(Head), empty)) :- !, sandbox_write(Head), write('.').
sandbox_write(rule(head(Head), body(Body))) :- !, sandbox_write(Head), write(' <- '), sandbox_write(Body), write('.').
sandbox_write(fasill_rule(head(Head), empty, [id(Id)|_])) :- !,
    write(Id), write(' '),
    sandbox_write(Head), write('.').
sandbox_write(fasill_rule(head(Head), body(Body), [id(Id)|_])) :- !,
    write(Id), write(' '),
    sandbox_write(Head), write(' <- '),
    sandbox_write(Body), write('.').
sandbox_write(symbolic_subs(Subs)) :- !, write('{'), sandbox_write(Subs), write('}').
sandbox_write(sym(Type1,Cons,Arity)/val(Type2,Name,Arity)) :- !,
    Types = [(td,''),(and,'&'),(or,'|'),(agr,'@'),(con,'?')],
    member((Type1,Op1), Types),
    member((Type2,Op2), Types),
    write('#'), write(Op1), write(Cons), write('/'), write(Op2),
    (Type1 = td -> sandbox_write(Name) ; write(Name)).
sandbox_write(top) :- write(top).
sandbox_write(bot) :- write(bot).
sandbox_write(num(X)) :- write(X).
sandbox_write(var(X)) :- write(X).
sandbox_write(X/Y) :- write(X), write('/'), sandbox_write(Y).
sandbox_write(term('#'(Name),[])) :- !, write('#'), write(Name).
sandbox_write(term('#@'(Name),Args)) :- !, write('#@'), write(Name), write('('), sandbox_write(Args), write(')').
sandbox_write(term('#&'(Name),[X,Y])) :- !, write('('), sandbox_write(X), write(' #&'), write(Name), write(' '), sandbox_write(Y), write(')'). 
sandbox_write(term('#|'(Name),[X,Y])) :- !, write('('), sandbox_write(X), write(' #|'), write(Name), write(' '), sandbox_write(Y), write(')'). 
sandbox_write(term('&'(Name),[X,Y])) :- !, write('('), sandbox_write(X), write(' &'), write(Name), write(' '), sandbox_write(Y), write(')'). 
sandbox_write(term('@'(Name),Xs)) :- !, write(@), write(Name), write('('), sandbox_write(Xs), write(')').
sandbox_write(term('|'(Name),[X,Y])) :- !, write('('), sandbox_write(X), write(' |'), write(Name), write(' '), sandbox_write(Y), write(')'). 
sandbox_write(term('.',[X,Y])) :- !, sandbox_write_list(list(term('.',[X,Y]))). 
sandbox_write(term(X,[])) :- escape_atom(X, X_), write(X_).
sandbox_write(term(X,Y)) :- Y \= [], escape_atom(X, X_), write(X_), write('('), sandbox_write(Y), write(')').
sandbox_write(exception(X)) :- write('uncaught exception in derivation: '), sandbox_write(X).
sandbox_write(state(Goal,Subs)) :-
    write('<'),
    sandbox_write(Goal),
    write(', {'),
    sandbox_write(Subs),
    write('}>').
sandbox_write([X|Y]) :-
    Y \= [],
    sandbox_write(X),
    write(', '),
    sandbox_write(Y).
sandbox_write([X]) :-
    sandbox_write(X).

sandbox_write_list(term('[]',[])) :- !.
sandbox_write_list(term([],[])) :- !.
sandbox_write_list(term('.',[X,Y])) :- !,
    write(','), sandbox_write(X), sandbox_write_list(Y).
sandbox_write_list(list(term('.',[X,Y]))) :- !,
    write('['), sandbox_write(X), sandbox_write_list(Y), write(']').
sandbox_write_list(X) :- write('|'), sandbox_write(X).

% sandbox_run/6
% sandbox_run(+Program, +Lattice, +Sim, +Goal, +Limit, +Options)
% 
% This predicate loads the program <+Program, +Lattice, +Sim>
% into the environment and runs the goal +Goal, with a limit
% of derivations +Limit, and writes in the standard output
% the resulting derivations.
sandbox_run(Program, Lattice, Sim, Goal, Limit, Options) :-
    set_fasill_flag(trace, term(true,[])),
    set_fasill_flag(max_inferences, num(Limit)),
    (member(cut(LambdaPl), Options) ->
        from_prolog(LambdaPl, Lambda), set_fasill_flag(lambda_unification, Lambda);
        true),
    lattice_consult(Lattice),
    catch(program_consult(Program), Error1, (write('uncaught exception in program: '), sandbox_write(Error1), nl)),
    catch(similarity_consult(Sim), Error2, (write('uncaught exception in similarities: '), sandbox_write(Error2), nl)),
    statistics(runtime,[_,_]),
    ( catch(query_consult(Goal, State), Error3, (write('uncaught exception in goal: '), sandbox_write(Error3), nl)),
      sandbox_write(State), nl, fail ; true ),
    statistics(runtime,[_,T1]),
    (member(runtime, Options) -> (write('execution time: '), write(T1), writeln(' milliseconds')) ; true),
    nl,
    ( semantics:trace_derivation(Trace),
      sandbox_write(Trace), nl, fail ; true).

% sandbox_listing/1
% sandbox_listing(+Program)
% 
% This predicate loads the program +Program
% into the environemnt, and writes in the
% standard output the loaded rules.
sandbox_listing(Program) :-
    catch(program_consult(Program), Error1, (write('uncaught exception in program: '), sandbox_write(Error1), nl)),
    ( fasill_rule(Head, Body, Info),
      sandbox_write(fasill_rule(Head, Body, Info)),
      nl, fail ; true).

% sandbox_unfold/4
% sandbox_unfold(+Program, +Lattice, +Sim, +Rule)
% 
% This predicate loads the program <+Program, +Lattice, +Sim>
% into the environemnt and runs the unfolding of the rule +Rule.
sandbox_unfold(Program, Lattice, Sim, Rule) :-
    lattice_consult(Lattice),
    catch(program_consult(Program), Error1, (write('uncaught exception in program: '), sandbox_write(Error1), nl)),
    catch(similarity_consult(Sim), Error2, (write('uncaught exception in similarities: '), sandbox_write(Error2), nl)),
    unfold_by_id(Rule),
    ( fasill_rule(Head, Body, _),
      sandbox_write(rule(Head, Body)),
      nl, fail ; true).

% sandbox_tune/6
% sandbox_tune(+Program, +Lattice, +Sim, +Tests, +Limit, +Options)
% 
% This predicate loads the program <+Program, +Lattice, +Sim>
% into the environment and tune the program w.r.t. the set
% of test cases +Tests, with a limit of derivations +Limit,
% and writes in the standard output the resulting substitution.
sandbox_tune(Program, Lattice, Sim, Tests, Limit, Options) :-
    set_fasill_flag(max_inferences, num(Limit)),
    (member(cut(LambdaPl), Options) ->
        from_prolog(LambdaPl, Lambda), set_fasill_flag(lambda_unification, Lambda);
        true),
    lattice_consult(Lattice),
    catch(program_consult(Program), Error1, (write('uncaught exception in program: '), sandbox_write(Error1), nl)),
    catch(testcases_consult(Tests), Error2, (write('uncaught exception in testcases: '), sandbox_write(Error2), nl)),
    catch(similarity_consult(Sim), Error3, (write('uncaught exception in similarities: '), sandbox_write(Error3), nl)),
    statistics(runtime,[_,_]),
    tuning_thresholded(Subs, Deviation),
    statistics(runtime,[_,T1]),
    write('best symbolic substitution: '),
    sandbox_write(symbolic_subs(Subs)), nl,
    write('deviation: '), write(Deviation),
    (member(runtime, Options) -> (nl, write('execution time: '), write(T1), write(' milliseconds')) ; true).

% sandbox_tune_smt/8
% sandbox_tune_smt(+Program, +Lattice, +Sim, +Tests, +Domain, +Limit, +Options)
% 
% This predicate loads the program <+Program, +Lattice, +Sim>
% into the environment and tune the program w.r.t. the set
% of test cases +Tests, using an SMT solver with theory of +Domain,
% with a limit of derivations +Limit, and writes in the standard
% output the resulting substitution.
sandbox_tune_smt(Program, Lattice, Sim, Tests, Domain, LatticeSMT, Limit, Options) :-
    set_fasill_flag(max_inferences, num(Limit)),
    (member(cut(LambdaPl), Options) ->
        from_prolog(LambdaPl, Lambda), set_fasill_flag(lambda_unification, Lambda);
        true),
    lattice_consult(Lattice),
    catch(program_consult(Program), Error1, (write('uncaught exception in program: '), sandbox_write(Error1), nl)),
    testcases_consult(Tests),
    catch(similarity_consult(Sim), Error2, (write('uncaught exception in similarities: '), sandbox_write(Error2), nl)),
    statistics(runtime,[_,_]),
    tuning_smt(Domain, LatticeSMT, Subs, Deviation),
    statistics(runtime,[_,T1]),
    write('best symbolic substitution: '),
    sandbox_write(symbolic_subs(Subs)), nl,
    write('deviation: '), write(Deviation),
    (member(runtime, Options) -> (nl, write('execution time: '), write(T1), write(' milliseconds')) ; true).

% sandbox_linearize_heads/1
% sandbox_linearize_heads(+Program)
% 
% This predicate loads the program +Program
% into the environemnt, and writes in the
% standard output the loaded rules after
% linearizing the heads.
sandbox_linearize_heads(Program) :-
    program_consult(Program),
    linearize_head_program,
    ( fasill_rule(Head, Body, _),
      sandbox_write(rule(Head, Body)),
      nl, fail ; true).

% sandbox_extend/4
% sandbox_extend(+Program, +Lattice, +Sim, +Options)
% 
% This predicate loads the program <+Program, +Lattice, +Sim>
% into the environemnt, and writes in the standard output the
% loaded rules after extending the program.
sandbox_extend(Program, Lattice, Sim, Options) :-
    (member(cut(LambdaPl), Options) ->
        from_prolog(LambdaPl, Lambda), set_fasill_flag(lambda_unification, Lambda);
        true),
    lattice_consult(Lattice),
    program_consult(Program),
    catch(similarity_consult(Sim), Error, (write('uncaught exception in similarities: '), sandbox_write(Error), nl)),
    extend_program,
    ( fasill_rule(Head, Body, _),
      sandbox_write(rule(Head, Body)),
      nl, fail ; true).