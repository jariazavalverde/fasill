/**
  * 
  * FILENAME: tuning_smt.pl
  * DESCRIPTION: This module contains predicates for tuning symbolic FASILL programs with the Z3 SMT solver.
  * AUTHORS: José Antonio Riaza Valverde
  * UPDATED: 17.11.2018
  * 
  **/



% LATTICE TO SMT

%
%
:- dynamic(prolog_to_smt_var/1).
prolog_to_smt_var(0).
prolog_to_smt_current_var(X) :-
    prolog_to_smt_var(X), Y is X+1,
    retractall(prolog_to_smt_var(_)), 
    asserta(prolog_to_smt_var(Y)).

lat_to_smt_aux(['define-fun','lat!aux!max',[['a!0','Real'],['a!1','Real']],'Real',[ite,['>=','a!0','a!1'],'a!0','a!1']]).
lat_to_smt_aux(['define-fun','lat!aux!min',[['a!0','Real'],['a!1','Real']],'Real',[ite,['<=','a!0','a!1'],'a!0','a!1']]).

%
%
prolog_to_smt_bool(',', and).
prolog_to_smt_bool(';', or).
prolog_to_smt_bool(=, =).
prolog_to_smt_bool(<, <).
prolog_to_smt_bool(>, >).
prolog_to_smt_bool(=<, <=).
prolog_to_smt_bool(>=, >=).

%
%
prolog_to_smt_op(P, [Name,Xs,Ys]) :-
    nonvar(P),
    P =.. [Name,X,Y],
    member(Name, [+,-,*,/,'^']), !,
    prolog_to_smt_op(X, Xs),
    prolog_to_smt_op(Y, Ys).
prolog_to_smt_op(max(X,Y), ['lat!aux!max',Xs,Ys]) :- !, prolog_to_smt_op(X, Xs), prolog_to_smt_op(Y, Ys).
prolog_to_smt_op(min(X,Y), ['lat!aux!min',Xs,Ys]) :- !, prolog_to_smt_op(X, Xs), prolog_to_smt_op(Y, Ys).
prolog_to_smt_op(abs(X), [abs,Xs]) :- !, prolog_to_smt_op(X, Xs).
prolog_to_smt_op(sqrt(X), ['^',Xs,0.5]) :- !, prolog_to_smt_op(X, Xs).
prolog_to_smt_op(X,X).

%
%
% boolean predicate
prolog_to_smt(','(Xp,Yp), [let, Expr, Ys], Var) :-
    prolog_to_smt(Xp, [let, Expr], Var), !,
    prolog_to_smt(Yp, Ys, Var).
prolog_to_smt(Prolog, [NameS,Xs,Ys], Var) :-
    Prolog =.. [NameP,Xp,Yp],
    atom(NameP),
    prolog_to_smt_bool(NameP, NameS), !,
    prolog_to_smt(Xp, Xs, Var),
    prolog_to_smt(Yp, Ys, Var).
% arithmetic predicate
prolog_to_smt(is(X,Y), Ys, var(Var)) :-
    X == Var, !,
    prolog_to_smt_op(Y, Ys).
prolog_to_smt(is(X,Y), [let, [[X, Ys]]], Var) :-
    (Var == nonvar ; var(X) \== Var), !,
    prolog_to_smt_current_var(VarNum),
    atom_number(VarAtom, VarNum),
    atom_concat('x!', VarAtom, X),
    prolog_to_smt_op(Y, Ys).
% type testing (always true, smt check types)
prolog_to_smt(Prolog, true, _) :-
    Prolog =.. [Name,_],
    member(Name, [number, atom, atomic, integer]), !.
% atomic or var
prolog_to_smt(X,X,_) :- atomic(X) ; var(X).

%
%
lat_member_to_smt(Domain, ['define-fun', 'lat!member', [['a!0', Domain]], 'Bool', Body]) :-
    clause(lat:member('a!0'), Clause),
    prolog_to_smt(Clause, Body, nonvar).

%
%
lat_members_to_smt(Domain, ['define-fun', 'lat!members', [['a!0', Domain]], 'Bool', ['or'|Body]]) :-
    lat:members(Xs),
    lat_members_body_to_smt(Xs, Body).

lat_members_body_to_smt([], []).
lat_members_body_to_smt([X|Xs], [['=', 'a!0', X]|Ys]) :- lat_members_body_to_smt(Xs, Ys).

%
%
lat_leq_to_smt(Domain, ['define-fun', 'lat!leq', [['a!0', Domain], ['a!1', Domain]], 'Bool', Body]) :-
    clause(lat:leq('a!0','a!1'), Clause),
    prolog_to_smt(Clause, Body, nonvar).

%
%
lat_distance_to_smt(Domain, ['define-fun', 'lat!distance', [['a!0', Domain], ['a!1', Domain]], 'Real', Body]) :-
    clause(lat:distance('a!0','a!1','a!2'), Clause),
    prolog_to_smt(Clause, Body, var('a!2')).

%
%
lat_connective_to_smt(Domain, ['define-fun', Name, SignatureArgs, Domain, Body]) :-
    current_predicate(lat:P/N),
    member((Prefix,Len),[(and_,4),(or_,3),(agr_,4)]),
    sub_atom(P, _, Len, _, Prefix),
    lat_arguments(N, Args),
    lat_signature_arguments(Domain, N, SignatureArgs),
    Connective =.. [P|Args],
    atom_concat('lat!', P, Name),
    clause(lat:Connective, Clause),
    M is N-1, atom_number(Atom,M), atom_concat('a!', M, Last),
    prolog_to_smt(Clause, Body, var(Last)).

lat_signature_arguments(Domain, N, Args) :- M is N-2, lat_signature_arguments(Domain, M, [], Args).
lat_signature_arguments(_, -1, Args, Args) :- !.
lat_signature_arguments(Domain, N, Current, Args) :- N >= 0, !, M is N-1, atom_number(Num, N), atom_concat('a!', Num, Var), lat_signature_arguments(Domain, M, [[Var, Domain]|Current], Args).

lat_arguments(N, Args) :- M is N-1, lat_arguments(M, [], Args).
lat_arguments(-1, Args, Args) :- !.
lat_arguments(N, Current, Args) :- N >= 0, !, M is N-1, atom_number(Num, N), atom_concat('a!', Num, Var), lat_arguments(M, [Var|Current], Args).


% PROLOG TO SMT

% quoted_atom/2
%
quoted_atom(X, Z) :-
    atom_concat('"', X, Y),
    atom_concat(Y, '"', Z).

% smt_symbols/[0,1]
% update the table of symbolic elements
smt_symbols :-
	retractall(tuning_sym(_,_,_)),
	findall(Leaf, leaf(Leaf), Bs),
	smt_symbols(Bs).
smt_symbols([]).
smt_symbols([X|Xs]) :-
	smt_symbols(X),
	smt_symbols(Xs).
smt_symbols(atom(_,Xs)) :- smt_symbols(Xs).
smt_symbols(term(_,Xs)) :- smt_symbols(Xs).
smt_symbols(and(_,_,Xs)) :- smt_symbols(Xs).
smt_symbols(or(_,_,Xs)) :- smt_symbols(Xs).
smt_symbols(agr(_,_,Xs)) :- smt_symbols(Xs).
smt_symbols(pri(_,_,Xs)) :- smt_symbols(Xs).
smt_symbols(sym(td(S))) :- tuning_sym(td,1,S), ! ; assertz(tuning_sym(td,1,S)).
smt_symbols(sym(P)) :- P=..[C,S,L,A], (tuning_sym(C,L,S), ! ; assertz(tuning_sym(C,L,S))), smt_symbols(A).
smt_symbols(_).

% tuning_connectives/4
% search the current connectives in the lattice
tuning_connectives(and, L, and, Ps, P) :- N is L+1, current_predicate(lat:P/N), sub_atom(P, _, 4, _, and_), sub_atom(P, 4, _, 0, Ps).
tuning_connectives(or, L, or, Ps, P) :- N is L+1, current_predicate(lat:P/N), sub_atom(P, _, 3, _, or_), sub_atom(P, 3, _, 0, Ps).
tuning_connectives(agr, L, agr, Ps, P) :- N is L+1, current_predicate(lat:P/N), sub_atom(P, _, 4, _, agr_), sub_atom(P, 4, _, 0, Ps).
tuning_connectives(con, L, C, Ps, P) :- tuning_connectives(and, L, C, Ps, P) ; tuning_connectives(or, L, C, Ps, P) ; tuning_connectives(agr, L, C, Ps, P).

% tuning_fn_eval/3
%
% agregators
tuning_fn_eval(Domain, agr, ['define-fun', Name, [[s, 'String']|SigArgs], Domain, Body]) :- !,
    setof(N, P^(current_predicate(lat:P/N), sub_atom(P, _, 4, _, agr_)), Arities),
    member(Arity, Arities),
    N is Arity-1,
    atom_number(Len, N),
    atom_concat('eval-agr!', Len, Name),
    lat_signature_arguments(Domain, Arity, SigArgs),
    lat_arguments(N, Args),
    findall(C, tuning_connectives(agr, N, _, _, C), Connectives),
    tuning_fn_eval_body(Connectives, Args, Body).
% t-norms and t-conorms
tuning_fn_eval(Domain, Type, ['define-fun', Name, [[s, 'String']|SigArgs], Domain, Body]) :-
    atom_concat('eval-', Type, Name),
    findall(C, tuning_connectives(Type, 2, _, _, C), Connectives),
    lat_signature_arguments(Domain, 3, SigArgs),
    lat_arguments(2, Args),
    tuning_fn_eval_body(Connectives, Args, Body).

% tuning_fn_eval_body/3
%
tuning_fn_eval_body([X], Args, [Xl|Args]) :- !, atom_concat('lat!', X, Xl).
tuning_fn_eval_body([X|Xs], Args, [ite, [=, s, Qx], [Xl|Args], Else]) :- quoted_atom(X, Qx), atom_concat('lat!', X, Xl), tuning_fn_eval_body(Xs, Args, Else).

% tuning_fn_domain/3
%
tuning_fn_domain(_, agr, ['define-fun', Name, [[s, 'String']], 'Bool', [or, list(Body)]]) :- !,
    setof(N, P^(current_predicate(lat:P/N), sub_atom(P, _, 4, _, agr_)), Arities),
    member(Arity, Arities),
    N is Arity-1,
    atom_number(Len, N),
    atom_concat('domain-agr!', Len, Name),
    findall(C, tuning_connectives(agr, N, _, _, C), Connectives),
    tuning_fn_domain(Connectives, Body).
tuning_fn_domain(_, Type, ['define-fun', Name, [[s, 'String']], 'Bool', [or, list(Body)]]) :-
    atom_concat('domain-', Type, Name),
    findall(C, tuning_connectives(Type, 2, _, _, C), Connectives),
    tuning_fn_domain(Connectives, Body).
tuning_fn_domain([], []).
tuning_fn_domain([X|Xs], [[=, s, Qx]|Ys]) :- quoted_atom(X, Qx), tuning_fn_domain(Xs, Ys).

%
%
tuning_fn_error(TD, [assert, [=, 'x!0', [+|Distances]]]) :-
    tuning_fn_error(TD, 1, Distances).
tuning_fn_error([], _, []).
tuning_fn_error([td(TD)|TDs], N, [['lat!distance', Var, TD]|Distances]) :-
    atom_number(Num, N),
    atom_concat('x!', Num, Var),
    M is N+1,
    tuning_fn_error(TDs, M, Distances).

tuning_fn_minimize(Tests, Expected, [assert, [=, 'error!', [+|Distances]]]) :-
    tuning_fn_minimize_body(Tests, Expected, Distances).
tuning_fn_minimize_body([], [], []).
tuning_fn_minimize_body([X|Xs], [td(Y)|Ys], [['lat!distance',C,Y]|Zs]) :- tuning_fn_case(X,C), tuning_fn_minimize_body(Xs, Ys, Zs).

% tuning_fn_members/[2,3]
%
tuning_fn_members(td, list(Members)) :- !,
    findall(S,tuning_sym(td,1,S),Sym),
    tuning_fn_members(td, Sym, Members).
tuning_fn_members(agr, list(Members)) :- !,
    setof(N, tuning_sym(agr,N,_), Arities),
    member(Arity, Arities),
    findall(S,tuning_sym(agr,Arity,S),Sym),
    atom_number(Len, Arity),
    atom_concat('domain-agr!', Len, Name),
    tuning_fn_members(Name, Sym, Members).
tuning_fn_members(Type, list(Members)) :- !,
    findall(S,tuning_sym(Type,2,S),Sym),
    atom_concat('domain-', Type, Name),
    tuning_fn_members(Name, Sym, Members).
tuning_fn_members(_, [], []).
tuning_fn_members(td, [X|Xs], [[assert, ['lat!member', X]]|Ms]) :- !,
    tuning_fn_members(td, Xs, Ms).
tuning_fn_members(Name, [X|Xs], [[assert, [Name, X]]|Ms]) :- !,
    tuning_fn_members(Name, Xs, Ms).

% tuning_fn_cases/[2,3], tuning_fn_case/2
%
tuning_fn_cases(Tests, list(Cases)) :-
    tuning_fn_cases(Tests, 1, Cases).
tuning_fn_cases([], _, []).
tuning_fn_cases([T|Ts], N, [[assert, [=, Var, Case]]|Cases]) :-
    atom_number(Num, N),
    atom_concat('x!', Num, Var),
    tuning_fn_case(T, Case),
    M is N+1,
    tuning_fn_cases(Ts, M, Cases).
tuning_fn_case(td(X), X). :- !.
tuning_fn_case(sym(td(X)), X) :- !.
tuning_fn_case(sym(F), [Eval,S|Args]) :- F =.. [agr,S,L,A], !, atom_number(Atom, L), atom_concat('eval-agr!', Atom, Eval), !, tuning_fn_case(A, Args).
tuning_fn_case(sym(F), [Eval,S|Args]) :- F =.. [C,S,_,A], atom_concat('eval-', C, Eval), !, tuning_fn_case(A, Args).
tuning_fn_case(F, [Name|Args]) :- F =.. [C,S,_,A], !, atom_concat('lat!', C, C1), atom_concat(C1, '_', C2), atom_concat(C2, S, Name), tuning_fn_case(A, Args).
tuning_fn_case([], []).
tuning_fn_case([X|Xs], [Y|Ys]) :-
    tuning_fn_case(X,Y),
    tuning_fn_case(Xs,Ys). 

% tuning_fn_declarations/3
%
tuning_fn_declarations(_, [], list([])).
tuning_fn_declarations(Domain, [sym(C,_,S)|Syms], list([['declare-const', S, Dom]|Decs])) :-
    (C = td -> Dom = Domain ; Dom = 'String'),
    tuning_fn_declarations(Domain, Syms, list(Decs)).

% tuning_fn_declarations_answers/[3,4]
%
tuning_fn_declarations_answers(Domain, TDs, list([['declare-const', 'x!0', 'Real']|Decs])) :-
    tuning_fn_declarations_answers(Domain, TDs, 1, Decs).
tuning_fn_declarations_answers(_, [], _, []).
tuning_fn_declarations_answers(Domain, [_|TDs], N, [['declare-const', Var, Domain]|Decs]) :-
    atom_number(Num, N),
    atom_concat('x!', Num, Var),
    M is N+1,
    tuning_fn_declarations_answers(Domain, TDs, M, Decs).

% tuning_program_smt/2
% generate the smt program
tuning_program_smt(Domain, Program) :-
	check_testcases,
	retractall(leaf(_)),
	( testcase(_,B),
	  once(tuning_leaves(B)),
	  fail
	; !, true),
	once(smt_symbols),
	findall(sym(C,L,S),tuning_sym(C,L,S),Sym),
	findall(Leaf,leaf(Leaf),Tests),
	findall(TD,testcase(TD,_),Expected),
    % lattice
    findall(Aux, lat_to_smt_aux(Aux), LatticeAux),
    lat_member_to_smt(Domain, LatticeMember),
    lat_members_to_smt(Domain, LatticeMembers),
    lat_leq_to_smt(Domain, LatticeLeq),
    lat_distance_to_smt(Domain, LatticeDistance),
    findall(Connective, lat_connective_to_smt(Domain, Connective), LatticeConnectives),
    % declarations
    %tuning_fn_declarations_answers(Domain, Expected, DeclarationsAns),
    tuning_fn_declarations(Domain, Sym, Declarations),
    % domains
    tuning_fn_domain(Domain, and, DomainAND),
    tuning_fn_domain(Domain, or, DomainOR),
    findall(AGR, tuning_fn_domain(Domain, agr, AGR), DomainAGR),
    % evals
    tuning_fn_eval(Domain, and, EvalAND),
    tuning_fn_eval(Domain, or, EvalOR),
    findall(AGR, tuning_fn_eval(Domain, agr, AGR), EvalAGR),
    % members
    tuning_fn_members(td, MembersTD),
    tuning_fn_members(and, MembersAND),
    tuning_fn_members(or, MembersOR),
    findall(AGR, tuning_fn_members(agr, AGR), MembersAGR),
    % cases
    %tuning_fn_cases(Tests, Cases),
    % error
    %tuning_fn_error(Expected, Error),
    tuning_fn_minimize(Tests, Expected, Min),
    % write
   smt_program_round(list([
        %DeclarationsAns,
        ['declare-const', 'error!', 'Real'],
        Declarations,
        list(LatticeAux), LatticeMember, LatticeMembers, LatticeLeq,
        LatticeDistance, list(LatticeConnectives),
        DomainAND, DomainOR, list(DomainAGR),
        EvalAND, EvalOR, list(EvalAGR),
        MembersTD, MembersAND, MembersOR, list(MembersAGR),
        %Cases,
        %Error,
        Min,
        ['set-option', ':pp.decimal', true],
        [minimize, 'error!'],
        ['check-sat'],
        ['get-model']
    ]), Program).

smt_program_round([], []) :- !.
smt_program_round(X, Y) :- float(X), !, Y is round(X*100)/100. 
smt_program_round(list(Xs), list(Ys)) :- !, smt_program_round(Xs,Ys).
smt_program_round([X|Xs], [Y|Ys]) :- !, smt_program_round(X,Y), smt_program_round(Xs,Ys).
smt_program_round(X, X) :- !.


% tuning_smt/1
% start the process of tuning with smt
tuning_smt(Domain) :-
    tuning_program_smt(Domain, Program),
    random_file_id(R),
    atom_concat(R, '-tuning.smt', Path),
    write_smt(Path, Program),
    atom_concat('z3 -smt2 ', Path, Command),
    atom_concat(Command, ' > result.smt', CommandOut),
    shell(CommandOut, _),
    open('result.smt', read, Stream),
    read_stream_to_codes(Stream, Codes),
    remove_last(Codes, Codes2),
    string_to_atom(Codes2, Atom),
    atom_chars(Atom, Chars),
    parse_smt(SMT, Chars, []).

%
%
remove_last([], []) :- !.
remove_last([_], []) :- !.
remove_last([X|Xs], [X|Ys]) :- !, remove_last(Xs, Ys).

%
%
write_smt_tabular(_, 0) :- !.
write_smt_tabular(Stream, N) :- !, write(Stream, '  '), M is N-1, write_smt_tabular(Stream, M).

% write_smt/[2,3]
% write the smt program
write_smt(Path, X) :- 
    open(Path, write, Stream),
    write_smt(Stream, X, 0),
    close(Stream).
write_smt(_, list([]), _) :- !.
write_smt(Stream, list([X|Xs]), Level) :- !,
    write_smt(Stream, X, Level),
    write_smt(Stream, list(Xs), Level).
write_smt(Stream, X, _) :-
    X \= [],
    atomic(X), !,
    write(Stream, X),
    write(Stream, ' ').
write_smt(Stream, Xs, Level) :-
    is_list(Xs), !,
    Level_ is Level + 1,
    write(Stream, '\n'),
    write_smt_tabular(Stream, Level),
    write(Stream, '( '),
    write_smt(Stream, list(Xs), Level_),
    write(Stream, ') ').

%
%
web_tuning_smt(R, D) :-
	assertz(random_file_id(R)),
	assert(loaded_file_lat('num.lat')),retractall(parsingGoal),assert(fasiller_lcut(0)),
	retractall(rule(_,_,_,_,_)), retractall(state(_,_)),
	retractall(fasiller_depth(_)), assert(fasiller_depth(12)),
	fasiller_default,
	lat('lat.pl'),
	parse('fuzzy.fpl'),
	sim('sim.sim'),
	parse_dcg_testcases,
	depth(D),
    tuning_smt('Real').



% SMT TO PROLOG

% parse_smt/3
%
parse_smt(list([X|Xs])) --> parse_smt_blanks, parse_smt_list(X), !, parse_smt(list(Xs)).
parse_smt(list([])) --> [].

% parse_smt_list/3
%
parse_smt_list(sat) --> [s,a,t].
parse_smt_list(unsat) --> [u,n,s,a,t].
parse_smt_list(unknown) --> [u,n,k,n,o,w,n].
parse_smt_list(Args) --> ['('], !, parse_smt_args(Args), parse_smt_blanks, [')'].

% parse_smt_args/3
%
parse_smt_args([A|As]) --> parse_smt_blanks, parse_smt_token(A), !, parse_smt_args(As).
parse_smt_args([]) --> [].
parse_smt_token(N) --> parse_smt_token_number(N), !.
parse_smt_token(I) --> parse_smt_token_identifier(I), !.
parse_smt_token(S) --> parse_smt_token_string(S), !.
parse_smt_token(G) --> parse_smt_token_graphics(G), !.
parse_smt_token(L) --> parse_smt_list(L), !.

% parse_smt_identifier/3
%
parse_smt_token_identifier(T) --> parse_smt_letter(F), parse_smt_identifier(L), {atom_chars(T,[F|L])}.
parse_smt_identifier([H|T]) --> parse_smt_id(H), !, parse_smt_identifier(T).
parse_smt_identifier([]) --> [].
parse_smt_id(X) --> parse_smt_letter(X).
parse_smt_id(X) --> parse_smt_number(X).
parse_smt_minus(X) --> [X], {char_code(X,C), C >= 97, C =< 122}.
parse_smt_mayus(X) --> [X], {char_code(X,C), C >= 65, C =< 90}.
parse_smt_letter(X) --> parse_smt_minus(X).
parse_smt_letter(X) --> parse_smt_mayus(X).
parse_smt_letter('_') --> ['_'].
parse_smt_letter('-') --> ['-'].
parse_smt_letter('!') --> ['!'].

% parse_smt_string/3
%
parse_smt_token_string(str(S)) --> parse_smt_double_quote, parse_smt_double_quote_contents(T), parse_smt_double_quote, {atom_chars(S,T)}.
parse_smt_double_quote --> ['"'].
parse_smt_double_quote_contents([X|Xs]) --> parse_smt_double_quote_content(X), !, parse_smt_double_quote_contents(Xs).
parse_smt_double_quote_contents([]) --> [].
parse_smt_double_quote_content(X) --> [X], {X \= '"'}.
parse_smt_double_quote_content(['"']) --> ['"','"'].
parse_smt_double_quote_content(['"']) --> ['\\','"'].

% parse_smt_graphics/3
%
parse_smt_token_graphics(T) --> parse_smt_graphic(H), parse_smt_graphics(G), {atom_chars(T,[H|G])}.
parse_smt_graphics([H|T]) --> parse_smt_graphic(H), !, parse_smt_graphics(T).
parse_smt_graphics([]) --> [].
parse_smt_graphic(X) --> [X], {member(X,['$','&','*','+','-','/',':','<','?','@','^','~'])}.

% parse_smt_number/3
%
parse_smt_token_number(num(N)) --> parse_smt_numbers(X), parse_smt_token_number2(Y), !, {append(X,Y,Z)}, {atom_chars(T,Z), atom_number(T,N)}.
parse_smt_token_number2(['.'|X]) --> ['.'], parse_smt_numbers(X), !.
parse_smt_token_number2([]) --> [].
parse_smt_number(X) --> [X], {char_code(X,C), C >= 48, C =< 57}.
parse_smt_numbers([N|M]) --> parse_smt_number(N), parse_smt_numbers(M), !.
parse_smt_numbers([N]) --> parse_smt_number(N).

% parse_smt_blanks/2
%
parse_smt_blanks --> parse_smt_blank, !, parse_smt_blanks.
parse_smt_blanks --> [].
parse_smt_blank --> [' '].
parse_smt_blank --> ['\t'].
parse_smt_blank --> ['\n'].
parse_smt_blank --> ['\r'].
