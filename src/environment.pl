:- module(environment, [
    set_max_inferences/1,
    to_prolog/2,
    from_prolog/2,
    fasill_atom/1,
    fasill_float/1,
    fasill_integer/1,
    fasill_number/1,
    fasill_term/1,
    fasill_var/1,
    program_clause/2,
    program_rule_id/2,
    program_consult/1,
    program_has_predicate/1,
    lattice_tnorm/1,
    lattice_tconorm/1,
    lattice_call_bot/1,
    lattice_call_top/1,
    lattice_call_member/1,
    lattice_call_connective/3,
    lattice_consult/1,
    similarity_tnorm/1,
    similarity_between/4,
    similarity_consult/1
]).

:- use_module(parser).

:- dynamic(
    fasill_rule/3,
    fasill_predicate/1,
    fasill_lattice_tnorm/1,
    '~'/1,
    '~'/2
).



% ENVIRONMENT

% fasill_max_inferences/1
% fasill_max_inferences(?Limit)
%
% This predicate succeeds when ?Limit is the
% current limit of inferences that can be performed
% when a goal is executed.
:- dynamic(fasill_max_inferences/1).
fasill_max_inferences(false).

% set_max_inferences/1
% set_max_inferences(+Limit)
%
% This predicate succeeds, and chages the current
% limit of inferences that can be performed when
% a goal is executed.
set_max_inferences(Limit) :-
    retractall(fasill_max_inferences(Limit)),
    asserta(fasill_max_inferences(Limit)).



% OBJECT MANIPULATION

% to_prolog/2
% to_prolog(+FASILL, ?Prolog)
%
% This predicate takes the FASILL object +FASILL
% and returns the object ?Prolog in Prolog notation.
to_prolog([], []) :- !.
to_prolog([X|Xs], [Y|Ys]) :-
    !, to_prolog(X,Y),
    to_prolog(Xs,Ys).
to_prolog(num(X), X) :- !.
to_prolog(var(_), _).
to_prolog(term(X,Xs), Term) :-
    atom(X),
    !, to_prolog(Xs, Ys),
    Term =.. [X|Ys].

% from_prolog/2
% from_prolog(+Prolog, ?FASILL)
%
% This predicate takes the Prolog object +Prolog
% and returns the object ?FASILL in FASILL notation.
from_prolog([], term([], [])) :- !.
from_prolog([X|Xs], term('.', [Y,Ys])) :-
    !, from_prolog(X,Y),
    from_prolog(Xs,Ys).
from_prolog(X, num(X)) :- number(X), !.
from_prolog(X, term(X, [])) :- atom(X), !.
from_prolog(X, term(H,Args)) :-
    compound(X), !,
    X =.. [H|T],
    maplist(from_prolog, T, Args).

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
    file_consult(Path, Rules),
    (   member(Rule, Rules),
        assertz(Rule),
        Rule = fasill_rule(head(term(Name,Args)),_,_),
        length(Args,Arity),
        (fasill_predicate(Name/Arity) -> true ; assertz(fasill_predicate(Name/Arity))),
        fail ; true).

% program_has_predicate/1
% program_has_predicate(?Indicator)
%
% This predicate succeeds when ?Indicator is the indicator
% of a predicate asserted in the program loaded in the current
% environment.
program_has_predicate(Name/Arity) :-
    fasill_predicate(Name/Arity) ;
    lattice_call_bot(Bot),
    similarity_between(Name, Other, Length, TD),
    TD \= Bot,
    fasill_predicate(Other/Length), !.


% LATTICES

% lattice_tnorm/1
% lattice_tnorm(?Tnorm)
%
% This predicate succeeds when ?Tnorm is the
% current t-norm asserted in the environment.
lattice_tnorm(Tnorm) :- tnorm(Tnorm).

% lattice_tconorm/1
% lattice_tconorm(?Tconorm)
%
% This predicate succeeds when ?Tconorm is the
% current t-conorm asserted in the environment.
lattice_tconorm(Tconorm) :- tconorm(Tconorm).

% lattice_call_bot/1
% lattice_call_bot(-Bot)
%
% This predicate succeeds when -Bot is the
% bottom member of the lattice loaded into
% the environment.
lattice_call_bot(Bot) :-
    bot(Prolog),
    from_prolog(Prolog, Bot).

% lattice_call_top/1
% lattice_call_top(-Bot)
%
% This predicate succeeds when -Bot is the
% bottom member of the lattice loaded into
% the environment.
lattice_call_top(Top) :-
    top(Prolog),
    from_prolog(Prolog, Top).

% lattice_call_member/1
% lattice_call_member(+Memeber)
%
% This predicate succeeds when +Member is a member
% of the lattice loaded into the environment.
lattice_call_member(Member) :-
    to_prolog(Member, Prolog),
    member(Prolog).

% lattice_call_connective/3
% lattice_call_connective(+Name, +Arguments, ?Result)
%
% This predicate succeeds when ?Result is the result
% of evaluate the connective ?Name with the arguments
% +Arguments of the lattice loaded into the environment.
lattice_call_connective('&', Args, Result) :- !,
    (lattice_tnorm(Name) ;
    current_predicate(Tnorm/3),
    atom_concat(and_, Name, Tnorm)), !,
    lattice_call_connective('&'(Name), Args, Result).
lattice_call_connective('|', Args, Result) :- !,
    (lattice_tnorm(Name) ;
    current_predicate(Tconorm/3),
    atom_concat(or_, Name, Tconorm)), !,
    lattice_call_connective('|'(Name), Args, Result).
lattice_call_connective(Op, Args, Result) :-
    Op =.. [Type,Name],
    (   Type = '&', Pre = 'and_' ;
        Type = '|', Pre = 'or_' ;
        Type = '@', Pre = 'agr_'
    ), !,
    atom_concat(Pre, Name, Name_),
    maplist(to_prolog, Args, Args_),
    append(Args_, [Prolog], ArgsCall),
    Call =.. [Name_|ArgsCall],
    call(environment:Call),
    from_prolog(Prolog, Result).

% lattice_consult/1
% lattice_consult(+Path)
%
% This predicate loads the lattice of the file +Path into
% the environment. This predicate cleans the previous lattice.
lattice_consult(Path) :-
    consult(Path).



% SIMILARITY RELATIONS

% ~/1
% ~(+Assignment)
%
% This predicate succeeds when +Assignment is a valid 
% assignment of a t-norm. A valid assignment is of the 
% form ~tnorm = Atom, where Atom is an atom. This predicate
% asserts Atom in the current environment as the current
% t-norm for similarities. This predicate retracts the
% current t-norm, if exists.
:- op(750, fx, ~).
:- multifile('~'/1).

% ~/2
% ~(+SimilarityEquation)
%
% This predicate succeeds when +SimilarityEquation is a
% valid similarity equation and asserts it in the current
% environment. A valid similarity equation is of the form
% AtomA/Length ~ AtomB/Length = TD, where AtomA and AtomB
% are atoms and Length is a non-negative integer. Note that
% this equation is parsed with the default table operator
% as '~'('/'(AtomA,Length), '='('/'(AtomB,Length),TD)).
:- op(800, xfx, ~).
:- multifile('~'/2).

% similarity_tnorm/1
% similarity_tnorm(?Tnorm)
%
% This predicate succeeds when ?Tnorm is the current
% t-norm asserted in the environment.
similarity_tnorm(Tnorm) :- ~(tnorm=Tnorm).

% similarity_between/4
% similarity_between(?AtomA, ?AtomB, ?Length, ?TD)
%
% This predicate succeeds when ?AtomA/?Length is similar
% to ?AtomB/?Length with truth degree ?TD, using the current
% similarity relation in the environment.
similarity_between(AtomA, AtomB, Length, TD) :-
    environment:'~'(AtomA/Length, '='(AtomB/Length, Prolog)),
    from_prolog(Prolog, TD).
similarity_between(AtomA, AtomB, 0, TD) :-
    environment:'~'(AtomA, '='(AtomB, Prolog)),
    AtomA \= '/'(_,_), AtomB \= '/'(_,_),
    from_prolog(Prolog, TD).

% similarity_retract/0
% similarity_retract
%
% This predicate succeeds and retracts all the clauses
% of similarity from the current environment.
similarity_retract :-
    retractall(~(_, _)),
    retractall(~(_)).

% similarity_consult/1
% similarity_consult(+Path)
%
% This predicate loads the similarities equations of the
% file +Path into the environment. This predicate cleans
% the previous similarity relations.
similarity_consult(Path) :-
    similarity_retract,
    load_files(Path, [imports(['~'/1,'~'/2])]),
    similarity_closure.

% similarity_closure/0
% similarity_closure
%
% This predicate computes the reflexive, symmetric and 
% transitive closure of the similarity scheme asserted
% into the current environment.
similarity_closure :-
    findall(Atom/Length, similarity_between(Atom, _, Length, _), Dom1),
    findall(Atom/Length, similarity_between(_, Atom, Length, _), Dom2),
    append(Dom1, Dom2, DomR),
    list_to_set(DomR, Dom),
    findall(sim(Atom1,Atom2,Length,TD), similarity_between(Atom1,Atom2,Length,TD), Scheme),
    similarity_tnorm(Tnorm),
    lattice_call_bot(Bot),
    lattice_call_top(Top),
    similarity_retract,
    findall(_, similarity_closure_reflexive(Dom, Scheme, Tnorm, Bot, Top), _),
    findall(_, similarity_closure_symmetric(Dom, Scheme, Tnorm, Bot, Top), _),
    findall(_, similarity_closure_transitive(Dom, Scheme, Tnorm, Bot, Top), _),
    assertz('~'(tnorm=Tnorm)).

similarity_closure_reflexive(Dom, _, _, _, Top) :-
    to_prolog(Top,TopP),
    member(X/Length, Dom),
    member(Y/Length, Dom),
    (X = Y -> assertz('~'(X/Length,Y/Length = TopP)) ; true).

similarity_closure_symmetric(Dom, Scheme, _, Bot, _) :-
    member(X/Length, Dom),
    member(Y/Length, Dom),
    \+('~'(X/Length,Y/Length = _)),
    (member(sim(X,Y,Length,TD), Scheme) -> true ; (
        member(sim(Y,X,Length,TD), Scheme) -> true ; TD = Bot)
    ),
    to_prolog(TD, TDP),
    assertz('~'(X/Length,Y/Length = TDP)),
    assertz('~'(Y/Length,X/Length = TDP)).

similarity_closure_transitive(Dom, _, Tnorm, _, _) :-
    member(Z/Length, Dom),
    member(X/Length, Dom),
    member(Y/Length, Dom),
    '~'(X/Length,Y/Length=TDxy),
    '~'(X/Length,Z/Length=TDxz),
    '~'(Z/Length,Y/Length=TDzy),
    from_prolog(TDxy, TDPxy),
    from_prolog(TDxz, TDPxz),
    from_prolog(TDzy, TDPzy),
    retract('~'(X/Length,Y/Length=TDxy)),
    lattice_call_connective('&'(Tnorm), [TDPxz,TDPzy], TDz),
    lattice_call_connective('|'(Tnorm), [TDPxy,TDz], TD),
    to_prolog(TD, TDP),
    assertz('~'(X/Length,Y/Length = TDP)).