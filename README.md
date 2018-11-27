![FASILL](logo/colorx2048.png)

# FASILL

## Fuzzy Aggregators and Similarities Into a Logic Language

**FASILL** is a Prolog-like first order language containing variables, function symbols, predicate symbols, constants and several (arbitrary) connectives to increase language expressiveness. FASILL uses connectives to combine/propagate truth values through the rules: **conjunctive operators** (denoted by &amp;<sub>1</sub>, &amp;<sub>2</sub>, ..., &amp;<sub>i</sub>), **disjunctive operators** (|<sub>1</sub>, |<sub>2</sub>, ..., |<sub>j</sub>), and **aggregation operators** (usually denoted by @<sub>1</sub>, @<sub>2</sub>, ..., @<sub>k</sub>). Additionally, FASILL contains the truth values of a complete lattice equipped with a collection of connectives.

## Programs

A FASILL program is a tuple <Π, R, L> where Π is a set of rules, R is a similarity relation between the elements of the signature Σ of Π, and L is a complete lattice.

### Rules

A **rule** has the form A &larr; B, where A is an atomic formula called head and B, called body, is a well-formed formula (ultimately built from atomic formulas B<sub>1</sub>, ..., B<sub>n</sub>, truth values of the lattice and connectives). 

```prolog
vanguardist(hydropolis) <- 0.9.
elegant(ritz)           <- 0.8.
close(hydropolis, taxi) <- 0.7.
good_hotel(X) <- @aver(elegant(X), @very(close(X, metro))).
```

### Complete lattices

A complete lattice is a partially ordered set in which all subsets have both a supremum and an infimum.

All relevant components of each lattice can be encapsulated inside a Prolog file which must contain the definitions of a minimal set of predicates defining the set of valid elements (including special mentions to the "top" and "bottom" ones), the full or partial ordering established among them, as well as the repertoire of fuzzy connectives which can be used for their subsequent manipulation.

- **member/1** which is satisfied when being called with a parameter representing a valid truth degree.
- **members/1** which returns in one go a list containing the whole set of truth degrees.
- **bot/1** and **top/1** answer with the top and bottom element of the lattice, respectively.
- **leq/2** models the ordering relation among all the possible pairs of truth degrees, and it is only satisfied when it is invoked with two elements verifying that the first parameter is equal or smaller than the second one.
- Finally, given some fuzzy connectives of the form &amp;<sub>label1</sub> (conjunction), |<sub>label2</sub> (disjunction) or @<sub>label3</sub> (aggregation) with arities n<sub>1</sub>, n<sub>2</sub> and n<sub>3</sub> respectively, we must provide clauses defining the connective predicates **and_label1/(n<sub>1</sub>+1)**, **or_label2/(n<sub>2</sub>+1)** and **agr_label3/(n<sub>3</sub>+1)**, where the extra argument of each predicate is intended to contain the result achieved after the evaluation of the proper connective.

```prolog
% Elements
member(X) :- number(X), 0 =< X, X =< 1.
members([0.0,0.1,0.2,0.3,0.4,0.5,0.6,0.7,0.8,0.9,1.0]).

% Distance
distance(X,Y,Z) :- Z is abs(Y-X).

% Ordering relation
leq(X,Y) :- X =< Y.

% Supremum and infimum
bot(0.0).
top(1.0).

% Binary operations
and_prod(X,Y,Z) :- Z is X*Y.
and_godel(X,Y,Z) :- Z is min(X,Y).
and_luka(X,Y,Z) :- Z is max(X+Y-1,0).
or_prod(X,Y,Z) :- U1 is X*Y, U2 is X+Y, Z is U2-U1.
or_godel(X,Y,Z) :- Z is max(X,Y).
or_luka(X,Y,Z) :- Z is min(X+Y,1).

% Aggregators
agr_aver(X,Y,Z) :- Z is (X+Y)/2.
agr_very(X,Y) :- Y is X*X.

% Default connectives
tnorm(godel).
tconorm(godel).
```

### Similarity relations

Given a domain U and a lattice L with a fixed t-norm, a **similarity relation** R is a fuzzy binary relation on U fulfilling the reflexive, symmetric and transitive properties.

FASILL takes a set of similarity equations `f/n ~ g/n = r`, where `f` and `g` are propositional variables or constants and `r` is an element of L, and generates a valid similarity relation by applying the reflexive, symmetric and transitive closures over the initial scheme.

```prolog
elegant/1 ~ vanguardist/1 = 0.6.
metro ~ bus = 0.5.
bus ~ taxi = 0.4.
~tnorm = godel.
```

## License

Source code is released under the terms of the [BSD 3-Clause License](LICENSE).
