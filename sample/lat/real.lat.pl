% Elements
member(X) :- number(X).
member(-inf).
member(+inf).
members([-1.0, -0.5, 0.0, 0.5, 1.0]).

% Distance
distance(X,Y,Z) :- Z is abs(Y-X).

% Ordering relation
leq(_, +inf).
leq(-inf, _).
leq(X, Y) :- X =< Y.

% Supremum and infimum
bot(-inf).
top(+inf).
supremum(X, Y, Y) :- leq(X, Y), !.
supremum(X, _, X).

% Binary operations
or_add(_, +inf, +inf).
or_add(+inf, _, +inf).
or_add(_, -inf, -inf).
or_add(-inf, _, -inf).
or_add(X, Y, Z) :- Z is X+Y.

and_prod(X, +inf, X).
and_prod(+inf, X, X).
and_prod(X, -inf, X).
and_prod(-inf, X, X).
and_prod(X, Y, Z) :- Z is X*Y.

% Default connectives
tnorm(prod).
tconorm(add).
