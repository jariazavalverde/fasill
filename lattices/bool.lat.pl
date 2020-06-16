% Elements
member(0).
member(1).
members([0,1]).

% Distance
distance(X, X, 0.0).
distance(_, _, 1.0).

% Ordering relation
leq(0, _).
leq(_, 1).

% Supremum and infimum
bot(0).
top(1).
supremum(X, Y, Z) :- or_bool(X, Y, Z).

% Binary operations
% and_bool is defined intensionally using the product operator
% by efficiency reasons.
%and_bool(X, Y, Z) :- Z is X*Y.
and_bool(1, 1, 1).
and_bool(_,_,0).
or_bool(X, Y, Z) :- Z is min(1, X+Y).

% Aggregators
agr_xor(X, Y, Z) :- Z is X xor Y.
agr_not(X, Y) :- Y is 1-X.

% Default connectives
tnorm(bool).
tconorm(bool).
