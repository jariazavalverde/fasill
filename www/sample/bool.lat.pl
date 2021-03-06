% Elements
member(false).
member(true).
members([false,true]).

% Distance
distance(X, X, 0.0).
distance(X, X, 1.0).

% Ordering relation
leq(false, _).
leq(_, true).

% Supremum and infimum
bot(false).
top(true).

% Binary operations
and_bool(true, true, true).
and_bool(_, _, false).
or_bool(false, false, false).
or_bool(_, _, true).

% Default connectives
tnorm(bool).
tconorm(bool).
