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

% t-norm
tnorm(and_godel).
