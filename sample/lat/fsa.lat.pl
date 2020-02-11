:- op(200, xfx, ^^).

% Elements
member(X^^'http://www.w3.org/2001/XMLSchema#decimal') :- number(X).
members([
	0.0^^'http://www.w3.org/2001/XMLSchema#decimal',
	0.1^^'http://www.w3.org/2001/XMLSchema#decimal',
	0.2^^'http://www.w3.org/2001/XMLSchema#decimal',
	0.3^^'http://www.w3.org/2001/XMLSchema#decimal',
	0.4^^'http://www.w3.org/2001/XMLSchema#decimal',
	0.5^^'http://www.w3.org/2001/XMLSchema#decimal',
	0.6^^'http://www.w3.org/2001/XMLSchema#decimal',
	0.7^^'http://www.w3.org/2001/XMLSchema#decimal',
	0.8^^'http://www.w3.org/2001/XMLSchema#decimal',
	0.9^^'http://www.w3.org/2001/XMLSchema#decimal',
	1.0^^'http://www.w3.org/2001/XMLSchema#decimal'
]).

% Distance
distance(X^^T,Y^^T,Z) :- Z is abs(Y-X).

% Ordering relation
leq(X^^T,Y^^T) :- X =< Y.

% Supremum and infimum
bot(0.0^^'http://www.w3.org/2001/XMLSchema#decimal').
top(1.0^^'http://www.w3.org/2001/XMLSchema#decimal').

% Conjuctions
and_prod(X^^T,Y^^T,Z^^T) :- Z is X*Y.
and_god(X^^T,Y^^T,Z^^T) :- Z is min(X,Y).
and_luk(X^^T,Y^^T,Z^^T) :- Z is max(X+Y-1,0).

% Disjunctions
or_prod(X^^T,Y^^T,Z^^T) :- U1 is X*Y, U2 is X+Y, Z is U2-U1.
or_god(X^^T,Y^^T,Z^^T) :- Z is max(X,Y).
or_luk(X^^T,Y^^T,Z^^T) :- Z is min(X+Y,1).

% Aggregators
agr_mean(X^^T,Y^^T,Z^^T) :- Z is 0.5*X+0.5*Y.
agr_wmean(W^^T,X^^T,Y^^T,Z^^T) :- Z is W*X+(1-W)*Y.
agr_wsum(U^^T,X^^T,V^^T,Y^^T,Z^^T):-Z is U*X+V*Y.
agr_wmax(U^^T,X^^T,V^^T,Y^^T,Z^^T):-Z is max(min(U,X),min(V,Y)).
agr_wmin(U^^T,X^^T,V^^T,Y^^T,Z^^T):-Z is min(max(1-U,X),max(1-V,Y)).
agr_very(X^^T,Z^^T) :- Z is X*X.
agr_more_or_less(X^^T,Z^^T):-Z is sqrt(X).
agr_close_to(X^^T,L^^T,A^^T,Z^^T):-Z is 1/(1+ ((X-L)/A)^2).
agr_at_least(X^^T,L^^T,A^^T,Z^^T):-X =< A,!, Z is 0.
agr_at_least(X^^T,L^^T,A^^T,Z^^T):-A < X, X < L,!, Z is (X-A)/(L-A).
agr_at_least(X^^T,L^^T,A^^T,Z^^T):-L =< X,!, Z is 1.
agr_at_most(X^^T,L^^T,A^^T,Z^^T):-X >= A,!, Z is 0.
agr_at_most(X^^T,L^^T,A^^T,Z^^T):-A > X , X > L,!, Z is (A-X)/(A-L).
agr_at_most(X^^T,L^^T,A^^T,Z^^T):-X =< L,!, Z is 1.
agr_trapezoidal(A^^T, B^^T, C^^T, D^^T, X^^T, 0^^T) :- X < A ; X > D.
agr_trapezoidal(A^^T, B^^T, C^^T, D^^T, X^^T, Y^^T) :- A =< X, X =< B, Y is (X-A)/(B-A).
agr_trapezoidal(A^^T, B^^T, C^^T, D^^T, X^^T, 1^^T) :- B =< X, X =< C.
agr_trapezoidal(A^^T, B^^T, C^^T, D^^T, X^^T, Y^^T) :- C =< X, X =< D, Y is (D-X)/(D-C).

agr_gt(X^^T, Y^^T, Z^^T) :- X > Y -> Z = 1.0 ; Z = 0.0.

% Default connectives
tnorm(god).
tconorm(god).
