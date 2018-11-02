?- consult(builtin).



% VAR/1

% (real) <var(2),{}> -> [<0.0,{}>]
?- test_builtin(1, '../../sample/lat/real.lat.pl', term(var,[num(2)]), [state(num(0.0), [])]).

% (real) <var(-2),{}> -> [<0.0,{}>]
?- test_builtin(1, '../../sample/lat/real.lat.pl', term(var,[num(-2)]), [state(num(0.0), [])]).

% (real) <var(0.5),{}> -> [<0.0,{}>]
?- test_builtin(1, '../../sample/lat/real.lat.pl', term(var,[num(0.5)]), [state(num(0.0), [])]).

% (real) <var(a),{}> -> [<0.0,{}>]
?- test_builtin(1, '../../sample/lat/real.lat.pl', term(var,[term(a,[])]), [state(num(0.0), [])]).

% (real) <var(p(a)),{}> -> [<0.0,{}>]
?- test_builtin(1, '../../sample/lat/real.lat.pl', term(var,[term(p,[term(a,[])])]), [state(num(0.0), [])]).

% (real) <var(X),{}> -> [<1.0,{}>]
?- test_builtin(1, '../../sample/lat/real.lat.pl', term(var,[var('X')]), [state(num(1.0), [])]).



% NONVAR/1

% (real) <nonvar(2),{}> -> [<1.0,{}>]
?- test_builtin(1, '../../sample/lat/real.lat.pl', term(nonvar,[num(2)]), [state(num(1.0), [])]).

% (real) <nonvar(-2),{}> -> [<1.0,{}>]
?- test_builtin(1, '../../sample/lat/real.lat.pl', term(nonvar,[num(-2)]), [state(num(1.0), [])]).

% (real) <nonvar(0.5),{}> -> [<1.0,{}>]
?- test_builtin(1, '../../sample/lat/real.lat.pl', term(nonvar,[num(0.5)]), [state(num(1.0), [])]).

% (real) <nonvar(a),{}> -> [<1.0,{}>]
?- test_builtin(1, '../../sample/lat/real.lat.pl', term(nonvar,[term(a,[])]), [state(num(1.0), [])]).

% (real) <nonvar(p(a)),{}> -> [<1.0,{}>]
?- test_builtin(1, '../../sample/lat/real.lat.pl', term(nonvar,[term(p,[term(a,[])])]), [state(num(1.0), [])]).

% (real) <nonvar(X),{}> -> [<0.0,{}>]
?- test_builtin(1, '../../sample/lat/real.lat.pl', term(nonvar,[var('X')]), [state(num(0.0), [])]).



% NUMBER/1

% (real) <number(2),{}> -> [<1.0,{}>]
?- test_builtin(1, '../../sample/lat/real.lat.pl', term(number,[num(2)]), [state(num(1.0), [])]).

% (real) <number(-2),{}> -> [<1.0,{}>]
?- test_builtin(1, '../../sample/lat/real.lat.pl', term(number,[num(-2)]), [state(num(1.0), [])]).

% (real) <number(0.5),{}> -> [<1.0,{}>]
?- test_builtin(1, '../../sample/lat/real.lat.pl', term(number,[num(0.5)]), [state(num(1.0), [])]).

% (real) <number(a),{}> -> [<0.0,{}>]
?- test_builtin(1, '../../sample/lat/real.lat.pl', term(number,[term(a,[])]), [state(num(0.0), [])]).

% (real) <number(p(a)),{}> -> [<0.0,{}>]
?- test_builtin(1, '../../sample/lat/real.lat.pl', term(number,[term(p,[term(a,[])])]), [state(num(0.0), [])]).

% (real) <number(X),{}> -> [<0.0,{}>]
?- test_builtin(1, '../../sample/lat/real.lat.pl', term(number,[var('X')]), [state(num(0.0), [])]).



% INTEGER/1

% (real) <integer(2),{}> -> [<1.0,{}>]
?- test_builtin(1, '../../sample/lat/real.lat.pl', term(integer,[num(2)]), [state(num(1.0), [])]).

% (real) <integer(-2),{}> -> [<1.0,{}>]
?- test_builtin(1, '../../sample/lat/real.lat.pl', term(integer,[num(-2)]), [state(num(1.0), [])]).

% (real) <integer(0.5),{}> -> [<0.0,{}>]
?- test_builtin(1, '../../sample/lat/real.lat.pl', term(integer,[num(0.5)]), [state(num(0.0), [])]).

% (real) <integer(a),{}> -> [<0.0,{}>]
?- test_builtin(1, '../../sample/lat/real.lat.pl', term(integer,[term(a,[])]), [state(num(0.0), [])]).

% (real) <integer(p(a)),{}> -> [<0.0,{}>]
?- test_builtin(1, '../../sample/lat/real.lat.pl', term(integer,[term(p,[term(a,[])])]), [state(num(0.0), [])]).

% (real) <integer(X),{}> -> [<0.0,{}>]
?- test_builtin(1, '../../sample/lat/real.lat.pl', term(integer,[var('X')]), [state(num(0.0), [])]).



% FLOAT/1

% (real) <float(2),{}> -> [<1.0,{}>]
?- test_builtin(1, '../../sample/lat/real.lat.pl', term(float,[num(2)]), [state(num(0.0), [])]).

% (real) <float(-2),{}> -> [<0.0,{}>]
?- test_builtin(1, '../../sample/lat/real.lat.pl', term(float,[num(-2)]), [state(num(0.0), [])]).

% (real) <float(0.5),{}> -> [<0.0,{}>]
?- test_builtin(1, '../../sample/lat/real.lat.pl', term(float,[num(0.5)]), [state(num(1.0), [])]).

% (real) <float(a),{}> -> [<0.0,{}>]
?- test_builtin(1, '../../sample/lat/real.lat.pl', term(float,[term(a,[])]), [state(num(0.0), [])]).

% (real) <float(p(a)),{}> -> [<0.0,{}>]
?- test_builtin(1, '../../sample/lat/real.lat.pl', term(float,[term(p,[term(a,[])])]), [state(num(0.0), [])]).

% (real) <float(X),{}> -> [<0.0,{}>]
?- test_builtin(1, '../../sample/lat/real.lat.pl', term(float,[var('X')]), [state(num(0.0), [])]).



% ATOM/1

% (real) <atom(2),{}> -> [<1.0,{}>]
?- test_builtin(1, '../../sample/lat/real.lat.pl', term(atom,[num(2)]), [state(num(0.0), [])]).

% (real) <atom(-2),{}> -> [<0.0,{}>]
?- test_builtin(1, '../../sample/lat/real.lat.pl', term(atom,[num(-2)]), [state(num(0.0), [])]).

% (real) <atom(2.0),{}> -> [<0.0,{}>]
?- test_builtin(1, '../../sample/lat/real.lat.pl', term(atom,[num(2.0)]), [state(num(0.0), [])]).

% (real) <atom(a),{}> -> [<1.0,{}>]
?- test_builtin(1, '../../sample/lat/real.lat.pl', term(atom,[term(a,[])]), [state(num(1.0), [])]).

% (real) <atom(p(a)),{}> -> [<0.0,{}>]
?- test_builtin(1, '../../sample/lat/real.lat.pl', term(atom,[term(p,[term(a,[])])]), [state(num(0.0), [])]).

% (real) <atom(X),{}> -> [<0.0,{}>]
?- test_builtin(1, '../../sample/lat/real.lat.pl', term(atom,[var('X')]), [state(num(0.0), [])]).



% COMPOUND/1

% (real) <compound(2),{}> -> [<0.0,{}>]
?- test_builtin(1, '../../sample/lat/real.lat.pl', term(compound,[num(2)]), [state(num(0.0), [])]).

% (real) <compound(-2),{}> -> [<0.0,{}>]
?- test_builtin(1, '../../sample/lat/real.lat.pl', term(compound,[num(-2)]), [state(num(0.0), [])]).

% (real) <compound(2.0),{}> -> [<0.0,{}>]
?- test_builtin(1, '../../sample/lat/real.lat.pl', term(compound,[num(2.0)]), [state(num(0.0), [])]).

% (real) <compound(a),{}> -> [<0.0,{}>]
?- test_builtin(1, '../../sample/lat/real.lat.pl', term(compound,[term(a,[])]), [state(num(0.0), [])]).

% (real) <compound(p(a)),{}> -> [<1.0,{}>]
?- test_builtin(1, '../../sample/lat/real.lat.pl', term(compound,[term(p,[term(a,[])])]), [state(num(1.0), [])]).

% (real) <compound(X),{}> -> [<0.0,{}>]
?- test_builtin(1, '../../sample/lat/real.lat.pl', term(compound,[var('X')]), [state(num(0.0), [])]).