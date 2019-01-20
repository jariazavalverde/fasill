?- consult(builtin).



% VAR/1

% (real) <var(2),{}> -> [<0.0,{}>]
?- test_builtin(1, '../../sample/lat/real.lat.pl', term(var,[num(2)]), [state(num(0.0), [])]).

% (real) <var(-2),{}> -> [<0.0,{}>]
?- test_builtin(2, '../../sample/lat/real.lat.pl', term(var,[num(-2)]), [state(num(0.0), [])]).

% (real) <var(0.5),{}> -> [<0.0,{}>]
?- test_builtin(3, '../../sample/lat/real.lat.pl', term(var,[num(0.5)]), [state(num(0.0), [])]).

% (real) <var(a),{}> -> [<0.0,{}>]
?- test_builtin(4, '../../sample/lat/real.lat.pl', term(var,[term(a,[])]), [state(num(0.0), [])]).

% (real) <var(p(a)),{}> -> [<0.0,{}>]
?- test_builtin(5, '../../sample/lat/real.lat.pl', term(var,[term(p,[term(a,[])])]), [state(num(0.0), [])]).

% (real) <var(X),{}> -> [<1.0,{}>]
?- test_builtin(6, '../../sample/lat/real.lat.pl', term(var,[var('X')]), [state(num(1.0), ['X'/var('X')])]).



% NONVAR/1

% (real) <nonvar(2),{}> -> [<1.0,{}>]
?- test_builtin(11, '../../sample/lat/real.lat.pl', term(nonvar,[num(2)]), [state(num(1.0), [])]).

% (real) <nonvar(-2),{}> -> [<1.0,{}>]
?- test_builtin(12, '../../sample/lat/real.lat.pl', term(nonvar,[num(-2)]), [state(num(1.0), [])]).

% (real) <nonvar(0.5),{}> -> [<1.0,{}>]
?- test_builtin(13, '../../sample/lat/real.lat.pl', term(nonvar,[num(0.5)]), [state(num(1.0), [])]).

% (real) <nonvar(a),{}> -> [<1.0,{}>]
?- test_builtin(14, '../../sample/lat/real.lat.pl', term(nonvar,[term(a,[])]), [state(num(1.0), [])]).

% (real) <nonvar(p(a)),{}> -> [<1.0,{}>]
?- test_builtin(15, '../../sample/lat/real.lat.pl', term(nonvar,[term(p,[term(a,[])])]), [state(num(1.0), [])]).

% (real) <nonvar(X),{}> -> [<0.0,{}>]
?- test_builtin(16, '../../sample/lat/real.lat.pl', term(nonvar,[var('X')]), [state(num(0.0), ['X'/var('X')])]).



% NUMBER/1

% (real) <number(2),{}> -> [<1.0,{}>]
?- test_builtin(21, '../../sample/lat/real.lat.pl', term(number,[num(2)]), [state(num(1.0), [])]).

% (real) <number(-2),{}> -> [<1.0,{}>]
?- test_builtin(22, '../../sample/lat/real.lat.pl', term(number,[num(-2)]), [state(num(1.0), [])]).

% (real) <number(0.5),{}> -> [<1.0,{}>]
?- test_builtin(23, '../../sample/lat/real.lat.pl', term(number,[num(0.5)]), [state(num(1.0), [])]).

% (real) <number(a),{}> -> [<0.0,{}>]
?- test_builtin(24, '../../sample/lat/real.lat.pl', term(number,[term(a,[])]), [state(num(0.0), [])]).

% (real) <number(p(a)),{}> -> [<0.0,{}>]
?- test_builtin(25, '../../sample/lat/real.lat.pl', term(number,[term(p,[term(a,[])])]), [state(num(0.0), [])]).

% (real) <number(X),{}> -> [<0.0,{}>]
?- test_builtin(26, '../../sample/lat/real.lat.pl', term(number,[var('X')]), [state(num(0.0), ['X'/var('X')])]).



% INTEGER/1

% (real) <integer(2),{}> -> [<1.0,{}>]
?- test_builtin(31, '../../sample/lat/real.lat.pl', term(integer,[num(2)]), [state(num(1.0), [])]).

% (real) <integer(-2),{}> -> [<1.0,{}>]
?- test_builtin(32, '../../sample/lat/real.lat.pl', term(integer,[num(-2)]), [state(num(1.0), [])]).

% (real) <integer(0.5),{}> -> [<0.0,{}>]
?- test_builtin(33, '../../sample/lat/real.lat.pl', term(integer,[num(0.5)]), [state(num(0.0), [])]).

% (real) <integer(a),{}> -> [<0.0,{}>]
?- test_builtin(34, '../../sample/lat/real.lat.pl', term(integer,[term(a,[])]), [state(num(0.0), [])]).

% (real) <integer(p(a)),{}> -> [<0.0,{}>]
?- test_builtin(35, '../../sample/lat/real.lat.pl', term(integer,[term(p,[term(a,[])])]), [state(num(0.0), [])]).

% (real) <integer(X),{}> -> [<0.0,{}>]
?- test_builtin(36, '../../sample/lat/real.lat.pl', term(integer,[var('X')]), [state(num(0.0), ['X'/var('X')])]).



% FLOAT/1

% (real) <float(2),{}> -> [<1.0,{}>]
?- test_builtin(41, '../../sample/lat/real.lat.pl', term(float,[num(2)]), [state(num(0.0), [])]).

% (real) <float(-2),{}> -> [<0.0,{}>]
?- test_builtin(42, '../../sample/lat/real.lat.pl', term(float,[num(-2)]), [state(num(0.0), [])]).

% (real) <float(0.5),{}> -> [<0.0,{}>]
?- test_builtin(43, '../../sample/lat/real.lat.pl', term(float,[num(0.5)]), [state(num(1.0), [])]).

% (real) <float(a),{}> -> [<0.0,{}>]
?- test_builtin(44, '../../sample/lat/real.lat.pl', term(float,[term(a,[])]), [state(num(0.0), [])]).

% (real) <float(p(a)),{}> -> [<0.0,{}>]
?- test_builtin(45, '../../sample/lat/real.lat.pl', term(float,[term(p,[term(a,[])])]), [state(num(0.0), [])]).

% (real) <float(X),{}> -> [<0.0,{}>]
?- test_builtin(46, '../../sample/lat/real.lat.pl', term(float,[var('X')]), [state(num(0.0), ['X'/var('X')])]).



% ATOM/1

% (real) <atom(2),{}> -> [<1.0,{}>]
?- test_builtin(51, '../../sample/lat/real.lat.pl', term(atom,[num(2)]), [state(num(0.0), [])]).

% (real) <atom(-2),{}> -> [<0.0,{}>]
?- test_builtin(52, '../../sample/lat/real.lat.pl', term(atom,[num(-2)]), [state(num(0.0), [])]).

% (real) <atom(2.0),{}> -> [<0.0,{}>]
?- test_builtin(53, '../../sample/lat/real.lat.pl', term(atom,[num(2.0)]), [state(num(0.0), [])]).

% (real) <atom(a),{}> -> [<1.0,{}>]
?- test_builtin(54, '../../sample/lat/real.lat.pl', term(atom,[term(a,[])]), [state(num(1.0), [])]).

% (real) <atom(p(a)),{}> -> [<0.0,{}>]
?- test_builtin(55, '../../sample/lat/real.lat.pl', term(atom,[term(p,[term(a,[])])]), [state(num(0.0), [])]).

% (real) <atom(X),{}> -> [<0.0,{}>]
?- test_builtin(56, '../../sample/lat/real.lat.pl', term(atom,[var('X')]), [state(num(0.0), ['X'/var('X')])]).



% COMPOUND/1

% (real) <compound(2),{}> -> [<0.0,{}>]
?- test_builtin(61, '../../sample/lat/real.lat.pl', term(compound,[num(2)]), [state(num(0.0), [])]).

% (real) <compound(-2),{}> -> [<0.0,{}>]
?- test_builtin(62, '../../sample/lat/real.lat.pl', term(compound,[num(-2)]), [state(num(0.0), [])]).

% (real) <compound(2.0),{}> -> [<0.0,{}>]
?- test_builtin(63, '../../sample/lat/real.lat.pl', term(compound,[num(2.0)]), [state(num(0.0), [])]).

% (real) <compound(a),{}> -> [<0.0,{}>]
?- test_builtin(64, '../../sample/lat/real.lat.pl', term(compound,[term(a,[])]), [state(num(0.0), [])]).

% (real) <compound(p(a)),{}> -> [<1.0,{}>]
?- test_builtin(65, '../../sample/lat/real.lat.pl', term(compound,[term(p,[term(a,[])])]), [state(num(1.0), [])]).

% (real) <compound(X),{}> -> [<0.0,{}>]
?- test_builtin(66, '../../sample/lat/real.lat.pl', term(compound,[var('X')]), [state(num(0.0), ['X'/var('X')])]).