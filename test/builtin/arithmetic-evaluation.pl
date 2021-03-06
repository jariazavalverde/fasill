?- consult(builtin).



% IS/2

% (real) <X is 1+1,{}> -> [<1.0,{X/2}>]
?- test_builtin(1, '../../sample/lat/real.lat.pl',
    term(is,[var('X'),term('+',[num(1),num(1)])]),
    [state(num(1.0), ['X'/num(2)])]
).

% (real) <X is 1.0+1,{}> -> [<1.0,{X/2.0}>]
?- test_builtin(2, '../../sample/lat/real.lat.pl',
    term(is,[var('X'),term('+',[num(1.0),num(1)])]),
    [state(num(1.0), ['X'/num(2.0)])]
).

% (real) <X is 4.2 + 3 * 2,{}> -> [<1.0,{X/10.2}>]
?- test_builtin(3, '../../sample/lat/real.lat.pl',
    term(is,[var('X'),term('+',[num(4.2),term('*',[num(3),num(2)])])]),
    [state(num(1.0), ['X'/num(10.2)])]
).

% (real) <X is 4/2,{}> -> [<1.0,{X/2.0}>]
?- test_builtin(4, '../../sample/lat/real.lat.pl',
    term(is,[var('X'),term('/',[num(4),num(2)])]),
    [state(num(1.0), ['X'/num(2.0)])]
).

% (real) <X is 4/0,{}> -> error(evaluation_error(zero_division), is/2)
?- test_builtin(5, '../../sample/lat/real.lat.pl',
    term(is,[var('X'),term('/',[num(4),num(0)])]),
    [exception(term(error,[term(evaluation_error,[term(zero_division,[])]),term('/',[term(is,[]),num(2)])]))]
).

% (real) <X is 4//0,{}> -> error(evaluation_error(zero_division), is/2)
?- test_builtin(6, '../../sample/lat/real.lat.pl',
    term(is,[var('X'),term('//',[num(4),num(0)])]),
    [exception(term(error,[term(evaluation_error,[term(zero_division,[])]),term('/',[term(is,[]),num(2)])]))]
).

% (real) <X is 4.0//2,{}> -> error(type_error(integer,4.0), is/2)
?- test_builtin(7, '../../sample/lat/real.lat.pl',
    term(is,[var('X'),term('//',[num(4.0),num(2)])]),
    [exception(term(error,[term(type_error,[term(integer,[]),4.0]),term('/',[term(is,[]),num(2)])]))]
).

% (real) <X is 4//2.0,{}> -> error(type_error(integer,4.0), is/2)
?- test_builtin(8, '../../sample/lat/real.lat.pl',
    term(is,[var('X'),term('//',[num(4),num(2.0)])]),
    [exception(term(error,[term(type_error,[term(integer,[]),2.0]),term('/',[term(is,[]),num(2)])]))]
).

% (real) <X is 5//2,{}> -> [<1.0,{X/2}>]
?- test_builtin(9, '../../sample/lat/real.lat.pl',
    term(is,[var('X'),term('//',[num(5),num(2)])]),
    [state(num(1.0), ['X'/num(2)])]
).

% (real) <X is 1+Y,{}> -> error(instantiation_error, is/2)
?- test_builtin(10, '../../sample/lat/real.lat.pl',
    term(is,[var('X'),term('+',[num(1),var('Y')])]),
    [exception(term(error,[term(instantiation_error,[]),term('/',[term(is,[]),num(2)])]))]
).

% (real) <X is op(3.0),{}> -> error(type_error(evaluable, op/1), is/2)
?- test_builtin(11, '../../sample/lat/real.lat.pl',
    term(is,[var('X'),term(op,[num(3.0)])]),
    [exception(term(error,[term(type_error,[term(evaluable,[]),op/1]),term('/',[term(is,[]),num(2)])]))]
).

% (real) <X is mod(3,2),{}> -> [<1.0,{X/1}>]
?- test_builtin(12, '../../sample/lat/real.lat.pl',
    term(is,[var('X'),term(mod,[num(3),num(2)])]),
    [state(num(1.0), ['X'/num(1)])]
).

% (real) <X is mod(4,2),{}> -> [<1.0,{X/1}>]
?- test_builtin(13, '../../sample/lat/real.lat.pl',
    term(is,[var('X'),term(mod,[num(4),num(2)])]),
    [state(num(1.0), ['X'/num(0)])]
).

% (real) <X is mod(4,0),{}> -> error(evaluation_error(zero_division), is/2)
?- test_builtin(14, '../../sample/lat/real.lat.pl',
    term(is,[var('X'),term(mod,[num(4),num(0)])]),
    [exception(term(error,[term(evaluation_error,[term(zero_division,[])]),term('/',[term(is,[]),num(2)])]))]
).

% (real) <X is log(1),{}> -> [<1.0,{X/0.0}>]
?- test_builtin(15, '../../sample/lat/real.lat.pl',
    term(is,[var('X'),term(log,[num(1)])]),
    [state(num(1.0), ['X'/num(0.0)])]
).

% (real) <X is log(0),{}> -> error(evaluation_error(undefined), is/2)
?- test_builtin(16, '../../sample/lat/real.lat.pl',
    term(is,[var('X'),term(log,[num(0)])]),
    [exception(term(error,[term(evaluation_error,[term(undefined,[])]),term(/,[term(is,[]),num(2)])]))]
).

% (real) <X is float_integer_part(2.3),{}> -> [<1.0,{X/2.0}>]
?- test_builtin(17, '../../sample/lat/real.lat.pl',
    term(is,[var('X'),term(float_integer_part,[num(2.3)])]),
    [state(num(1.0), ['X'/num(2.0)])]
).

% (real) <X is float_fractional_part(2.5),{}> -> [<1.0,{X/0.5}>]
?- test_builtin(18, '../../sample/lat/real.lat.pl',
    term(is,[var('X'),term(float_fractional_part,[num(2.5)])]),
    [state(num(1.0), ['X'/num(0.5)])]
).