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
    [exception(error(evaluation_error(zero_division), is/2))]
).

% (real) <X is 4//0,{}> -> error(evaluation_error(zero_division), is/2)
?- test_builtin(6, '../../sample/lat/real.lat.pl',
    term(is,[var('X'),term('//',[num(4),num(0)])]),
    [exception(error(evaluation_error(zero_division), is/2))]
).

% (real) <X is 4.0//2,{}> -> error(type_error(integer,4.0), is/2)
?- test_builtin(7, '../../sample/lat/real.lat.pl',
    term(is,[var('X'),term('//',[num(4.0),num(2)])]),
    [exception(error(type_error(integer,4.0), is/2))]
).

% (real) <X is 4//2.0,{}> -> error(type_error(integer,4.0), is/2)
?- test_builtin(8, '../../sample/lat/real.lat.pl',
    term(is,[var('X'),term('//',[num(4),num(2.0)])]),
    [exception(error(type_error(integer,2.0), is/2))]
).

% (real) <X is 5//2,{}> -> [<1.0,{X/2}>]
?- test_builtin(9, '../../sample/lat/real.lat.pl',
    term(is,[var('X'),term('//',[num(5),num(2)])]),
    [state(num(1.0), ['X'/num(2)])]
).

% (real) <X is 1+Y,{}> -> error(instantiation_error, is/2)
?- test_builtin(10, '../../sample/lat/real.lat.pl',
    term(is,[var('X'),term('+',[num(1),var('Y')])]),
    [exception(error(instantiation_error, is/2))]
).

% (real) <X is op(3.0),{}> -> error(type_error(evaluable, op/1), is/2)
?- test_builtin(11, '../../sample/lat/real.lat.pl',
    term(is,[var('X'),term(op,[num(3.0)])]),
    [exception(error(type_error(evaluable, op/1), is/2))]
).