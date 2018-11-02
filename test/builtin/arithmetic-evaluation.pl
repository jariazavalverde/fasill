?- consult(builtin).



% IS/2

% (real) <X is 1+1,{}> -> [<1.0,{X/2}>]
?- test_builtin(1, '../../sample/lat/real.lat.pl',
    term(is,[var('X'),term('+',[num(1),num(1)])]),
    [state(num(1.0), ['X'/num(2)])]
).

% (real) <X is 1.0+1,{}> -> [<1.0,{X/2.0}>]
?- test_builtin(1, '../../sample/lat/real.lat.pl',
    term(is,[var('X'),term('+',[num(1.0),num(1)])]),
    [state(num(1.0), ['X'/num(2.0)])]
).

% (real) <X is 4.2 + 3 * 2,{}> -> [<1.0,{X/10.2}>]
?- test_builtin(1, '../../sample/lat/real.lat.pl',
    term(is,[var('X'),term('+',[num(4.2),term('*',[num(3),num(2)])])]),
    [state(num(1.0), ['X'/num(10.2)])]
).

% (real) <X is 4/2,{}> -> [<1.0,{X/2.0}>]
?- test_builtin(1, '../../sample/lat/real.lat.pl',
    term(is,[var('X'),term('/',[num(4),num(2)])]),
    [state(num(1.0), ['X'/num(2.0)])]
).

% (real) <X is 4/0,{}> -> error(evaluation_error(zero_division), is/2)
?- test_builtin(1, '../../sample/lat/real.lat.pl',
    term(is,[var('X'),term('/',[num(4),num(0)])]),
    [exception(error(evaluation_error(zero_division), is/2))]
).

% (real) <X is op(3.0),{}> -> error(type_error(evaluable, op/1), is/2)
?- test_builtin(1, '../../sample/lat/real.lat.pl',
    term(is,[var('X'),term(op,[num(3.0)])]),
    [exception(error(type_error(evaluable, op/1), is/2))]
).