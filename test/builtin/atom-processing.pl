?- consult(builtin).



% ATOM_LENGTH/2

% (real) <atom_length(abc, 3),{}> -> [<1.0,{}>]
?- test_builtin(1, '../../sample/lat/real.lat.pl',
    term(atom_length,[term(abc,[]), num(3)]),
    [state(num(1.0), [])]
).

% (real) <atom_length(abc, 4),{}> -> [<0.0,{}>]
?- test_builtin(1, '../../sample/lat/real.lat.pl',
    term(atom_length,[term(abc,[]), num(4)]),
    [state(num(0.0), [])]
).

% (real) <atom_length(abc, X),{}> -> [<1.0,{X/3}>]
?- test_builtin(1, '../../sample/lat/real.lat.pl',
    term(atom_length,[term(abc,[]), var('X')]),
    [state(num(1.0), ['X'/num(3)])]
).

% (real) <atom_length(X, Y),{}> -> error(instantiation_error, atom_length/2)
?- test_builtin(1, '../../sample/lat/real.lat.pl',
    term(atom_length,[var('X'), var('Y')]),
    [exception(error(instantiation_error,atom_length/2))]
).

% (real) <atom_length(5, Y),{}> -> error(type_error(atom,5), atom_length/2)
?- test_builtin(1, '../../sample/lat/real.lat.pl',
    term(atom_length,[num(5), var('Y')]),
    [exception(error(type_error(atom,num(5)),atom_length/2))]
).

% (real) <atom_length(ab, 2.0),{}> -> error(type_error(integer,2,0), atom_length/2)
?- test_builtin(1, '../../sample/lat/real.lat.pl',
    term(atom_length,[term(ab,[]), num(2.0)]),
    [exception(error(type_error(integer,num(2.0)),atom_length/2))]
).