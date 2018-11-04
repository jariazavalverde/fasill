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
    [exception(term(error,[term(instantiation_error,[]),term(/,[term(atom_length,[]),num(2)])]))]
).

% (real) <atom_length(5, Y),{}> -> error(type_error(atom,5), atom_length/2)
?- test_builtin(1, '../../sample/lat/real.lat.pl',
    term(atom_length,[num(5), var('Y')]),
    [exception(term(error,[term(type_error,[term(atom,[]),num(5)]),term('/',[term(atom_length,[]),num(2)])]))]
).

% (real) <atom_length(ab, 2.0),{}> -> error(type_error(integer,2,0), atom_length/2)
?- test_builtin(1, '../../sample/lat/real.lat.pl',
    term(atom_length,[term(ab,[]), num(2.0)]),
    [exception(term(error,[term(type_error,[term(integer,[]),num(2.0)]),term('/',[term(atom_length,[]),num(2)])]))]
).



% ATOM_CONCAT/3

% (real) <atom_concat(ab, cd, abcd),{}> -> [<1.0,{}>]
?- test_builtin(1, '../../sample/lat/real.lat.pl',
    term(atom_concat,[term(ab,[]), term(cd,[]), term(abcd,[])]),
    [state(num(1.0), [])]
).

% (real) <atom_concat(ab, cd, X),{}> -> [<1.0,{X/abcd}>]
?- test_builtin(1, '../../sample/lat/real.lat.pl',
    term(atom_concat,[term(ab,[]), term(cd,[]), var('X')]),
    [state(num(1.0), ['X'/term(abcd,[])])]
).

% (real) <atom_concat(X, Y, abc),{}> -> [<1.0,{}>]
?- test_builtin(1, '../../sample/lat/real.lat.pl',
    term(atom_concat,[var('X'), var('Y'), term(abc,[])]),
    [state(num(1.0),['X'/term('',[]),'Y'/term(abc,[])]),state(num(1.0),['X'/term(a,[]),'Y'/term(bc,[])]),state(num(1.0),['X'/term(ab,[]),'Y'/term(c,[])]),state(num(1.0),['X'/term(abc,[]),'Y'/term('',[])])]
).