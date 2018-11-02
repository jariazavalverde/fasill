?- consult(builtin).



% ATOM_LENGTH/2

% (real) <atom_length(abc, 3),{}> -> [<1.0,{}>]
?- test_builtin(1, '../../sample/lat/real.lat.pl',
    term(atom_length,[term(abc,[]), num(3)]),
    [state(num(1.0), [])]
).