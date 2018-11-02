?- consult(builtin).



% '='/2

% (real) <p = p,{}> -> [<1.0,{}>]
?- test_builtin(1, '../../sample/lat/real.lat.pl', term('=',[term(p,[]), term(p,[])]), [state(num(1.0), [])]).

% (real) <X = p,{}> -> [<1.0,{X/p}>]
?- test_builtin(2, '../../sample/lat/real.lat.pl', term('=',[var('X'), term(p,[])]), [state(num(1.0), ['X'/term(p,[])])]).

% (real) <(X = a &prod X = b),{}> -> [<0.0,{X/p}>]
?- test_builtin(3, '../../sample/lat/real.lat.pl',
    term('&'(and_prod),[term('=',[var('X'),term(a,[])]), term('=',[var('X'),term(b,[])])]),
    [state(num(0.0), ['X'/term(a,[])])]
).