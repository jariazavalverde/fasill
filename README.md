# FASILL

## Fuzzy Aggregators and Similarities Into a Logic Language

**FASILL** is a first order language containing variables, function symbols, predicate symbols, constants and several (arbitrary) connectives to increase language expressiveness. FASILL uses connectives to combine/propagate truth values through the rules: **conjunctive operators** (denoted by &amp;<sub>1</sub>, &amp;<sub>2</sub>, ..., &amp;<sub>k</sub>), **disjunctive operators** (|<sub>1</sub>, |<sub>2</sub>, ..., |<sub>j</sub>), and **aggregation operators** (usually denoted by @<sub>1</sub>, @<sub>2</sub>, ..., @<sub>n</sub>). Additionally, FASILL contains the truth values of a complete lattice equipped with a collection of connectives.

A **rule** has the form A &larr; B, where A is an atomic formula called head and B, called body, is a well-formed formula (ultimately built from atomic formulas B<sub>1</sub>, ..., B<sub>n</sub>, truth values of the lattice and connectives). A FASILL program is a tuple <Π, R, L> where Π is a set of rules, R is a similarity relation between the elements of the signature Σ of Π, and L is a complete lattice. Given a domain U and a lattice L with a fixed t-norm ∧, a **similarity relation** R is a fuzzy binary relation on U fulfilling the reflexive, symmetric and transitive properties.
