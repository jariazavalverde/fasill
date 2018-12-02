<div class="container">
	<div class="container pb-4">
		<img class="img-fluid mb-3" src="img/colorx2048.png" alt="FASILL" />
	</div>
	<div class="container py-4">
		<h3>What is FASILL?</h3>
		<p class="text-justify text-secondary" style="font-size: 120%;">
			FASILL is a Prolog-like first order language containing variables, function symbols, predicate symbols and constants.
			To increase language expressiveness, FASILL also contains the truth values of a complete lattice, equipped with a collection of connectives to combine/propagate truth values through the rules.
		</p>
	</div>
	<div class="container pb-4">
		<div class="row">
			<div class="col-sm">
				<h4 class="text-center">Rules</h4>
				<p class="text-justify">A FASILL program is a tuple &lt;Π, R, L&gt; where Π is a set of rules, R is a similarity relation between the elements of the signature Σ of Π, and L is a complete lattice. A rule has the form A ← B, where A is an atomic formula called head and B, called body, is a well-formed formula (built from atomic formulas B<sub>1</sub>, ..., B<sub>n</sub>, truth values of the lattice and connectives).</p>
			</div>
			<div class="col-sm">
				<h4 class="text-center">Complete Lattices</h4>
				<p class="text-justify">All relevant components of each lattice can be encapsulated inside a Prolog file which must contain the definitions of a minimal set of predicates defining the set of valid elements, the full or partial ordering established among them, as well as the repertoire of fuzzy connectives which can be used for their subsequent manipulation.</p>
			</div>
		</div>
		<div class="row">
			<div class="col-sm pb-4">
				<a href="sandbox" title="Try example"><img class="img-fluid" src="sample/good_hotel.png" alt="good_hotel.fpl" /></a>
			</div>
			<div class="col-sm pb-4">
				<a href="sandbox" title="Try example"><img class="img-fluid" src="sample/real.png" alt="real.lat.pl" /></a>
			</div>
		</div>
		<div class="row">
			<div class="col-sm pb-4">
				<h4 class="text-center">Similarity Relations</h4>
				<p class="text-justify">Given a domain U and a lattice L with a fixed t-norm, a similarity relation R is a fuzzy binary relation on U fulfilling the reflexive, symmetric and transitive properties. FASILL takes a set of similarity equations f/n ~ g/n = r, where f and g are propositional variables or constants and r is an element of L, and generates a valid similarity relation by applying the reflexive, symmetric and transitive closures over the initial scheme.</p>
				<a href="sandbox" title="Try example"><img class="img-fluid" src="sample/sim.png" alt="good_hotel.sim.pl" /></a>
			</div>
			<div class="col-sm pb-4">
				<h4 class="text-center">Built-in Predicates</h4>
				<p class="text-justify">FASILL has a large set of built-in predicates for arithmetic comparison, arithmetic evaluation, atom processing, control constructs, term comparison, term unification, type testing, list manipulation, etc.</p>
				<a href="documentation#ref" class="btn btn-primary btn-block" role="button" aria-pressed="true">See FASILL Predicate Reference</a>
			</div>
		</div>
	</div>
	<div class="container pt-4">
		<h3>Weak Unification and Operational Semantics</h3>
		<p class="text-justify text-secondary" style="font-size: 120%;">As a logic language, FASILL inherits the concepts of substitution, unifier and most general unifier. Some of them are extended to cope with similarities. Concretely, the most general unifier is replaced by the concept of weak most general unifier and a weak unification algorithm is introduced to compute it.</p>
		<p class="text-justify text-secondary" style="font-size: 120%;">The procedural semantics of FASILL is defined in a stepwise manner. First, an operational stage is introduced which proceeds similarly to SLD resolution in pure logic programming, returning an expression still containing values and connectives. Then, an interpretive stage evaluates these connectives and produces a final answer.</p>
		<p><a href="documentation/operational-semantics" class="btn btn-primary" role="button" aria-pressed="true">More about Operational Semantics</a></p>
	</div>
</div>
