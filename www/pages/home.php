<div class="container">
	<img class="img-fluid mb-3" src="img/colorx2048.png" alt="FASILL" />
	<div class="container px-0 pt-4">
			<h3>What is FASILL?</h3>
			<div class="row">
				<div class="col-md pt-2 pb-4">
					<p class="text-justify text-secondary">
						FASILL is a Prolog-like first order language containing variables, function symbols, predicate symbols and constants.
						To increase language expressiveness, FASILL also contains the truth values of a complete lattice, equipped with a collection of connectives to combine/propagate truth values through the rules.
					</p>
				</div>
				<div class="col-md pt-2 pb-4 text-center">
					<a href="sandbox" title="Try example"><img class="img-fluid" src="sample/good_hotel.png" alt="good_hotel.fpl" /></a>
				</div>
			</div>
		</div>
	</div>
	<div class="container px-0 pt-4">
		<div class="row">
			<div class="col-sm">
				<h4 class="text-center">Rules</h4>
				<p class="text-justify">A FASILL program is a tuple &lt;Π, R, L&gt; where Π is a set of rules, R is a similarity relation between the elements of the signature Σ of Π, and L is a complete lattice. A rule has the form A ← B, where A is an atomic formula called head and B, called body, is a well-formed formula (ultimately built from atomic formulas B1, ..., Bn, truth values of the lattice and connectives).</p>
			</div>
			<div class="col-sm">
				<h4 class="text-center">Complete lattices</h4>
				<p class="text-justify">All relevant components of each lattice can be encapsulated inside a Prolog file which must contain the definitions of a minimal set of predicates defining the set of valid elements (including special mentions to the "top" and "bottom" ones), the full or partial ordering established among them, as well as the repertoire of fuzzy connectives which can be used for their subsequent manipulation.</p>
			</div>
		</div>
		<div class="row">
			<div class="col-sm">
				<h4 class="text-center">Similarity Relations</h4>
				<p class="text-justify">Given a domain U and a lattice L with a fixed t-norm, a similarity relation R is a fuzzy binary relation on U fulfilling the reflexive, symmetric and transitive properties. FASILL takes a set of similarity equations f/n ~ g/n = r, where f and g are propositional variables or constants and r is an element of L, and generates a valid similarity relation by applying the reflexive, symmetric and transitive closures over the initial scheme.</p>
			</div>
			<div class="col-sm">
				<h4 class="text-center">Built-in predicates</h4>
				<p class="text-justify">FASILL has a large set of built-in predicates for arithmetic comparison, arithmetic evaluation, atom processing, control constructs, term comparison, term unification, type testing, exceptions, list manipulation, etc.</p>
			</div>
		</div>
	</div>
</div>
