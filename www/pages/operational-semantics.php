<div class="container">
	
	<h1>Operational Semantics</h1>

	<p class="text-justify">
		As a logic language, FASILL inherits the concepts of substitution, unifier and most general unifier (mgu).
		Some of them are extended to cope with similarities. Concretely, the most general unifier is replaced by the concept of <b>weak most general unifier</b>
		(wmgu) and a weak unification algorithm is introduced to compute it. Roughly speaking, the weak unification algorithm states that two expressions
		(i.e, terms or atomic formulas) f(t<sub>1</sub>, ..., t<sub>n</sub>) and g(s<sub>1</sub>, ..., s<sub>n</sub>) weakly unify if the root symbols f
		and g are close with a certain degree (i.e. R(f, g) = r > ⊥) and each of their arguments t<sub>i</sub> and s<sub>i</sub> weakly unify. Therefore,
		there is a weak unifier for two expressions even if the symbols at their roots are not syntactically equals (f ≢ g).
	</p>
	<p class="text-justify">
		More technically, the weak unification algorithm we are using is a reformulation/extension of the one which appears in <a href="https://www.sciencedirect.com/science/article/pii/S0304397501001888?via%3Dihub" target="_blank">[Approximate reasoning by similarity-based SLD resolution]</a> for arbitrary complete lattices.
		We formalize it as a transition system supported by a similarity-based unification relation (⇒). The unification of the expressions E<sub>1</sub> and E<sub>2</sub>
		is obtained by a state transformation sequence starting from an initial state &lt;G ≡ {E<sub>1</sub> ≈ E<sub>2</sub>}, id, α<sub>0</sub>&gt;, where id is the identity
		substitution and α<sub>0</sub> = ⊤ is the supreme of (L,≤): &lt;G, id, α<sub>0</sub>&gt; ⇒ &lt;G<sub>1</sub>, θ<sub>1</sub>, α<sub>1</sub>&gt; ⇒ ... ⇒ &lt;G<sub>n</sub>, θ<sub>n</sub>, α<sub>n</sub>&gt;.
		When the final state &lt;G<sub>n</sub>, θ<sub>n</sub>, α<sub>n</sub>&gt;, with G<sub>n</sub>= &empty;, is reached (i.e., the equations in the initial state have
		been solved), the expressions E<sub>1</sub> and E<sub>2</sub> are unifiable by similarity with wmgu θ<sub>n</sub> and unification degree α<sub>n</sub>.
		Therefore, the final state &lt;G<sub>n</sub>, θ<sub>n</sub>, α<sub>n</sub>&gt; signals out the unification success. On the other hand, when expressions
		E<sub>1</sub> and E<sub>2</sub> are not unifiable, the state transformation sequence ends with failure (i.e., G<sub>n</sub> = Fail).
	</p>
	<p class="text-justify">
		The similarity-based unification relation, (⇒), is defined as the smallest relation derived by the
		following set of transition rules (where Var(t) denotes the set of variables of a given term t):
	</p>
	<p class="text-center"><img src="img/wmgu.png" title="Weak Unification" alt="Weak Unification" /></p>
	<p class="text-justify">
		Rule 1 decomposes two expressions and annotates the relation between the function (or predicate) symbols
		at their root. The second rule eliminates spurious information and the fourth rule interchanges the
		position of the symbols to be handled by other rules. The third and fifth rules perform an occur check of
		variable X in a term t. In case of success, it generates a substitution {X/t}; otherwise the algorithm ends
		with failure. It can also end with failure if the relation between function (or predicate) symbols in R is
		⊥, as stated by Rule 6.
	</p>
	
	<p class="text-justify">
		Rules in a FASILL program have the same role than clauses in Prolog
		programs, that is, stating that a certain predicate relates some terms (the head) if some conditions (the
		body) hold. The procedural semantics of FASILL is defined in a stepwise manner as follows. First, an operational stage is introduced
		which proceeds similarly to SLD resolution in pure logic programming, returning an expression still containing values and
		connectives. Then, an interpretive stage evaluates these connectives and produces a final answer.
	</p>
	<p>
		Let Q be a goal and σ a substitution. The pair &lt;Q; σ&gt; is a state. Given a FASILL program &lt;Π, R, L&gt; and a t-norm ∧ in L,
		a computation is formalized as a state transition system, whose transition relation (&zigrarr;) is the smallest relation satisfying these rules:
	</p>
	<p class="text-center"><img src="img/semantics.png" title="Operational Semantics" alt="Operational Semantics" style="max-width: 900px;" /></p>
	<p>
		A derivation is a sequence of arbitrary lenght &lt;Q; id&gt; &zigrarr;<sup>*</sup> &lt;Q'; σ&gt;. As usual, rules are renamed apart.
		When Q' = r ∈ L, the state &lt;r; σ&gt; is called a <b>fuzzy computed answer</b> (fca) for that derivation.
	</p>
</div>
