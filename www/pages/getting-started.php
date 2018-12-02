<div class="container">
	
	<h1>Getting Started</h1>
	
	<ul>
		<li><a href="documentation/getting-started#what-is">What is FASILL?</a></li>
		<li><a href="documentation/getting-started#programs">Programs</a></li>
		<li><a href="documentation/getting-started#console">Interactive console</a></li>
	</ul>

	<h2 id="what-is" class="pt-4">What is FASILL?</h2>
	
	<p class="text-justify">
		Logic programming has been widely used for problem solving and knowledge representation in the past.
		Nevertheless, traditional logic programming languages do not incorporate techniques or constructs to treat explicitly
		with uncertainty and approximated reasoning. To overcome this situation, during the last decades several
		fuzzy logic programming systems have been developed where the classical inference mechanism of SLD-Resolution
		has been replaced with a fuzzy variant able to handle partial truth and to reason with uncertainty. Most of
		these systems implement the fuzzy resolution principle introduced by Lee in
		<a href="https://dl.acm.org/citation.cfm?id=1622935" target="_blank">[Fuzzy Logic and the Resolution Principle]</a>.
	</p>
	
	<p class="text-justify">
		<b>FASILL</b> (acronym of <i>Fuzzy Aggregators and Similarity Into a Logic Language</i>) is a fuzzy logic programming language with
		implicit/explicit truth degree annotations, a great variety of connectives and unification by similarity. FASILL integrates and
		extends features coming from <b>MALP</b> (<i>Multi-Adjoint Logic Programming</i>, a fuzzy logic language with explicitly annotated rules)
		and <b>Bousi∼Prolog</b> (which uses a weak unification algorithm and is well suited for flexible query answering). Hence, it properly manages
		similarity and truth degrees in a single framework combining the expressive benefits of both languages.
	</p>
	
	<h2 id="programs" class="pt-4">Programs</h2>
	
	<p class="text-justify">
		A FASILL program is a tuple <code>&lt;Π, R, L&gt;</code> where <code>Π</code> is a set of rules, <code>R</code> is a similarity relation between the elements of the signature
		<code>Σ</code> of <code>Π</code>, and <code>L</code> is a complete lattice.
	</p>
	
	<h4 id="rules" class="mt-4">Rules</h4>
	
	<p class="text-justify">
		A rule is a formula <code>A ← B</code>, where <code>A</code> is an atomic formula (usually called the head) and <code>B</code> (which is called the body) is a
		formula built from atomic formulas (<code>B<sub>1</sub></code>, ..., <code>B<sub>n</sub></code>), truth values of <code>L</code> and conjunctions, disjunctions
		and aggregations. Rules with an empty body are called facts. A goal is a body submitted as a query to the system. Variables in a rule are
		assumed to be governed by universal quantifiers.
	</p>
		
	<pre><code class="prolog">vanguardist(hydropolis) <- 0.9.
elegant(ritz)           <- 0.8.
close(hydropolis, taxi) <- 0.7.
good_hotel(X)           <- @aver(elegant(X), @very(close(X, metro))).</code></pre>

	<h4 id="lattices" class="mt-4">Complete lattices</h4>
	
	<p class="text-justify">
		A complete lattice is a partially ordered set in which all subsets have both a supremum and an infimum.
	</p>

	<p class="text-justify">
		All relevant components of each lattice can be encapsulated inside a Prolog file which must contain the definitions of a minimal
		set of predicates defining the set of valid elements (including special mentions to the "top" and "bottom" ones), the full or
		partial ordering established among them, as well as the repertoire of fuzzy connectives which can be used for their subsequent manipulation.
	</p>
	
	<ul>
		<li><p class="text-justify"><code>member/1</code> which is satisfied when being called with a parameter representing a valid truth degree.</p></li>
		<li><p class="text-justify"><code>members/1</code> which returns in one go a list containing the whole set of truth degrees.</p></li>
		<li><p class="text-justify"><code>bot/1</code> and <code>top/1</code> answer with the top and bottom element of the lattice, respectively.</p></li>
		<li><p class="text-justify"><code>leq/2</code> models the ordering relation among all the possible pairs of truth degrees, and it is only satisfied when it is invoked with two elements verifying that the first parameter is equal or smaller than the second one.</p></li>
		<li><p class="text-justify">Finally, given some fuzzy connectives of the form &amp;<sub>label1</sub> (conjunction), |<sub>label2</sub> (disjunction) or @<sub>label3</sub> (aggregation) with arities n1, n2 and n3 respectively, we must provide clauses defining the connective predicates <code>and_label1/(n1+1)</code>, <code>or_label2/(n2+1)</code> and <code>agr_label3/(n3+1)</code>, where the extra argument of each predicate is intended to contain the result achieved after the evaluation of the proper connective.</p></li>
	</ul>
	
	<pre><code class="prolog">% Elements
member(X) :- number(X), 0 =< X, X =< 1.
members([0.0,0.1,0.2,0.3,0.4,0.5,0.6,0.7,0.8,0.9,1.0]).

% Distance
distance(X,Y,Z) :- Z is abs(Y-X).

% Ordering relation
leq(X,Y) :- X =< Y.

% Supremum and infimum
bot(0.0).
top(1.0).

% Binary operations
and_prod(X,Y,Z) :- Z is X*Y.
and_godel(X,Y,Z) :- Z is min(X,Y).
and_luka(X,Y,Z) :- Z is max(X+Y-1,0).
or_prod(X,Y,Z) :- U1 is X*Y, U2 is X+Y, Z is U2-U1.
or_godel(X,Y,Z) :- Z is max(X,Y).
or_luka(X,Y,Z) :- Z is min(X+Y,1).

% Aggregators
agr_aver(X,Y,Z) :- Z is (X+Y)/2.
agr_very(X,Y) :- Y is X*X.

% Default connectives
tnorm(godel).
tconorm(godel).</code></pre>

	<h4 id="simlarities" class="mt-4">Similarity relations</h4>
	
	<p class="text-justify">
		Given a domain <code>U</code> and a lattice <code>L</code> with a fixed t-norm, a similarity relation <code>R</code> is a fuzzy binary relation on U fulfilling the reflexive,
		symmetric and transitive properties.
	</p>

	<p class="text-justify">
		FASILL takes a set of similarity equations <code>f/n ~ g/n = r</code>, where <code>f</code> and <code>g</code> are propositional variables or constants and <code>r</code>
		is an element of <code>L</code>, and generates a valid similarity relation by applying the reflexive, symmetric and transitive closures over the initial scheme.
	</p>
	
	<pre><code class="prolog">elegant/1 ~ vanguardist/1 = 0.6.
metro ~ bus = 0.5.
bus ~ taxi = 0.4.
~tnorm = godel.</code></pre>

	<h2 id="console" class="pt-4">Interactive console</h2>
	
	<p class="text-justify">
		You can download and install FASILL from <a href="http://dectau.uclm.es/fasill/downloads#install">here</a>. Once installed, you can run the interactive console of FASILL by typing <kbd>fasill</kbd> on a terminal. <code>fasill&gt;</code> is the prompt of FASILL.
	</p>
	
<pre><code class="bash">$ fasill
FASILL (pre-alfa): http://dectau.uclm.es/fasill/
Copyright (C) 2018 José Antonio Riaza Valverde
Released under the BSD-3 Clause license
fasill> </code></pre>

	<p class="text-justify">
		Now, you can execute FASILL goals or commands.
	</p>
	
	<h4 id="commands" class="mt-4">Commands</h4>
	
	<p class="text-justify">
		A command is a FASILL term preceded by the character (<code>:</code>).
	</p>
	
	<ul>
		<li><code>:exit</code> – exit FASILL.</li>
		<li><code>:help</code> – print this message.</li>
		<li><code>:lattice(Path)</code> – change lattice from file <code>Path</code>.</li>
		<li><code>:license</code> – print license message.</li>
	</ul>
	
	<p class="text-justify">
		By default, FASILL incorporates a set of predefined lattices, and loads the lattice <code>([0,1], &le;)</code> into the environment.
		You can change the current lattice with the command <code>:lattice(Path)</code>. If <code>Path</code> is a term of the form <code>library(Name)</code>
		instead of a file path, FASILL finds in its predefined lattices:
	</p>
	
	<ul>
		<li><code>:lattice(library(real))</code> – reals in the unit interval with logics of product, Gödel and Łukasiewicz.</li>
		<li><code>:lattice(library(bool))</code> – boolean values with classical operators.</li>
	</ul>
	
	<p class="text-justify">
		You can directly run FASILL with a different lattice with the option <kbd>fasill -lat &lt;lattice&gt;</kbd>.
	</p>
	
	<h4 id="goals" class="mt-4">Goals</h4>
	
	<p class="text-justify">
		FASILL reads the input until the first break line, analyzes the term and runs the goal. After the first answer, you can press the key (<code>;</code>)
		to find the next answer, or any other to end the search.
	</p>
	
<pre><code class="bash">fasill> consult('sample/program/good_hotel.fpl').
< 1.0, {} > .

fasill> consult_sim('sample/sim/good_hotel.sim.pl').
< 1.0, {} > .

fasill> good_hotel(X).
< 0.38, {X/hydropolis} > ;
< 0.4, {X/ritz} > ;

fasill></code></pre>

</div>
