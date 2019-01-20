<div class="container">
	<h1>Documentation</h1>
	<div class="container px-0 py-4">
		<h3 id="manual">FASILL Manual</h3>
		<ul>
			<li><a href="documentation/getting-started">Getting Started</a></li>
			<li><a href="documentation/operational-semantics">Operational Semantics</a></li>
		</ul>
	</div>
	<div class="container px-0 py-4">
		<h3 id="ref">FASILL Predicate Reference</h3>
		<ul>
<?php
foreach( scandir("pages/ref-doc") as $f ) {
	if( $f != "." && $f != "..") {
		$name = str_replace(".php", "", $f);
		$show = ucfirst(str_replace("-", " ", $name));
		echo "<li><a href=\"documentation/ref/$name\">$show</a></li>";
	}
}
?>
		</ul>
	</div>
	<div class="container px-0 py-4">
		<h3 id="src">Implementation details</h3>
		<ul>
<?php
foreach( scandir("pages/src-doc") as $f ) {
	if( $f != "." && $f != "..") {
		$name = str_replace(".php", "", $f);
		echo "<li><a href=\"documentation/src/$name\">$name.pl</a></li>";
	}
}
?>
		</ul>
	</div>
</div>

<div class="container py-4">
	<div class="container px-0">
		<h1>Acknowledgment <span class="text-secondary">(in alphabetical order)</span></h1>
		<ul>
			<li><a href="http://dectau.uclm.es/Gines.Moreno/" target="_blank">Ginés Moreno</a> (language design, documentation, suggestions)</li>
			<li><a href="http://dectau.uclm.es/Jaime.Penabad/" target="_blank">Jaime Penabad</a> (language design, documentation, suggestions)</li>
			<li><a href="http://www.josemariagarcia.es/" target="_blank">José M. García</a> (documentation)</li>
			<li><a href="http://dectau.uclm.es/Pascual.Julian/" target="_blank">Pascual Julián</a> (language design, documentation, suggestions)</li>
		</ul>
	</div>
</div>

<div class="container pt-4">
	<h1 id="references">References</h1>
	 <script src="https://bibbase.org/show?bib=https%3A%2F%2Fraw.githubusercontent.com%2Fjariazavalverde%2Ffasill%2Fmaster%2Fbibliography.bib&jsonp=1"></script> 
</div>
