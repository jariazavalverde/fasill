<div class="container">
	<h1>Documentation</h1>
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
	<div class="container px-0 pt-4 pb-0">
		<h3>Acknowledgment <span class="text-secondary">(in alphabetical order)</span></h3>
		<ul>
			<li><a href="http://dectau.uclm.es/Gines.Moreno/" target="_blank">Ginés Moreno</a> (suggestions)</li>
			<li><a href="http://dectau.uclm.es/Jaime.Penabad/" target="_blank">Jaime Penabad</a> (suggestions)</li>
			<li><a href="http://www.josemariagarcia.es/" target="_blank">José M. García</a> (documentation)</li>
			<li><a href="http://dectau.uclm.es/Pascual.Julian/" target="_blank">Pascual Julián</a> (suggestions)</li>
		</ul>
	</div>
</div>
