<?php $_MODULE = $_GET["module"]; ?>
<div class="container">
	<h1 class="pb-2"><?php echo $_MODULE; ?> module</h1>
	<?php include("pages/src-doc/$_MODULE.php"); ?>
</div>
