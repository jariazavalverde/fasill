<?php $_CATEGORY = $_GET["category"]; ?>
<div class="container">
	<h1 class="pb-2"><?php echo ucfirst(str_replace("-", " ", $_CATEGORY)); ?></h1>
	<?php include("pages/ref-doc/$_CATEGORY.php"); ?>
</div>
