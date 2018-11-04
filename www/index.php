<?php

$_VIEW = isset($_GET["view"]) ? $_GET["view"] : "home";

?>
<!doctype html>
<html lang="en">
	<head>
		<meta charset="utf-8">
		<meta name="author" content="José Antonio Riaza Valverde" />
		<meta name="viewport" content="width=device-width, initial-scale=1, shrink-to-fit=no">
		<!-- Bootstrap CSS -->
		<link rel="stylesheet" href="https://stackpath.bootstrapcdn.com/bootstrap/4.1.3/css/bootstrap.min.css" integrity="sha384-MCw98/SFnGE8fJT3GXwEOngsV7Zt27NXFoaoApmYm81iuXoPkFOJwJ8ERdknLPMO" crossorigin="anonymous">
		<link rel="stylesheet" href="https://use.fontawesome.com/releases/v5.5.0/css/all.css" integrity="sha384-B4dIYHKNBt8Bc12p+WXckhzcICo0wtJAoU8YZTY5qE0Id1GSseTk6S+L3BlXeVIU" crossorigin="anonymous">
		<link rel="stylesheet" href="css/fasill.css">
		<!-- jQuery first, then Popper.js, Bootstrap JS -->
		<script src="https://code.jquery.com/jquery-3.3.1.slim.min.js" integrity="sha384-q8i/X+965DzO0rT7abK41JStQIAqVgRVzpbzo5smXKp4YfRvH+8abtTE1Pi6jizo" crossorigin="anonymous"></script>
		<script src="https://cdnjs.cloudflare.com/ajax/libs/popper.js/1.14.3/umd/popper.min.js" integrity="sha384-ZMP7rVo3mIykV+2+9J3UJ46jBk0WLaUAdn689aCwoqbBJiSnjAK/l8WvCWPIPm49" crossorigin="anonymous"></script>
		<script src="https://stackpath.bootstrapcdn.com/bootstrap/4.1.3/js/bootstrap.min.js" integrity="sha384-ChfqqxuZUCnJSK3+MXmPNIyE6ZbWh2IMqE241rYiqJxyMiZ6OW/JmZQ5stwEULTy" crossorigin="anonymous"></script>
		<!-- Codemirror -->
		<script src="codemirror/lib/codemirror.js"></script>
		<link rel="stylesheet" href="codemirror/lib/codemirror.css">
		<link rel="stylesheet" href="codemirror/theme/fasill.css">
		<script src="codemirror/addon/mode/simple.js"></script>
		<script src="codemirror/mode/prolog/prolog.js"></script>
		<script src="codemirror/addon/placeholder/placeholder.js"></script>
		<script src="js/fasill.js"></script>
		<title>FASILL</title>
	</head>
	<body>
		<div class="container" id="nav">
			<div class="row">
				<div class="col-sm"><a href="./">Home</a></div>
				<div class="col-sm"><a href="./downloads">Downloads</a></div>
				<div class="col-sm"><a href="./documentation">Documentation</a></div>
				<div class="col-sm"><a href="./sandbox">Sandbox</a></div>
			</div>
		</div>
		<div class="container px-0 " id="body">
			<?php include("pages/$_VIEW.php"); ?>
		</div>
		<div class="container" id="footer">
			<p><i class="far fa-copyright"></i> 2018 <a href="http://jariaza.es" title="jariaza.es" target="_blank">José Antonio Riaza Valverde</a> | <i class="fab fa-github"></i> <a href="https://github.com/jariazavalverde/fasill" title="GitHub" target="_blank">jariazavalverde/fasill</a> | <i class="fas fa-university"></i> <a href="http://uclm.es" target="_blank">University of Castilla-La Mancha</a>, <a href="dectau.uclm.es">DEC-Tau</a> research group</p>
			<p><i class="fas fa-balance-scale"></i> Released under the <a href="https://github.com/jariazavalverde/fasill/blob/master/LICENSE" target="_blank">BSD-3 Clause license</a> | <i class="fas fa-font"></i> Uses <a href="https://fontawesome.com/" target="_blank" rel="nofollow">Font Awesome</a> and <a href="https://getbootstrap.com/" target="_blank" rel="nofollow">Bootstrap</a></p>
		</div>
	</body>
</html>
