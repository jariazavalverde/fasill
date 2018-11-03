<?php

$def_program = file_get_contents("sample/good_hotel.fpl");
$def_lattice = file_get_contents("sample/real.lat.pl");
$def_sim = file_get_contents("sample/good_hotel.sim.pl");
$def_goal = str_replace("\n", "", file_get_contents("sample/good_hotel.goal.fpl"));
$def_limit = 1000;

$_PROGRAM = isset($_POST["program"]) ? $_POST["program"] : $def_program;
$_LATTICE = isset($_POST["lattice"]) ? $_POST["lattice"] : $def_lattice;
$_SIM = isset($_POST["sim"]) ? $_POST["sim"] : $def_sim;
$_GOAL = isset($_POST["goal"]) ? $_POST["goal"] : $def_goal;
$_LIMIT = isset($_POST["limit"]) ? $_POST["limit"] : $def_limit;

?>

<form action="." method="POST">
	<div class="container">
		<h1>Input</h1>
		<div class="container container-sandbox">
			<h4>Program</h4>
			<div id="program" class="sandbox-editor"><?php echo $_PROGRAM; ?></div>
		</div>
		<div class="container container-sandbox">
			<h4>Lattice</h4>
			<div id="lattice" class="sandbox-editor"><?php echo $_LATTICE; ?></div>
		</div>
		<div class="container container-sandbox">
			<h4>Similarity Relation</h4>
			<div id="sim" class="sandbox-editor"><?php echo $_SIM; ?></div>
		</div>
		<div class="container container-sandbox">
			<div class="row">
				<div class="col-sm">
					<h4>Goal</h4>
					<div id="goal"><?php echo $_GOAL; ?></div>
				</div>
				<div class="col-sm">
					<h4>Limit</h4>
					<div id="limit"><?php echo $_LIMIT; ?></div>
				</div>
				<div class="col-sm">
					<h4>Answers</h4>
					<button type="submit" class="btn btn-danger btn-lg btn-block">Run</button>
				</div>
			</div>
		</div>
	</div>
</form>

<div class="container-sep"></div>

<div class="container">
	<h1>Output</h1>
</div>
