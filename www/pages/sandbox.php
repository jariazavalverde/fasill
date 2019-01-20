<?php

$def_program = file_get_contents("sample/good_hotel.fpl");
$def_lattice = file_get_contents("sample/real.lat.pl");
$def_sim = file_get_contents("sample/good_hotel.sim.pl");
$def_goal = str_replace("\n", "", file_get_contents("sample/good_hotel.goal.fpl"));
$def_tests = file_get_contents("sample/good_hotel.test.fpl");
$def_limit = 1000;

$_PROGRAM = isset($_POST["program"]) ? $_POST["program"] : $def_program;
$_LATTICE = isset($_POST["lattice"]) ? $_POST["lattice"] : $def_lattice;
$_SIM = isset($_POST["sim"]) ? $_POST["sim"] : $def_sim;
$_GOAL = isset($_POST["goal"]) ? $_POST["goal"] : $def_goal;
$_TESTS = isset($_POST["tests"]) ? $_POST["tests"] : $def_tests;
$_LIMIT = isset($_POST["limit"]) ? $_POST["limit"] : $def_limit;

?>

<form action="./sandbox" method="POST">
	<div class="container">
		<h1>Input</h1>
		<div class="container px-0 py-4">
			<h4><i class="fas fa-code"></i> Program</h4>
			<div id="program" class="sandbox-editor"><?php echo $_PROGRAM; ?></div>
			<div class="text-right mt-2">
				<button onClick="fasill_listing();" type="button" class="btn btn-primary btn-sm">Unfold program</button>
			</div>
			<div id="listing"></div>
		</div>
		<div class="container px-0 py-4">
			<h4><i class="fas fa-circle"></i> Lattice</h4>
			<div id="lattice" class="sandbox-editor"><?php echo $_LATTICE; ?></div>
			<div class="text-right mt-2">
				<button type="button" class="btn btn-dark btn-sm ml-2" onClick="load_lattice('sample/bool.lat.pl');">bool</button>
				<button type="button" class="btn btn-dark btn-sm" onClick="load_lattice('sample/real.lat.pl');">real</button>
			</div>
		</div>
		<div class="container px-0 py-4">
			<h4><i class="fas fa-equals"></i> Similarity Relation</h4>
			<div id="sim" class="sandbox-editor"><?php echo $_SIM; ?></div>
		</div>
		<div class="container px-0">
			<div class="row">
				<div class="col-sm py-4">
					<h4><i class="fas fa-stopwatch"></i> Max. inferences</h4>
					<div id="limit"><?php echo $_LIMIT; ?></div>
				</div>
			</div>
		</div>

		<div class="btn-group py-4 btn-group-lg" role="toolbar" aria-label="Action">
			<button class="btn btn-primary" id="button-show-run" type="button" onClick="show_running();">Running</button>
			<button class="btn btn-secondary" id="button-show-tuning" type="button" onClick="show_tuning();">Tuning</button>
		</div>
		
		<div class="container px-0" id="collapse-run">
			<div class="row">
				<div class="col-sm">
					<h4><i class="fab fa-font-awesome-flag"></i> Goal</h4>
					<div id="goal"><?php echo $_GOAL; ?></div>
				</div>
				<div class="col-sm">
					<h4>&nbsp;</h4>
					<button id="run" onClick="fasill_run();" type="button" class="btn btn-danger btn btn-block">Run</button>
				</div>
			</div>
		</div>
		
		<div class="container px-0" id="collapse-tuning">
			<h4><i class="fas fa-vial"></i> Test cases</h4>
			<div id="tests"><?php echo $_TESTS; ?></div>
			<div class="mt-4">
				<button id="tuning" onClick="fasill_tuning();" type="button" class="btn btn-danger btn btn-block">Tune</button>
			</div>
		</div>
		
	</div>
</form>

<div class="container-sep"></div>

<div class="container pt-5">
	<h1>Output</h1>
	<div id="output-run">
		<div class="container px-0 py-4">
			<h4><i class="fas fa-search"></i> Fuzzy Computed Answers</h4>
			<div id="out"></div>
		</div>
		<div class="container px-0 py-4">
			<h4><i class="fas fa-tree"></i> Derivation tree</h4>
			<div id="derivation"></div>
			<div id="tree-container" class="text-center">
				<canvas id="tree" width="0" height="0"></canvas>
			</div>
		</div>
	</div>
	<div id="output-tuning">
		<div class="container px-0 py-4">
			<h4><i class="fas fa-search"></i> Symbolic substitution</h4>
			<div id="symbolic-substitution"></div>
		</div>
	</div>
</div>
