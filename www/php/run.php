<?php

$fpl = $_POST['program'];
$lat = $_POST['lattice'];
$sim = $_POST['sim'];
$limit = $_POST['limit'];
$goal = $_POST['goal'];

$ran = rand(1000, 9999);

$file_fpl = fopen( "$ran-program.fpl", 'w' );
$file_lat = fopen( "$ran-lat.pl", 'w' );
$file_sim = fopen( "$ran-sim.pl", 'w' );
$file_goal = fopen( "$ran-goal.fpl", 'w' );
fwrite( $file_fpl, $fpl );
fwrite( $file_lat, $lat );
fwrite( $file_sim, $sim );
fwrite( $file_goal, $goal );
fclose( $file_fpl );
fclose( $file_lat );
fclose( $file_sim );
fclose( $file_goal );

try {
	$cmd = "timeout 10s swipl -f '../src/web.pl' -g \"web_run('$ran-program.fpl', '$ran-lat.pl', '$ran-sim.pl', '$ran-goal.fpl', $limit),halt\"";
	echo shell_exec( $cmd );
} catch (Exception $e) {
    echo "<div class=\"error-message\">There was an error.</div>";
}

unlink( "$ran-program.fpl" );
unlink( "$ran-lat.pl" );
unlink( "$ran-sim.pl" );
unlink( "$ran-goal.fpl" );
