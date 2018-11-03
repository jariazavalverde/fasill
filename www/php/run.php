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
fwrite( $file_fpl, $fpl );
fwrite( $file_lat, $lat );
fwrite( $file_sim, $sim );
fclose( $file_fpl );
fclose( $file_lat );
fclose( $file_sim );

try {
	$cmd = "nice -n15 swipl -f '../src/web.pl' -g \"web_run('$ran-program.fpl', '$ran-lat.pl', '$ran-sim.pl', '$goal', $limit),halt\"";
	echo shell_exec( $cmd );
} catch (Exception $e) {
    echo "<div class=\"error-message\">There was an error.</div>";
}

unlink( "$ran-program.fpl" );
unlink( "$ran-lat.pl" );
unlink( "$ran-sim.pl" );
