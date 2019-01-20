<?php

$fpl = $_POST['program'];
$lat = $_POST['lattice'];
$sim = $_POST['sim'];
$rule = $_POST['rule'];

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
	$cmd = "timeout 10s swipl -f '../src/sandbox.pl' -g \"sandbox_unfold('$ran-program.fpl', '$ran-lat.pl', '$ran-sim.pl', '$rule'),halt\"";
	echo shell_exec( $cmd );
} catch (Exception $e) {
    echo "There was an error.";
}

unlink( "$ran-program.fpl" );
unlink( "$ran-lat.pl" );
unlink( "$ran-sim.pl" );
