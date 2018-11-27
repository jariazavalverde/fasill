<?php

$fpl = $_POST['program'];
$lat = $_POST['lattice'];
$sim = $_POST['sim'];
$limit = $_POST['limit'];
$tests = $_POST['tests'];

$ran = rand(1000, 9999);

$file_fpl = fopen( "$ran-program.fpl", 'w' );
$file_lat = fopen( "$ran-lat.pl", 'w' );
$file_sim = fopen( "$ran-sim.pl", 'w' );
$file_tests = fopen( "$ran-tests.fpl", 'w' );
fwrite( $file_fpl, $fpl );
fwrite( $file_lat, $lat );
fwrite( $file_sim, $sim );
fwrite( $file_tests, $tests );
fclose( $file_fpl );
fclose( $file_lat );
fclose( $file_sim );
fclose( $file_tests );

try {
	$cmd = "timeout 10s swipl -f '../src/sandbox.pl' -g \"sandbox_tune('$ran-program.fpl', '$ran-lat.pl', '$ran-sim.pl', '$ran-tests.fpl', $limit, [runtime]),halt\"";
	echo shell_exec( $cmd );
} catch (Exception $e) {
    echo "There was an error.";
}

unlink( "$ran-program.fpl" );
unlink( "$ran-lat.pl" );
unlink( "$ran-sim.pl" );
unlink( "$ran-tests.fpl" );
