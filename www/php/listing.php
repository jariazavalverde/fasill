<?php

$fpl = $_POST['program'];
$ran = rand(1000, 9999);
$file_fpl = fopen( "$ran-program.fpl", 'w' );
fwrite( $file_fpl, $fpl );

try {
	$cmd = "timeout 10s swipl -f '../src/sandbox.pl' -g \"sandbox_listing('$ran-program.fpl'),halt\"";
	echo shell_exec( $cmd );
} catch (Exception $e) {
    echo "There was an error.";
}

unlink( "$ran-program.fpl" );
