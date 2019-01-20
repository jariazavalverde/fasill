<?php

/** Show template */
function show_template( $template ) {
	$template = explode( '(', $template );
	$html = '<span class="predicate-template-name">' . trim( $template[0] ) . '</span>';
	if( count( $template ) > 1 ) {
		$html .= '<span class="predicate-template-paren">( </span>';
		$template = str_replace( ')', '', $template[1] );
		$args = explode( ',', $template );
		for( $i = 0; $i < count( $args ); $i++ ) {
			if( $i > 0 ) $html .= '<span class="predicate-template-paren">, </span>';
			$arg = trim( $args[$i] );
			if( $arg[0] == '+' ) $class = 'plus';
			elseif( $arg[0] == '?' ) $class = 'query';
			elseif( $arg[0] == '-' ) $class = 'minus';
			elseif( $arg[0] == '@' ) $class = 'arroba';
			elseif( $arg[0] == ':' ) $class = 'dots';
			else $class = 'generic';
			$html .= '<span class="predicate-template-argument-' . $class . '">' . $arg . '</span>';
		}
		$html .= '<span class="predicate-template-paren"> )</span>';
	}
	return '<div class="predicate-template">' . $html . '</div>';
}

/** Show description */
function show_description( $desc ) {
	$words = explode(" ", $desc);
	$html = "";
	foreach( $words as $w ) {
		if( $w[0] == '+' ) $class = 'plus';
		elseif( $w[0] == '?' ) $class = 'query';
		elseif( $w[0] == '-' ) $class = 'minus';
		elseif( $w[0] == '@' ) $class = 'arroba';
		elseif( $w[0] == ':' ) $class = 'dots';
		else $class = false;
		if( $class != false ) {
			$html .= ' <span class="predicate-template-argument-' . $class . '">' . $w . '</span>';
		} else {
			$html .= " $w";
		}
	}
	return $html;
}
