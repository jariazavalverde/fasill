(function() {

	var get_tree = function( str ) {
		str = str.replace(/\n\n/g, "");
		var lines = str.split("\n");
		var j = 0;
		while( j < lines.length && lines[j].indexOf(",") === -1 )
			j++;
		var tree = [[get_node(lines[j], 0, 0)]];
		for( var i = j + 1; i < lines.length; i++ ) {
			if (lines[i].indexOf(",") != -1) {
				var deep = (lines[i].match(/  /g) || []).length;
				var parent = tree[deep - 1].length - 1;
				if( tree.length == deep )
					tree.push([]);
				tree[deep].push( get_node( lines[i], deep, parent ) );
			}
		}
		return tree;
	};
	
	var get_node = function( str, deep, parent ) {
		obj = {};
		obj.deep = deep;
		obj.parent = parent;
		obj.rule = str.split(" <")[0].replace(/ /g, "");
		obj.goal = str.split(" <")[1].split(", {")[0].replace(/ /g, "");
		obj.goal = obj.goal.length > 100 ? obj.goal.substring(0, 100) + "..." : obj.goal;
		obj.subs = "{" + str.split("<")[1].split(", {")[1].replace("}>", "}").replace(/ /g, "");
		obj.subs = obj.subs.length > 100 ? obj.unifier.substring(0, 100) + "..." : obj.subs;
		obj.width = width;
		return obj;
	};

	var width = function( ctx, font, margin, padding ) {
		ctx.font = font;
		ctx.textAlign = "center";
		return Math.max( ctx.measureText( this.goal ).width, ctx.measureText( this.subs ).width ) + ( 2 * margin ) + ( 2 * padding );
	};
	
	var set_style = function( obj, name, value ) {
		if( typeof obj[name] === "undefined" )
			obj[name] = value;
	};

	var draw_tree = function( string, canvas, styles ) {
		styles = styles ? styles : {};
		set_style( styles, "font-size", 14 );
		set_style( styles, "font-family", "Monospace, Courier New" );
		set_style( styles, "font", styles["font-size"] + "px " + styles["font-family"] );
		set_style( styles, "border-width", 2 );
		set_style( styles, "border-color", "#222222" );
		set_style( styles, "padding", 5 );
		set_style( styles, "margin-x", 10 );
		set_style( styles, "margin-y", 20 );
		set_style( styles, "node", {} );
		set_style( styles, "order", {} );
		set_style( styles, "state", {} );
		set_style( styles, "answer", {} );
		set_style( styles, "error", {} );
		set_style( styles["order"], "radius", 15 );
		set_style( styles["order"], "background-color", "#7e7fff" );
		set_style( styles["order"], "border-width", 4 );
		set_style( styles["order"], "border-color", "#222222" );
		set_style( styles["order"], "font-color", "#222222" );
		set_style( styles["state"], "background-color", "#ffff00" );
		set_style( styles["state"], "border-width", 4 );
		set_style( styles["state"], "border-color", "#222222" );
		set_style( styles["state"], "font-color", "#222222" );
		set_style( styles["answer"], "background-color", "#ffff00" );
		set_style( styles["answer"], "border-width", 4 );
		set_style( styles["answer"], "border-color", "#222222" );
		set_style( styles["answer"], "font-color", "#222222" );
		set_style( styles["error"], "background-color", "#ffff00" );
		set_style( styles["error"], "border-width", 4 );
		set_style( styles["error"], "border-color", "#222222" );
		set_style( styles["error"], "font-color", "#222222" );
		var tree = get_tree( string );
		draw( tree, canvas, styles );
	};

	var draw = function( tree, canvas_id, styles ) {
		// Graph configuration
		var padding = styles["padding"];
		var margin_x = styles["margin-x"];
		var margin_y = styles["margin-y"];
		var font_size = styles["font-size"];
		var radius = styles["order"]["radius"];
		// Get container, canvas and context
		var src = document.getElementById(src);
		var canvas = typeof canvas_id === "string" ? document.getElementById(canvas_id) : canvas_id;
		var ctx = canvas.getContext("2d");
		// Maximum width of each level
		var maxwidth = tree.map(function(a){return a.reduce(function(b,c){return b + c.width(ctx, styles["font"], margin_x, padding)}, 0)}, 0);
		// Width of the image
		var width = maxwidth.reduce(function(a,b){return Math.max(a,b)}, 0);
		// Get height of state blocks, levels and image
		var unifier_height = (padding * 3) + ((font_size + 2) * 2);
		var level_height = (radius * 2) + (margin_y * 2) + unifier_height;
		var height = level_height * tree.length - (2 * radius);
		// Set canvas properties
		ctx.height = height;
		ctx.width = width;
		canvas.height = ctx.height;
		canvas.width = ctx.width;
		
		// CLEAR CANVAS
		ctx.clearRect(0, 0, width, height);
		
		// DRAW LINES
		
		// Relative centers to other levels
		var relative = [];
		// Height
		var offset_y = margin_y;
		var offset_z = margin_y;
		// Iterate levels
		for (var i = 0; i < tree.length; i++) {
			// Push centers for following levels
			relative.push([]);
			// Get offset
			var offset_x = (width - maxwidth[i]) / 2;
			// Iterate states
			for (var j = 0; j < tree[i].length; j++) {
				// Get initial offset
				offset_z = offset_y;
				// Set relative center
				var center = offset_x + (tree[i][j].width(ctx, styles["font"], margin_x, padding) / 2);
				relative[i].push(center);
				if (i > 0) {
					// Draw lines
					ctx.lineWidth = styles["border-width"];
					ctx.strokeStyle = styles["border-color"];
					ctx.beginPath();
					ctx.moveTo(relative[i-1][tree[i][j].parent], offset_y - unifier_height / 2);
					ctx.lineTo(center, offset_y + 2 * (margin_y + radius));
					ctx.closePath();
					ctx.stroke();
					// Draw rule
					offset_z += 2 * (margin_y + radius)
				}
				offset_z += unifier_height;
				// Update offset
				offset_x += tree[i][j].width(ctx, styles["font"], margin_x, padding);
			}
			// Update offset
			offset_y = offset_z;
		}
		
		// DRAW BLOCKS
		
		// Relative centers to other levels
		relative = [];
		// Height
		offset_y = margin_y;
		offset_z = margin_y;
		// Iterate levels
		for (i = 0; i < tree.length; i++) {
			// Push centers for following levels
			relative.push([]);
			// Get offset
			offset_x = (width - maxwidth[i]) / 2;
			// Iterate states
			for (j = 0; j < tree[i].length; j++) {
				// Get initial offset
				offset_z = offset_y;
				// Set relative center
				center = offset_x + (tree[i][j].width(ctx, styles["font"], margin_x, padding) / 2);
				relative[i].push(center);
				if (i > 0) {
					var x1 = Math.abs(relative[i-1][tree[i][j].parent] - center);
					var y1 = 2 * (radius + margin_y) + unifier_height / 2;
					var y3 = margin_y + radius;
					var alpha = Math.atan(y1 / x1);
					var y4 = y3 + radius * Math.sin(alpha);
					var x3 = y3 / (Math.tan(alpha));
					var x4 = x3 - radius * Math.cos(alpha);
					if (relative[i-1][tree[i][j].parent] < center) {
						x3 = -x3;
						x4 = -x4;
					}
					// Draw rule
					offset_z += margin_y + radius;
							ctx.fillStyle = styles["order"]["background-color"];
							ctx.strokeStyle = styles["order"]["border-color"];
							ctx.lineWidth = styles["order"]["border-width"];
							/*ctx.beginPath();
							ctx.arc(center + x3, offset_z, radius, 0, 2 * Math.PI);
							ctx.closePath();
							ctx.stroke();
							ctx.fill();*/
							ctx.font = styles["font"];
							var w = ctx.measureText( tree[i][j].rule ).width;
							ctx.beginPath();
							ctx.rect(center + x3 - w/2 - padding, offset_z - font_size/2 - padding, w + 2 * padding, font_size + 2 * padding);
							ctx.closePath();
							ctx.stroke();
							ctx.fill();
							/*ctx.beginPath();
							ctx.arc(center + x3, offset_z, radius, 0, 2 * Math.PI);
							ctx.closePath();
							ctx.fill();*/
						ctx.fillStyle = styles["order"]["font-color"];
						ctx.font = "bold " + styles["font"];
						ctx.textAlign = "center"; 
						ctx.fillText(tree[i][j].rule, center + x3, offset_z + font_size / 2 - 1);
					offset_z += radius + margin_y;
				}
				// Draw state
				var type_state = "state";
				ctx.fillStyle = styles[type_state]["background-color"];
				ctx.strokeStyle = styles[type_state]["border-color"];
				ctx.lineWidth = styles[type_state]["border-width"];
				ctx.beginPath();
				ctx.rect(center - tree[i][j].width(ctx, styles["font"], 0, padding) / 2, offset_z, tree[i][j].width(ctx, styles["font"], 0, padding), unifier_height);
				ctx.closePath();
				ctx.stroke();
				ctx.fill();
				ctx.fillStyle = styles[type_state]["font-color"];
				ctx.font = styles["font"];
				ctx.textAlign = "center"; 
				ctx.fillText(tree[i][j].goal, center, offset_z + padding + font_size);
				ctx.fillText(tree[i][j].subs, center, offset_z + (2 * font_size) + (2 * padding));
				offset_z += unifier_height;
				// Update offset
				offset_x += tree[i][j].width(ctx, styles["font"], margin_x, padding);
			}
			// Update offset
			offset_y = offset_z;
		}
		// Add click event
		var click_draw = function(){ window.open(canvas.toDataURL(), '_blank'); };
		if (canvas.addEventListener) {
			if(canvas.click_draw)
				canvas.removeEventListener("click", canvas.click_draw);
			canvas.addEventListener("click", click_draw, false);
			canvas.style.cursor = "pointer";
		} else {
			if (canvas.attachEvent) {
				if(canvas.click_draw)
					canvas.detachEvent("click", canvas.click_draw);
				canvas.attachEvent("click", click_draw);
				canvas.style.cursor = "pointer";
			}
		}
		canvas.click_draw = click_draw;
	};
	
	window.draw_tree = draw_tree;

})();
