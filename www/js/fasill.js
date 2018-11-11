var program;
var lattice;
var sim;
var goal;
var limit;
var output;
var derivation;

window.addEventListener("load", function() {
	var program_value = document.getElementById("program").innerHTML.replace(/&lt;/g,"<").replace(/&gt;/g,">");
	document.getElementById("program").innerHTML = "";
	program = CodeMirror(document.getElementById("program"), {
		value: program_value,
		lineNumbers: true,
		theme: "fasill",
		placeholder: "Your program here...",
		mode: "prolog"
	});
	var lattice_value = document.getElementById("lattice").innerHTML.replace(/&lt;/g,"<").replace(/&gt;/g,">");
	document.getElementById("lattice").innerHTML = "";
	lattice = CodeMirror(document.getElementById("lattice"), {
		value: lattice_value,
		lineNumbers: true,
		theme: "fasill",
		placeholder: "Your lattice here...",
		mode: "prolog"
	});
	var sim_value = document.getElementById("sim").innerHTML.replace(/&lt;/g,"<").replace(/&gt;/g,">");
	document.getElementById("sim").innerHTML = "";
	sim = CodeMirror(document.getElementById("sim"), {
		value: sim_value,
		lineNumbers: true,
		theme: "fasill",
		placeholder: "Your similarity equations here...",
		mode: "prolog"
	});
	var goal_value = document.getElementById("goal").innerHTML.replace(/&lt;/g,"<").replace(/&gt;/g,">");
	document.getElementById("goal").innerHTML = "";
	goal = CodeMirror(document.getElementById("goal"), {
		value: goal_value,
		lineNumbers: false,
		theme: "fasill",
		placeholder: "Type a FASILL goal in here",
		mode: "prolog"
	});
	var limit_value = document.getElementById("limit").innerHTML.replace(/&lt;/g,"<").replace(/&gt;/g,">");
	document.getElementById("limit").innerHTML = "";
	limit = CodeMirror(document.getElementById("limit"), {
		value: limit_value,
		lineNumbers: false,
		theme: "fasill",
		placeholder: "Max. number of inferences",
		mode: "prolog"
	});
	output = CodeMirror(document.getElementById("out"), {
		lineNumbers: true,
		theme: "fasill",
		mode: "prolog",
		readOnly: true
	});
	derivation = CodeMirror(document.getElementById("derivation"), {
		lineNumbers: true,
		theme: "fasill",
		mode: "prolog",
		readOnly: true
	});
	program.setSize("100%", "100%");
	lattice.setSize("100%", "100%");
	sim.setSize("100%", "100%");
	goal.setSize("100%", "100%");
	limit.setSize("100%", "100%");
	output.setSize("100%", "100%");
	derivation.setSize("100%", "100%");
});

function load_lattice( from ) {
	post( from, "", function(data) {
		lattice.setValue(data);
	});
}

function post( url, data, callback ) {
	var xhttp = new XMLHttpRequest();
	xhttp.onreadystatechange = function() {
		if (this.readyState == 4 && this.status == 200) {
			callback(this.responseText);
		}
	};
	xhttp.open("POST", url, true);
	xhttp.setRequestHeader("Content-type", "application/x-www-form-urlencoded");
	xhttp.send(data);
}

function fasill_run() {
	var data = jQuery.param({
		"program": program.getValue(),
		"lattice": lattice.getValue(),
		"sim": sim.getValue(),
		"goal": goal.getValue(),
		"limit": limit.getValue()
	});
	output.setValue("Running...");
	derivation.setValue("Running...");
	post("php/run.php", data, function(data) {
		data = data.trim();
		if(data === "")
			data = "uncaught exception: unknown";
		data = data.trim().split("\n\n");
		if(data.length == 1)
			data[1] = "";
		output.setValue(data[0]);
		derivation.setValue(data[1]);
		draw_tree( data[1], "tree" );
	});
}

function fasill_listing() {
	var lst = document.getElementById("listing");
	var data = jQuery.param({
		"program": program.getValue()
	});
	post("php/listing.php", data, function(data) {
		data = data.trim();
		if(data === "")
			data = "uncaught exception: unknown";
		data = data.split("\n");
		var html = "";
		for(var i = 0; i < data.length; i++) {
			data[i] = data[i].trim().split(/ (.+)/);
			html += "<div onClick=\"fasill_unfold('" + data[i][0] + "');\" class=\"lst-rule mt-2\"> <span class=\"lst-rule-id\">" + data[i][0] + "</span> " + data[i][1] + "</div>";
		}
		lst.innerHTML = html;
	});
}

function fasill_unfold(rule) {
	var data = jQuery.param({
		"program": program.getValue(),
		"lattice": lattice.getValue(),
		"sim": sim.getValue(),
		"rule": rule
	});
	post("php/unfold.php", data, function(data) {
		data = data.trim();
		if(data !== "")
			program.setValue(data);
	});
}
