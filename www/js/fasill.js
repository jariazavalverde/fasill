var program;
var lattice;
var sim;
var goal;
var limit;
var output;

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
	program.setSize("100%", "100%");
	lattice.setSize("100%", "100%");
	sim.setSize("100%", "100%");
	goal.setSize("100%", "100%");
	limit.setSize("100%", "100%");
	output.setSize("100%", "100%");
});


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
	post("php/run.php", data, function(data) {
		output.setValue(data.trim());
	});
}
