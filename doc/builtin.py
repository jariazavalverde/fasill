from os import listdir

def gen(path, fun):
	with open(path, "r") as f:
		array = {}
		cat = None
		predicate = None
		templates = []
		short = None
		description = ""
		empty = False
		for line in f:
			if line[:3] == "%% ":
				cat = line[3:].replace("\n","").replace(" ","-").lower()
				array[cat] = []
			elif line[:4] == '%%% ' or line[:4] == '%%%\n':
				if predicate is None:
					predicate = line[4:]
				elif not empty and len(line) > 4:
					templates.append(line[4:])
				else:
					if short is None and empty:
						short = line[4:]
					else:
						description += line[3:]
					empty = True
			else:
				if cat is not None and predicate is not None:
					predicate = predicate.replace("\n","")
					short = short.replace("\n","")
					templates = map(lambda x: x.replace("\n",""), templates)
					description = description.replace("\n","").strip("  ")
					array[cat].append((predicate, templates, short, description))
				predicate = None
				short = None
				templates = []
				description = ""
				empty = False
	cats = sorted(array.keys())
	for name in cats:
		doc = "\n".join(map(lambda x: fun(name, x), array[name]))
		out = open("../www/pages/ref-doc/" + name + ".php", "w")
		out.write(doc)
		out.close()

def html(cat, x):
	(predicate, templates, short, description) = x
	html = "<div class=\"container py-2 px-0\">"
	html += "<h4 id=\"" + predicate + "\"><a href=\"/fasill/documentation/ref/" + cat + "#" + predicate + "\">" + predicate + "</a></h4>"
	html += "<p class=\"text-secondary\">" + short + "</p>"
	for template in templates:
		html += "<?php echo show_template(\"" + template + "\"); ?>"
	html += "<p><?php echo show_description(\"" + description + "\"); ?></p>"
	html += "</div>"
	return html

gen("../src/builtin.pl", html)
