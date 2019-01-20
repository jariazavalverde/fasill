from os import listdir

def gen(path, name, fun):
	with open(path, "r") as f:
		array = []
		predicate = None
		template = None
		description = ""
		for line in f:
			if line[:2] == '% ' or line[:2] == '%\n':
				if predicate is None:
					predicate = line[2:]
				elif template is None:
					template = line[2:]
				else:
					description += line[1:]
			else:
				if predicate is not None and template is not None and description != "":
					predicate = predicate.replace("\n","")
					template = template.replace("\n","")
					description = description.replace("\n","").strip("  ")
					array.append((predicate, template, description))
				predicate = None
				template = None
				description = ""
	doc = "\n".join(map(lambda x: fun(name, x), array))
	out = open("../www/pages/src-doc/" + name + ".php", "w")
	out.write(doc)
	out.close()

def html(module, x):
	(predicate, template, description) = x
	html = "<div class=\"container py-2 px-0\">"
	html += "<h4 id=\"" + predicate + "\"><a href=\"/fasill/documentation/src/" + module + "#" + predicate + "\">" + predicate + "</a></h4>"
	html += "<?php echo show_template(\"" + template + "\"); ?>"
	html += "<p><?php echo show_description(\"" + description + "\"); ?></p>"
	html += "</div>"
	return html

for f in listdir("../src/"):
	f = f.replace(".pl", "")
	gen("../src/" + f + ".pl", f, html)
