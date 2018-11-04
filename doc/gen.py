from os import listdir

def gen(path, name, fun):
	with open(path, "r") as f:
		array = []
		predicate = None
		template = None
		description = ""
		for line in f:
			if line[0] == '%':
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
	doc = "\n".join(map(fun, array))
	out = open(name, "w")
	out.write(doc)
	out.close()

def html(x):
	(predicate, template, description) = x
	html = "<div class=\"container\">"
	html += "<h4>" + predicate + "</h4>"
	html += "<pre><code>" + template + "</code></pre>"
	html += "<p>" + description + "</p>"
	html += "</div>"
	return html

for f in listdir("../src/"):
	f = f.replace(".pl", "")
	gen("../src/" + f + ".pl", f + ".html", html)
