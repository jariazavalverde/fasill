from sys import argv
import os

class Predicate:
	""" """
	def __init__(self, templates, description):
		""" """
		self.templates = templates
		self.description = description
		if "(" in self.templates[0]:
			split = self.templates[0].split("(")
			self.indicator = split[0] + "/" + str(len(split[1].split(",")))
		else:
			self.indicator = self.templates[0] + "/0"
	
	def html(self, slug):
		""" """
		html = "<div class=\"py-2 px-0\">"
		html += "<h4 id=\"" + self.indicator + "\"><a href=\"/fasill/documentation/src/" + slug + "#" + self.indicator + "\">" + self.indicator + "</a></h4>"
		for template in self.templates:
			html += "<?php echo show_template(\"" + template + "\"); ?>"
		html += "<p><?php echo show_description(\"" + self.description + "\"); ?></p>"
		html += "</div>"
		return html

class Module:
	""" """
	def __init__(self, name, description):
		""" """
		self.name = name
		self.description = description
		self.slug = name.replace(" ", "-").replace("/", "").lower()
		self.predicates = []
		
	def add_predicate(self, predicate):
		""" """
		self.predicates.append(predicate)
	
	def html(self):
		""" """
		html = "<div class=\"container py-2 px-0\">"
		html += "<h1 id=\"" + self.slug + "\">" + self.name + "</a></h1>"
		html += "<p>" + self.description + "</p>"
		for predicate in self.predicates:
			html += predicate.html(self.slug)
		html += "</div>"
		return html

def module(path):
	""" """
	mod = None
	with open(path, "r") as f:
		lines = f.readlines()
		nb_lines = len(lines)
		i = 0
		# Start of a module
		while lines[i][:12] != "/** <module>":
			i += 1
		name = lines[i][13:].replace("\n", "")
		description = ""
		i += 1
		while lines[i][:2] != "*/":
			description += lines[i][2:]
			i += 1
		mod = Module(name, description)
		while i < nb_lines:
		# Start of a predicate
			while lines[i][:3] != "%! ":
				i += 1
				if i >= nb_lines:
					return mod
			templates = []
			while lines[i][:3] == "%! ":
				template = lines[i][3:].replace(" ", "").replace("\n", "")
				templates.append(template)
				i += 1
			i += 1
			description = ""
			while lines[i][:2] == "% ":
				description += lines[i][2:]
				i += 1
			predicate = Predicate(templates, description)
			mod.add_predicate(predicate)
	return mod

if __name__ == "__main__":
	input = argv[1]
	output = argv[2]
	mod = module(input)
	f = open(os.path.basename(input).replace(".pl", "") + ".php", "w")
	f.write(mod.html())
	f.close()