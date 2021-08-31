from sys import argv
import os

class Predicate:
	""" """
	def __init__(self, templates, short, description):
		""" """
		self.templates = templates
		self.short = short
		self.description = description
		if "(" in self.templates[0]:
			split = self.templates[0].split("(")
			self.indicator = split[0] + "/" + str(len(split[1].split(",")))
		else:
			self.indicator = self.templates[0] + "/0"
	
	def html(self, slug):
		""" """
		html = "<div class=\"py-2 px-0\">"
		html += "<h4 id=\"" + self.indicator + "\"><a href=\"/fasill/documentation/ref/" + slug + "#" + self.indicator + "\">" + self.indicator + "</a></h4>"
		html += "<p class=\"text-secondary\">" + self.short + "</p>"
		for template in self.templates:
			html += "<?php echo show_template(\"" + template + "\"); ?>"
		html += "<p><?php echo show_description(\"" + self.description + "\"); ?></p>"
		html += "</div>"
		return html

class Category:
	""" """
	def __init__(self, name, description):
		""" """
		self.name = name
		self.description = description
		self.slug = name.replace(" ", "-").lower()
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

def builtin(path):
	""" """
	categories = dict()
	with open(path, "r") as f:
		lines = f.readlines()
		nb_lines = len(lines)
		for i in range(len(lines)):
			line = lines[i]
			# Start of a built-in category
			if line[:13] == "/** <builtin>":
				name = line[14:].replace("\n", "").replace("\r", "")
				description = ""
				i += 1
				while lines[i][:2] != "*/":
					description += lines[i][2:]
					i += 1
				categories[name] = Category(name, description)
				while lines[i][:13] != "/** <builtin>":
					while lines[i][:3] != "%! " and lines[i][:13] != "/** <builtin>":
						i += 1
						if i >= nb_lines:
							return categories
					if lines[i][:13] == "/** <builtin>":
						break
					# Start of a predicate
					templates = []
					while lines[i][:3] == "%! ":
						template = lines[i][3:].replace(" ", "").replace("\n", "")
						templates.append(template)
						i += 1
					i += 1
					short = lines[i][2:].replace("\n", "")
					i += 1
					description = ""
					while lines[i][:2] == "% ":
						description += lines[i][2:]
						i += 1
					predicate = Predicate(templates, short, description)
					categories[name].add_predicate(predicate)
				i -= 1
	return categories

if __name__ == "__main__":
	input = argv[1]
	output = argv[2]
	categories = builtin(input)
	for key in categories:
		category = categories[key]
		f = open(os.path.join(output, category.slug + ".php"), "w")
		f.write(category.html())
		f.close()