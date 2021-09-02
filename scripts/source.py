import sys
import markdown
import os

class Predicate:

	def __init__(self, templates, description):
		self.templates = templates
		self.description = description
		if "(" in self.templates[0]:
			split = self.templates[0].split("(")
			self.indicator = split[0] + "/" + str(len(split[1].split(",")))
		else:
			self.indicator = self.templates[0] + "/0"
	
	def html(self, slug):
		html = "<div class=\"fasill-module-predicate\">"
		html += "<h4 id=\"%s\"><a href=\"/fasill/documentation/src/%s#%s\">%s</a></h4>" % (self.indicator, slug, self.indicator, self.indicator)
		for template in self.templates:
			html += "<?php echo show_template(\"%s\"); ?>" % template
		html += "<p class=\"fasill-module-predicate-description\">%s</p>" % markdown.markdown(self.description)
		html += "</div>"
		return html

class Module:

	def __init__(self, name, description):
		self.name = name
		self.description = description
		self.slug = name.replace(" ", "-").replace("/", "").lower()
		self.predicates = []
		
	def add_predicate(self, predicate):
		self.predicates.append(predicate)
	
	def html(self):
		md = markdown.Markdown(extensions=['mdx_math'], extension_configs={'mdx_math': {'enable_dollar_delimiter': True}})
		html = "<div class=\"fasill-module\">"
		html += "<h1 id=\"%s\">%s</h1>" % (self.slug, self.name)
		html += "<div class=\"fasill-module-description\">%s</div>" % md.convert(self.description)
		for predicate in self.predicates:
			html += predicate.html(self.slug)
		html += "</div>"
		return html

def module(path):
	mod = None
	with open(path, "r", encoding="utf8") as f:
		lines = f.readlines()
		nb_lines = len(lines)
		i = 0
		# Start of a module
		while lines[i][:12] != "/** <module>":
			i += 1
		name = lines[i][13:].replace("\n", "")
		description = ""
		i += 1
		while lines[i].strip() != "*/":
			if lines[i] == "" or lines[i].isspace():
				description += "\n\r"
			else:
				description += lines[i].strip() + " "
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
	input = sys.argv[1]
	output = sys.argv[2]
	mod = module(input)
	f = open(os.path.join(output, os.path.basename(input).replace(".pl", "") + ".php"), "w", encoding="utf8")
	f.write(mod.html())
	f.close()