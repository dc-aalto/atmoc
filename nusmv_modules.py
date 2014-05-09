# -*- coding: iso-8859-15 -*-

# (c) 2011-2012 Roland Kindermann
#
# This file is part of the Aalto Timed Model Checker ATMOC.
# 
# ATMOC is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
# 
# ATMOC is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
# 
# You should have received a copy of the GNU General Public License
# along with ATMOC.  If not, see <http://www.gnu.org/licenses/>.





import copy

from expressions import *

def indent(strn, cnt=2):
	ind = " " * cnt
	strn = strn.split("\n")
	for i in xrange(len(strn)):
		if strn[i]:
			strn[i] = "  %s" % strn[i]
	return "\n".join(strn)

class StructureException(Exception):
	pass

class Program(object):
	def __init__(self, modules):
		assert isinstance(modules, list)
		assert all(isinstance(x, Module) for x in modules)
		self.modules = {}
		for mod in modules:
			if mod.name in self.modules:
				raise StructureException("More than one module with name %s" % modname)
			self.modules[mod.name] = mod
	
	def flatten(self, ignore=[]):
		"Flattens the model; ignores specified modules"
		#Figure out order in which to flatten
		dependencies = {}
		for mod in self.modules.itervalues():
			dependencies[mod.name] = mod.dependencies() - set(ignore)
		remaining = set(["main"])
		relevant = set()
		while remaining:
			next = remaining.pop()
			relevant.add(next)
			remaining.update(dependencies[next] - relevant)
		order = []
		done = set()
		while relevant:
			satisfied = [m for m in dependencies if m in relevant and dependencies[m].issubset(done)]
			if not satisfied:
				raise StructureException("Cycular dependency among the following modules: " + ", ".join(m for m in relevant) + " (not necessarily all modules are involved)")
			order += satisfied
			relevant.difference_update(satisfied)
			done.update(satisfied)
			
		#Flatten modules
		for modname in order:
			self.modules[modname].flatten(self.modules, ignore)
		
		mods = {"main" : self.modules["main"]}
		for ign in ignore:
			if ign in self.modules:
				mods[ign] = self.modules[ign]
		self.modules = mods
	
	def string(self, names):
		return "%s\n\n" % "\n\n".join(map(lambda x : x.string(names), self.modules.itervalues()))
	
	def __str__(self):
		return self.string(False)
	
	def enums_to_ranges(self):
		for mod in self.modules.itervalues():
			mod.enums_to_ranges()
	
	def inline_definitions(self, use_vars=False):
		for mod in self.modules.itervalues():
			mod.inline_definitions(use_vars)
	
	def remove_assigns(self):
		for mod in self.modules.itervalues():
			mod.remove_assigns()

def tmp(a):
	def r(x,y,z):
		ret = a(x, y, z)
		print ret
		return ret
	return r

def _prefix_callback(expr, _, (prefix, defnames)):
	if isinstance(expr, Variable):
		return Variable("%s.%s" % (prefix, expr.name), expr.type)
	elif expr in defnames:#isinstance(expr, AstExpression) and len(expr) == 1 and expr[0] in defnames:
		return AstExpression("%s.%s" % (prefix, expr[0]))
	else:
		return None

def _def_callback(expr, _, (definitions, out)):
	"If out == None, definitions will be replaced, otherwise uses will be stored in out"
	if expr in definitions:
		if out == None:
			return definitions[expr]
		else:
			out.append(expr)
			return expr
	else:
		return None

def find_viable_inlining_order(definitions):
	"definitions: name -> expression"
	assert isinstance(definitions, dict)
	assert all(isinstance(x, AstExpression) for x in definitions)
	assert all(len(x) == 1 for x in definitions), '\n\n'.join(str(x) for x in definitions)
	assert all(isinstance(x[0], basestring) for x in definitions)
	assert all(isinstance(x, Expression) for x in definitions.itervalues())
	
	#Find dependencies
	dependencies = {}
	for (defi, expr) in definitions.iteritems():
		dependencies[defi] = []
		expr.traverse_and_replace(_def_callback, (definitions, dependencies[defi]))
	
	#Determine viable order for inlining
	left = set(definitions)
	order = []
	while left:
		olen = len(order)
		for defi in left:
			if not (set(dependencies[defi]) - set(order)):
				order.append(defi)
		left -= set(order)
		
		if len(order) == olen and left:
			raise Exception("Circular dependency among definition(s): %s" % '\n\n'.join(map(str, left)))
	return order

class Module(object):
	def __init__(self, name, params, body):
		assert isinstance(name, basestring)
		assert isinstance(params, list)
		assert all(isinstance(x, basestring) for x in params)
		assert isinstance(body, list)
		assert all(isinstance(x, ModuleElement) for x in body)
		
		self.name = name
		self.params = params
		self.body = body
#		self._varify()
		self.inlined = False
		self.flattened = False
	
	def remove_assigns(self):
		newbody = []
		for el in self.body:
			if el.type != "ASSIGN":
				newbody.append(el)
			else:
				for asgn in el.content:
					assert asgn.modifier in ["init", "next"]
					
					if asgn.modifier == "init":
						typ = "INIT"
						lhs = asgn.name
					else:
						typ = "TRANS"
						lhs = AstExpression("next", asgn.name)
					newbody.append(Constraint(typ, AstExpression("=", lhs, asgn.value)))
		self.body = newbody
	
	def enums_to_ranges(self):
		"Replaces enumeration types with range types " \
		"Should be called after inlining but before flattening"
		if not self.flattened:
			raise Exception("Should be done after flattening")
		
		valmapping = {}
		by_type = {}
		for be in self.body:
			if be.type == "VAR" or be.type == "IVAR":
				for i in xrange(len(be.content)):
					(name, typ) = be.content[i]
					if isinstance(typ, Enumeration):
						if any(x.isdigit() for x in typ.values):
							raise Exception("Enumeration with integers: %s" % str(typ))
						nt = EnumRange(typ.values)
						be.content[i] = (name, nt)
						for j in xrange(nt.low, nt.high + 1):
							val = nt[j]
							if val in valmapping and by_type[val] != nt:
								raise Exception("Name collision: %s" % val)
							valmapping[val] = str(j)
							by_type[val] = nt
		
		def _val_rep_cb(expr, _, arg):
			if isinstance(expr, AstExpression) and len(expr) == 1 and expr[0] in arg:
				return AstExpression(arg[expr[0]])
		
		self.traverse_and_replace_all(_val_rep_cb, valmapping)
		self._varify()
	
	def _varify(self):
		"Assigns the correct types to all variables"
		# Collect information
		repl = {}
		for varsec in self.get_all("VAR"):
			assert isinstance(varsec, Variables)
			for (name, typ) in varsec.content:
				repl[name] = Variable(name, typ)
		
		# Replace variable references in expressions
		def _varify_cb(expr, _, repl):
			if isinstance(expr, AstExpression) and len(expr) == 1:
				return repl.get(expr[0], None)
			elif isinstance(expr, Variable):
				return repl.get(expr.name, None)
		
		self.traverse_and_replace_all(_varify_cb, repl)
	
	def get_all(self, *typ):
		"Returns all elements of specified type"
		return [elem for elem in self.body if elem.type in typ]
	
	def get_all_iter(self, *typ):
		'Same as get_all but returns iterator'
		for elem in self.body:
			if elem.type in typ:
				yield elem
	
	def get_first(self, typ):
		"Returns the first element of the specified type or None if no such module exists"
		for elem in self.body:
			if elem.type == typ:
				return elem
		return None
	
	def dependencies(self):
		"Returns a list of modules used as types"
		ret = set()
		for varsec in self.get_all("VAR", "IVAR"):
			for (_, typ) in varsec.content:
				if isinstance(typ, ModuleType):
					ret.add(typ.module)
		return ret
	
	def flatten(self, other_modules, ignore):
		if self.flattened:
			raise Exception("Flattening for the second time")
		
		for el in self.body:
			if isinstance(el, IsaDeclaration):
				raise StructureException("Flattening modules that contain ISA declarations is not supported.")
		
		### Figure out what to inline under which prefix and remove corresponding variable declarations
		inline = []
		for bi in xrange(len(self.body)):
			el = self.body[bi]
			if isinstance(el, Variables):
				for (i, (name, typ)) in enumerate(el.content):
					if isinstance(typ, ModuleType) and not typ.module in ignore:
						inline.append((name, typ))
						el.content[i] = None
				el.content = [x for x in el.content if not x == None]
				if not el.content:
					self.body[bi] = None
		self.body = [el for el in self.body if el != None]
		
		### Do the actual inlining
		for (name, typ) in inline:
			module = other_modules[typ.module]
			
			# Build list for argument replacements
			arguments = []
			argvals = []
			for i in xrange(len(typ.params)):
				arguments.append(AstExpression(module.params[i]))
				argvals.append(typ.params[i])
			
			# Find out variable names
			defnames = []
			for el in module.get_all("DEFINE"):
				for asgn in el.content:
					defnames.append(asgn.name)
				
			
			# Prefix everything required
			for el in module.body:
				#Prefix variables
				el = copy.deepcopy(el)
				el.prefix(name, defnames)
				
				# Inline arguments:
				el.traverse_and_replace_all(replace_callback, (arguments, argvals))
				
				self.body.append(el)
		
		self._varify() # The this is necessary for mod.var references that used to refer to variables in other modules but are local now
		
		self.flattened = True
	
	def get_type_info(self):
		# Enums
		enum_types = []
		for sec in self.body:
			if isinstance(sec, Variables):
				for (var, typ) in sec.content:
					if isinstance(typ, Enumeration):
						enum_types.append(typ)
		type_info = {}
		for et in enum_types:
			for val in et.values:
				type_info[val] = et
				
		# Definitions		
		defs = self.get_definitions()
		order = find_viable_inlining_order(defs)
		for dn in order:
			type_info[dn[0]] = defs[dn].get_type(False, type_info)
		
		return type_info
	
	def type_check(self):
		def _tc_cb(expr, _, et):
			expr.get_type(True, et)
			return expr
		self.traverse_and_replace_all(_tc_cb, self.get_type_info())
	
	def get_definitions(self, remove=False):
		definitions = {}
		for (si, sec) in enumerate(self.body):
			if sec.type == "DEFINE":
				for asgn in sec.content:
					assert asgn.modifier == None
					definitions[asgn.name] = asgn.value
				if remove:
					self.body[si] = None
		if remove:
			self.body = [sec for sec in self.body if sec != None]
		return definitions
	
	def inline_definitions(self, use_vars=False):
		"Inlines and removes all definitions; If use_vars is true, variables are "\
		"used instead of copying expressions."
		
		if self.inlined:
			raise Exception("Inlining twice")
		
		#Gather definitions
		tinfo = self.get_type_info()
		print tinfo
		definitions = self.get_definitions(True)
		
		self.def_var_names = []
		if use_vars: #
			assert self.flattened
			# Note that, technically, we should not count uses of definitions in
			# unused definitions; practically it should not be worth the effort
			# to actually check, which definitions are unused beforehand
			def _cnt_uses_cb(expr, _, (definitions, out)):
				if expr in definitions:
					out[expr] = out.get(expr, 0) + 1
					return expr
			usecnt = {}
			self.traverse_and_replace_all(_cnt_uses_cb, (definitions, usecnt))
			for v in definitions.itervalues():
				v.traverse_and_replace(_cnt_uses_cb, (definitions, usecnt))
			
			variables = []
			invars = []
			repl = {}
			for expr, cnt in usecnt.iteritems():
				if cnt > 1:
					val = definitions[expr]
					assert isinstance(expr, AstExpression)
					assert len(expr) == 1
					name = expr[0]
					assert isinstance(name, basestring), repr(repl)
					typ = val.get_type(False, tinfo)
					variables.append((name, typ))
					var = Variable(name, typ)
					self.def_var_names.append(name)
					invars.append(Constraint("INVAR", AstExpression("<->", var, val)))
					repl[expr] = var
					del definitions[expr]
			
			def _replace_cb(expr, _, replace):
				return replace.get(expr, None)
			
			self.body.append(Variables("VAR", variables))
			for inv in invars:
				self.body.append(inv)
			
			self.traverse_and_replace_all(_replace_cb, repl)
			for lhs in definitions:
				definitions[lhs] = definitions[lhs].traverse_and_replace(_replace_cb, repl)
		# endof use_vars
		
		order = find_viable_inlining_order(definitions)
		
		#Inline definitions in definitions
		for defi in order:
			definitions[defi] = definitions[defi].traverse_and_replace(_def_callback, (definitions, None))
		
		#Inline in the actual module
		for sec in self.body:
			sec.traverse_and_replace_all(_def_callback, (definitions, None))
		
		self.inlined = True
	
	def traverse_and_replace_all(self, function, arg):
		raise Exception("Don't use, max recursion depth!")
		for el in self.body:
			if el != None:
				el.traverse_and_replace_all(function, arg)
	
	def string(self, names):
		if self.params:
			pstr = "(%s)" % ", ".join(self.params)
		else:
			pstr = ""
		bodystr = indent("\n".join(map(lambda x : x.string(names), self.body)))
		return "MODULE %s%s\n%s" % (self.name, pstr, bodystr)
	
	def __str__(self):
		return self.string(False)

################################################################################
############################### Module Elements ################################
################################################################################


class ModuleElement(object):
	def __init__(self):
		raise Exception("This is an abstract class!")
	
	def _init(self, typ):
		assert isinstance(typ, basestring)
		self.type = typ
	
	def traverse_and_replace_all(self, function, argument):
		"Calls traverse_and_replace(function, argument) on any expression used\n" +\
		"anywhere any carries out replacements if necessary."
		raise Exception("Abstract method (not implemented in " + type(self).__name__ + ")")
	
	def prefix(self, prefix, defnames):
		"Prefixes any reference to a variable or any definition specified in defnames with the specified prefix."
		self.traverse_and_replace_all(_prefix_callback, (prefix, defnames))
	
	def string(self, names):
		raise Exception("Unimplemented abstract method!")
	
	def copy(self):
		r = self._copy()
		assert type(r) == type(self)
		return r
	
	def _copy(self):
		raise Exception("Unimplemented abstract method!")
	
	def __str__(self):	
		return self.string(False)
	
	def __eq__(self, other):
		if other == None:
			return False
		else:
			raise Exception("not implemented")
	
	def __ne__(self, other):
		return not self.__eq__(other)

########################### Single Expression style ############################
class Constraint(ModuleElement):
	def __init__(self, typ, expression):
		assert typ in ["INIT", "INVAR", "TRANS", "JUSTICE", "URGENT"]
		assert isinstance(expression, Expression)
		self._init(typ)
		self.expression = expression
	
	def traverse_and_replace_all(self, function, argument):
		self.expression = self.expression.traverse_and_replace(function, argument)
	
	def string(self, names):
		return "%s %s" % (self.type, self.expression.string(names))
	
	def _copy(self):
		return Constraint(self.type, self.expression)

class CompassionConstraint(ModuleElement):
	def __init__(self, exp1, exp2):
		self._init("COMPASSION")
		assert isinstance(exp1, Expression)
		assert isinstance(exp2, Expression)
		self.exp1 = exp1
		self.exp2 = exp2
	
	def traverse_and_replace_all(self, function, argument):
		self.exp1 = self.exp1.traverse_and_replace(function, argument)
		self.exp2 = self.exp2.traverse_and_replace(function, argument)
	
	def _copy(self):
		return CompassionConstraint(self.exp1, self.exp2)
	
	def string(self, names):
		return "%s(%s, %s)" % (self.type, self.exp1.string(names), self.exp2.string(names))

class Specification(ModuleElement):
	def __init__(self, typ, name, expression, customtype=False):
		assert customtype or typ in ["INVARSPEC", "LTLSPEC", "CTLSPEC", "COMPUTE"]
		assert name == None or isinstance(name, basestring)
		assert isinstance(expression, Expression)
		self._init(typ)
		self.name = name
		self.expression = expression
	
	def traverse_and_replace_all(self, function, argument):
		self.expression = self.expression.traverse_and_replace(function, argument)
	
	def prefix(self, prefix, defnames):
		ModuleElement.prefix(self, prefix, defnames)
		if self.name != None:
			self.name = "%s.%s" % (prefix, self.name)
	
	def _copy(self):
		return Specinification(self.type, self.name, self.expression, True)
	
	def string(self, names):
		if self.name == None:
			return "%s %s" % (self.type, self.expression.string(names))
		else:
			return "%s NAME %s := %s" % (self.type, self.name, self.expression.string(names))
	
	def __eq__(self, other):
		return type(self) == type(other) and self.name == other.name and self.expression == other.expression and self.type == other.type
	
class Constants(ModuleElement):
	def __init__(self, constants):
		assert isinstance(constants, list)
		assert all(isinstance(x, basestring) for x in constants)
		self._init("CONSTANTS")
		self.constants = constants
	
	def traverse_and_replace_all(self, function, argument):
		pass
	
	def _copy(self):
		Constants(copy.copy, self.constants)
	
	def string(self, names):
		return "%s %s;" % (self.type, ", ".join(self.constants))

class IsaDeclaration(ModuleElement):
	def __init__(self, module):
		assert isinstance(module, basestring)
		self._init("ISA")
		self.module = module
	
	def traverse_and_replace_all(self, function, argument):
		pass
	
	def prefix(self, prefix, defnames):
		raise StructureException("Not supported for ISA declarations.")
	
	def _copy(self):
		return IsaDeclaration(self.module)
	
	def string(self, names):
		return "%s %s" % (self.type, self.module)
		

class Comment(ModuleElement):
	"Note: Comments are not parsed but can only be added to the output"
	def __init__(self, text):
		assert isinstance(text, basestring)
		self.text = text
	
	def traverse_and_replace_all(self, function, argument):
		pass
	
	def prefix(self, prefix, defnames):
		pass
	
	def _copy(self):
		return Comment(self.text)
		
	def string(self, names):
		return "-- %s" % self.text

################################## List style ##################################

class ListModuleElement(ModuleElement):
	#Subclasses can implement a _conent_element_str method to convert content elements to strings
	def __init__(self):
		raise Exception("This is an abstract class!")
	
	def append(self, other):
		"Appends other to self"
		self.content += other.content
	
	def _content_element_str(self, el, names):
		return el.string(names)
	
	def string(self, names):
		contentstr = "\n".join(self._content_element_str(x, names) for x in self.content)
		return "%s\n%s\n" % (self.type, indent(contentstr))

class Variables(ListModuleElement):
	def __init__(self, typ, declarations):
		assert typ in ["VAR", "IVAR", "FROZENVAR"]
		assert isinstance(declarations, list)
		assert all(isinstance(x, tuple) and len(x) == 2 for x in declarations)
		assert all(isinstance(x[0], basestring) and isinstance(x[1], Type) for x in declarations)
		
		self._init(typ)
		self.content = declarations
	
	def traverse_and_replace_all(self, function, argument):
		for (_, typ) in self.content:
			if isinstance(typ, ModuleType):
				for i in xrange(len(typ.params)):
					typ.params[i] = typ.params[i].traverse_and_replace(function, argument)
	
	def _copy(self):
		return Variables(self.type, copy.copy(self.content))
	
	def prefix(self, prefix, defnames):
		ModuleElement.prefix(self, prefix, defnames)
		for i in xrange(len(self.content)):
			self.content[i] = ("%s.%s" % (prefix, self.content[i][0]) , self.content[i][1])
		
	def _content_element_str(self, x, names):
		return "%s : %s;" % (str(x[0]), x[1].string(False))

class Assignment(object):
	"Assignment in the form of name:=value or next(name):=value"
	
	def __init__(self, name, value, modifier=None):
		assert isinstance(name, (basestring, Expression))
		assert isinstance(value, Expression)
		assert isinstance(modifier, basestring) or modifier == None
#		if isinstance(name, basestring):
#			name = AstExpression(name)
		self.name = name
		self.value = value
		self.modifier = modifier
	
	def string(self, names):
		if self.modifier != None:
			return "%s(%s) := %s;" % (self.modifier, self.name.string(names), self.value.string(names))
		else:
			return "%s := %s;" % (self.name, self.value.string(names))
	
	def __str__(self):
		return self.string(False)

class AssignmentList(ListModuleElement):
	def __init__(self, typ, assignments):
		assert typ in ["ASSIGN", "DEFINE"]
		assert isinstance(assignments, list)
		assert all(isinstance(x, Assignment) for x in assignments)
		self.type = typ
		self.content = assignments
	
	def _copy(self):
		return AssignmentList(self.type, [Assignment(a.name, a.value, a.modifier) for a in self.content])
	
	def traverse_and_replace_all(self, function, argument):
		for asgn in self.content:
			asgn.name = asgn.name.traverse_and_replace(function, argument)
			asgn.value = asgn.value.traverse_and_replace(function, argument)

