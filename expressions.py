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






class TypeException(Exception):
	def __init__(self, msg, expr):
		assert isinstance(msg, basestring)
		assert isinstance(expr, Expression)
		self.msg = msg
		self.expr = expr
	
	def __str__(self):
		return "%s in expression %s" % (self.msg, str(self.expr))

#print TypeException("test", "expr")

################################################################################
################################ GENERIC STUFF #################################
################################################################################
def indent(strn, cnt=2):
	ind = " " * cnt
	strn = strn.split("\n")
	for i in xrange(len(strn)):
		if strn[i]:
			strn[i] = "  %s" % strn[i]
	return "\n".join(strn)

def replace_callback(expr, _, (a, b)):
	for (i, x) in enumerate(a):
		if expr == x:
			return b[i]
	return None

def replace_dict_callback(expr, _, dct):
	if expr in dct:
		return dct[expr]

def var_callback(expr, _, st):
	if isinstance(expr, Variable):
		st.add(expr)
	return None

class Expression(object):
	"NOTE: Expressions are expected to be immutable!"
	def __init__(self):
		raise Exception("Abstract class")
	
	def variables(self):
		ret = set()
		self.traverse_and_replace(var_callback, ret)
		return ret
	
	def traverse_and_replace(self, function, argument):
		"""Traverses the expression and calls the function for every
		subexpression. The function should take three arguments. The first
		argument passed is the current subexpression. The second argument is
		the next level surrounding expression or None for the top-level
		expression. The third argument is the argument passed to the
		traverse_and_replace function. The expression is traversed in preorder.
		
		The function may return either None or another expression. If another
		expression is returned, the expression passed to the function will be
		replaced with the returned expression. Note that in this case the
		traversal will not continue into any subexpressions, neither of the
		replaced nor of the replacing expression.
		
		The traversal starts by giving the top-level expression (i.e. self) to
		the function. If the function decides to replace the top-level
		expression, the replacement expression is returned by
		traverse_and_replace. In this case, the caller is responsible for
		carrying out the replacement. Otherwise, traverse_and_replace
		returns self."""
		raise Exception("Abstract method")
	
	def element_str(self, names):
		"Same as to_string, except that parantheses will be added around compound expressions"
		raise Exception("Abstract method")
	
	def __str__(self):
		return self.string(False)
		
	def string(self, names):
		"Returns a string representing the expression. If names is set to True,\n"
		"names will be used for named expressions instead of the actual expression"
		raise Exception("Abstract method")
	
	def __neq__(self, other):
		return not self == other
	
	def replace(self, a, b):
		"If a and b are expressions, every occurence of a is replaced with b.\n"+\
		"If both a lists, the ith expression in a is replaced with the ith in b."
		assert isinstance(a, (list, Expression))
		assert isinstance(b, (list, Expression))
		
		if not isinstance(a, list):
			a = [a]
		if not isinstance(b, list):
			b = [b]
		
		assert all(isinstance(x, Expression) for x in a)
		assert not isinstance(b, list) or all(isinstance(x, Expression) for x in b)
		
		return self.traverse_and_replace(replace_callback, (a, b))
	
	def __hash__(self):
		raise Exception("Abstract method")
	
	def get_type(self, check, type_info):
		raise Exception("Abstract method")

################################################################################
################################ AST EXPRSSIONS ################################
################################################################################

################################ OPERATOR TYPES ################################

TEMPORAL_LOGIC_OPERATORS = ["X", "G", "F", "Y", "Z", "H", "O", "U", "V", "S", "T", "EX", "AX", "EF", "AF", "EG", "AG", "EU", "AU", "EBF", "ABF", "EBG", "ABG", "ABU", "EBU"]
FUNCTION_STYLE = ["next", "word1", "bool", "toint", "swconst", "uwconst", "signed", "unsigned", "sizeof", "extend", "resize"]

############################# NUMBER OF ARGUMENTS ##############################
ARGS_COUNT = [
#0 args:
[],

#1 arg:
["X", "G", "F", "Y", "Z", "H", "O", "EX", "AX", "EF", "AF", "EG", "AG", "!",
    "next", "word1", "bool", "toint", "signed", "unsigned", "sizeof"],
    
# 2 args:
["U", "V", "S", "T", "EU", "AU", "&", "|", "xor", "xnor", "->", "<->", "=",
    "!=", "<", ">", "<=", ">=", "+", "*", "/", "mod", ">>", "<<", "::", "union",
    "in", "swconst", "uwconst", "extend", "resize", "[]", "MIN", "MAX", "EBF",
    "ABF", "EBG", "ABG", ".."],

#3 args:
["?:", "[:]", "ABU", "EBU"]
]

VARARGS = ["count", "{}"]#Variable argument count

EXPECTED_ARGUMENT_COUNT = {}
for (i, ops) in enumerate(ARGS_COUNT):
	for op in ops:
		EXPECTED_ARGUMENT_COUNT[op] = set([i])
for op in VARARGS:
	EXPECTED_ARGUMENT_COUNT[op] = None
EXPECTED_ARGUMENT_COUNT["-"] = set([1,2]) #Unary or binary


VARARGS = ["count", "{}"]#Variable argument count


def _to_ast_operand(arg):
	assert isinstance(arg, (tuple, basestring, Expression, list)), "%s %s" % (str(arg), str(type(arg)))
	if isinstance(arg, Expression):
		return arg
	elif isinstance(arg, basestring):
		return AstExpression(arg)
	else:
		assert isinstance(arg, (tuple, list))
		assert not isinstance(arg, AstExpression)
		if len(arg) == 1:
			return _to_ast_operand(arg[0])
		else:
			return AstExpression(arg)

def _to_ast_argument_list(arg):
	assert len(arg) > 0
	done = False
	while not done:
		done = True
		if isinstance(arg, (tuple, list)) and len(arg) == 1:
			#(x,) -> x
			arg = arg[0]
			done = False
		if isinstance(arg, (tuple, list)) and arg and not arg[0]:
			#("", x) -> x
			assert len(arg) == 2
			arg = arg[1]
			done = False
	if isinstance(arg, (tuple, list)):
		assert isinstance(arg[0], basestring) #operator
		
		ret = [arg[0]] + map(_to_ast_operand, arg[1:])
	else:
		ret = [arg]
	return ret


class AstExpression(Expression, tuple):
	def __new__(self, *a):
		#Convince the tuple subclass to take more than one argument
		return tuple.__new__(self, _to_ast_argument_list(a))
	
	def __init__(self, *_):
		#Note that tuple.__new__ has already been executed at this point and
		#therefore there is no need to do anything with the arguments
		assert len(self) > 0
		assert all(isinstance(x, (Expression, basestring)) for x in self)
		assert isinstance(self[0], basestring)
		
		if len(self) == 1:
			assert isinstance(self[0], basestring)
		else:
			assert self[0] in EXPECTED_ARGUMENT_COUNT, self
			argcnt = EXPECTED_ARGUMENT_COUNT[self[0]]
			if argcnt != None:
				assert len(self) - 1 in argcnt, (len(self), argcnt)
	
	def traverse_and_replace(self, function, argument, _surrounding=None):
		ret = function(self, _surrounding, argument)
		
		if ret == None:
			replacements = None
			for i in xrange(1, len(self)):
				if isinstance(self[i], Expression):
					oldid = id(self[i])
					ret = self[i].traverse_and_replace(function, argument, self)
					if id(ret) != oldid:
						if replacements == None:
							replacements = list(self)
						replacements[i] = ret
			if replacements == None:
				return self
			else:
				return AstExpression(replacements)
		else:
			assert isinstance(ret, Expression)
			return ret
		
	
	def element_str(self, names):
		"""Returns a string representation of self that can be used as an operator
		with arbitrary operators, i.e. is surrounded by parentheses if necessary"""
		if len(self) == 1:
			assert isinstance(self[0], basestring)
			return self[0]
		elif self[0] in ["AU", "EU", "..", "ABU", "EBU", "count", "[]", "[:]", "{}"] + FUNCTION_STYLE: #Do not need parentheses around
			return self.string(names)
		else:
			return "(%s)" % self.string(names)
	
	def string(self, names):
		strnfn = lambda x : x.string(names)
		if len(self) == 1:
			assert isinstance(self[0], basestring)
			return self[0]
		elif self[0] == "count":
			#Count statements
			return "%s(%s)" % (self[0], ", ".join(map(strnfn, self[1:])))
		elif self[0] == "{}":
			#Sets
			return "%s%s%s" % (self[0][0], ", ".join(map(strnfn, self[1:])), self[0][1])
		else:
			assert 2 <= len(self) <= 4
			if len(self) == 2:
				if self[0] in FUNCTION_STYLE:
					#Function-style
					return "%s(%s)" % (self[0], strnfn(self[1]))
				elif self[0] in TEMPORAL_LOGIC_OPERATORS:
					#Temporal logic
					return "%s %s" % (self[0], self[1].element_str(names))
				else:
					#Normal unary operator
					return "%s%s" % (self[0], self[1].element_str(names))
			elif len(self) == 3:
				if self[0] in FUNCTION_STYLE:
					#Function-style
					return "%s(%s, %s)" % (self[0], strnfn(self[1]), strnfn(self[2]))
				elif self[0] in ["EU", "AU"]:
					#Temporal logic -- until
					return "%s[%s %s %s]" % (self[0][0], self[1].element_str(names), self[0][1], self[2].element_str(names))
				elif self[0] in ["MIN", "MAX"]:
					#Compute expressions
					return "%s[%s, %s]" % (self[0], strnfn(self[1]), strnfn(self[2]))
				elif self[0] in ["EBF", "ABF", "EBG", "ABG"]:
					#Temproal logic -- G/F
					return "%s %s %s" % (self[0], strnfn(self[1]), strnfn(self[2]))
				elif self[0] == "[]":
					#Index
					return "%s[%s]" % (self[1].element_str(names), strnfn(self[2]))
				else:
					#Normal binary operator
					return "%s %s %s" % (self[1].element_str(names), self[0], self[2].element_str(names))
			else:
				if self[0] in ["EBU", "ABU"]:
					#Temporal logic
					return "%s[%s %s %s %s]" % (self[0][0], strnfn(self[2]), self[0][1:], strnfn(self[1]), strnfn(self[3]))
				elif self[0] == "[:]":
					#Index
					return "%s[%s, %s]" % (self[1].element_str(names), strnfn(self[2]), strnfn(self[3]))
				else:
					#Question mark operator
					assert self[0] == "?:"
					return "%s ? %s : %s" % (self[1].element_str(names), self[2].element_str(names), self[3].element_str(names))
	
	def get_type(self, check, type_info):
		assert isinstance(check, bool)
		assert isinstance(type_info, dict)
		assert all(isinstance(x, basestring) for x in type_info), repr([str(x) for x in type_info])
		assert all(isinstance(x, Type) for x in type_info.itervalues())
		if len(self) == 1:
			assert isinstance(self[0], basestring)
			if self[0] in ["TRUE", "FALSE"]:
				return BOOLEAN
			elif all(x in "0123456789" for x in self[0]):
				val = int(self[0])
				return Range(val, val)
			elif self[0] in type_info:
				return type_info[self[0]]
			else:
				raise TypeException("Could not find matching type for expression", self)
		else:
			if check or self[0] in ["+", "*", "mod", "-", "?:"]:
				types = [x.get_type(check, type_info) for x in self[1:]]
			
			if self[0] in ["X", "G", "F", "Y", "Z", "H", "O", "EX", "AX", "EF", "AF", "EG", "AG", "!"]:
				assert (not check) or len(types) == 1
				if check and types[0] != BOOLEAN:
					raise TypeException("Expecting boolean argument", self)
				return BOOLEAN
			elif self[0] == "next":
				assert (not check) or len(types) == 1
				return types[0]
			elif self[0] in ["U", "V", "S", "T", "EU", "AU", "&", "|", "xor", "xnor", "->", "<->"]:
				assert (not check) or len(types) == 2
				if check and (types[0] != BOOLEAN or types[1] != BOOLEAN):
					raise TypeException("Expected two boolean arguments", self)
				return BOOLEAN
			elif self[0] in ["=", "!="]:
				assert (not check) or len(types) == 2
				if check and isinstance(types[0], Range):
					types[0] = INTEGER
				if check and isinstance(types[1], Range):
					types[1] = INTEGER
				if check and \
						types[0] != types[1] \
						and not (types[0] == INTEGER and isinstance(types[1], ModuleType) and types[1].module == 'clock') \
						and not (types[1] == INTEGER and isinstance(types[0], ModuleType) and types[0].module == 'clock'):
					raise TypeException("Expected same type on both sides but got %s and %s" % (types[0], types[1]), self)
				return BOOLEAN
			elif self[0] in ["<", ">", "<=", ">=", "+", "*", "/", "mod", "-"]:
				assert (not check) or len(types) == 2
				if check and (not (isinstance(types[0], Range) or types[0] == INTEGER))\
				         and (not (isinstance(types[1], Range) or types[1] == INTEGER)):
					raise TypeException("Expected two integer arguments", self)
				if self[0] in ["<", ">", "<=", ">="]:
					return BOOLEAN
				elif isinstance(types[0], Range) and isinstance(types[1], Range):
					if self[0] == "+":
						return Range(types[0].low + types[1].low, types[0].high + types[1].high)
					elif self[0] == "-":
						return Range(types[0].low - types[1].high, types[0].high - types[1].low)
					elif self[0] == "*":
						return Range(min(types[0].low * types[1].low, types[0].high * types[1].low, types[0].low * types[1].high, types[0].high * types[1].high), 
						             max(types[0].low * types[1].low, types[0].high * types[1].low, types[0].low * types[1].high, types[0].high * types[1].high))
					elif self[0] == "mod":
						if check and (types[0].low < 0 or types[1].low < 0):
							raise TypeException("Modulo for negative numbers is not safe with respect to semantics in different tools", self)
						return Range(0, types[1].high - 1)
					else:
						return INTEGER
				else:
					return INTEGER
			elif self[0] == "?:":
				assert (not check) or len(types) == 3
				if types[0] != BOOLEAN:
					raise TypeException("Expecting first argument to be boolean", self)
				if types[1] != types[2]:
					if (types[1] == INTEGER and isinstance(types[2], Range)) or (types[2] == INTEGER and isinstance(types[1], Range)):
						return INTEGER
					elif isinstance(types[1], Range) and isinstance(types[2], Range):
						return Range(min(types[1].low, types[2].low), max(types[1].high, types[2].high))
					else:
						raise TypeException("Expecting second and third argument to have the same types", self)
				return types[1]
	def __hash__(self):
		return tuple.__hash__(self)

#ast_from_binary_operator_and_list = reduce_to_ast
def reduce_to_ast(op, lst):
	"[a,b,...,x,y] -> (((...(a ~ b) ~ ... ) ~ x) ~ y)\n"+\
	"E.g. sum, product, ..."
	assert isinstance(op, basestring)
	assert isinstance(lst, list)
	assert lst
	assert all(isinstance(x, Expression) for x in lst)
	
	expr = lst[0]
	for x in lst[1:]:
		expr = AstExpression(op, expr, x)
	return expr

def reduce_to_ast_commutative(op, lst, default=None):
	if not lst:
		assert default != None
		lst = [default]
	assert lst
	if len(lst) == 1:
		return lst[0]
	elif len(lst) == 2:
		return AstExpression(op, lst[0], lst[1])
	else:
		pivot = len(lst) / 2
		return AstExpression(op, reduce_to_ast_commutative(op, lst[:pivot]), reduce_to_ast_commutative(op, lst[pivot:]))

def to_constant_string(arg):
	if isinstance(arg, bool):
		if arg:
			return "TRUE"
		else:
			return "FALSE"
	elif isinstance(arg, (int, long)):
		return str(arg)
	else:
		assert isinstance(arg, basestring)
		return arg

################################################################################
############################### MISC EXPRSSIONS ################################
################################################################################


class CaseExpression(Expression):
	def __init__(self, cases):
		assert isinstance(cases, list)
		assert all(isinstance(c, tuple) and isinstance(c[0], Expression) and isinstance(c[1], Expression) for c in cases), cases
		self.cases = cases
	
	def traverse_and_replace(self, function, argument, _surrounding=None):
		ret = function(self, _surrounding, argument)
		
		if ret == None:
			#Call recursively
			ret = []
			for (c, v) in self.cases:
				ret.append((c.traverse_and_replace(function, argument, self), v.traverse_and_replace(function, argument, self)))
			
			#Check for changes and return self if there are none
			for i in xrange(len(self.cases)):
				if id(self.cases[i][0]) != id(ret[i][0]) or id(self.cases[i][1]) != id(ret[i][1]):
					break
			else:
				return self
			
			return CaseExpression(ret)
		else:
			assert isinstance(ret, Expression)
			return ret
	
	def element_str(self, names):
		return self.string(names)
	
	def string(self, names):
		strns = []
		for c in self.cases:
			if isinstance(c[1], CaseExpression):
				strns.append("%s :\n%s;" % (c[0].string(names), indent(c[1].string(names))))
			else:
				strns.append("%s : %s;" % (c[0].string(names), c[1].string(names)))
		return "case\n%s\nesac" % indent("\n".join(strns))
	
	def __eq__(self, other):
		return type(self) == type(other)               \
		       and len(self.cases) == len(other.cases)  \
		       and all(self.cases[i] == other.cases[i] for i in xrange(len(self.cases)))
	
	def __hash__(self):
		return hash(tuple(self.cases))
	
	def get_type(self, check, type_info):
		if not self.cases:
			raise TypeException("Empty case expression", self)
		tp = self.cases[0][1].get_type(check, type_info)
		if check:
			for (l, r) in self.cases:
				if l.get_type(check, type_info) != BOOLEAN:
					raise TypeException("Left hand side case expression value is not of type boolean", self)
				tp2 = r.get_type(check, type_info)
				if tp2 != tp:
					if (tp == INTEGER and isinstance(tp2, Range)) or (tp2 == INTEGER and isinstance(tp, Range)):
						tp = INTEGER
					elif isinstance(tp, Range) and isinstance(tp2, Range):
						tp = Range(min(tp.low, tp2.low), max(tp.high, tp2.high))
					else:
						raise TypeException("Different right hand side types in case expression", self)
		return tp

class NamedExpression(Expression):
	def __init__(self, name, expr):
		assert isinstance(name, basestring)
		self.name = name
		if not isinstance(expr, Expression):
			expr = AstExpression(expr)
		self.expr = expr
	
	def get_type(self, check, type_info):
		return self.expr.get_type(check, type_info)
	
	def string(self, names):
		if names:
			return "<<%s>>" % self.name
		else:
			return self.expr.string(names)
	
	def element_str(self, names):
		if names:
			return "<<%s>>" % self.name
		else:
			return self.expr.element_str(names)
	
	
	def traverse_and_replace(self, function, argument, _surrounding=None):
		"Name is lost once content changes"
		ret = self.expr.traverse_and_replace(function, argument, self)
		if id(ret) != id(self.expr):
			return ret
		else:
			return self
	
	def __eq__(self, other):
		return type(self) == type(other) and self.name == other.name and self.expr == other.expr
	
	def __hash__(self):
		return hash((self.name, self.expr))

class Variable(Expression):
	def __init__(self, name, typ):
		assert isinstance(name, basestring)
		self.name = name
		self.type = typ
	
	def get_type(self, check, type_info):
		return self.type
	
	def string(self, names):
		if names:
			return "%s::[%s]" % (self.name, self.type.string(False)) #False because the self.type may again have self as param
		else:
			return self.name
	
	def element_str(self, names):
		return self.string(names)
	
	def traverse_and_replace(self, function, argument, _surrounding=None):
		ret = function(self, _surrounding, argument)
		if ret == None:
			return self;
		else:
			assert isinstance(ret, Expression)
			return ret
	
	def __repr__(self):
		return "Variable(%s, %s)" % (self.name, repr(self.type))
	
	def __eq__(self, other):
		return type(self) == type(other) and self.name == other.name and self.type == other.type
	
	def __hash__(self):
		if isinstance(self.type, ModuleType):
			return hash((self.name, self.type.module, len(self.type.params), self.type.process)) #NOTE - module type + self referenceing leads to in
		else:
			return hash((self.name, self.type))

class Constant(Expression):
	def __init__(self, val):
		assert isinstance(val, self._VALID_TYPES)
		self.value = val
	
	def traverse_and_replace(self, function, argument, _surrounding=None):
		ret = function(self, _surrounding, argument)
		if ret == None:
			return self;
		else:
			assert isinstance(ret, Expression)
			return ret
	
	def __eq__(self, other):
		return type(self) == type(other) and self.value == other.value
	
	def __hash__(self):
		return hash(self.value)

class Number(Constant):
	_VALID_TYPES = (int, long)
	def get_type(self, check, type_info):
		return Range(self.value, self.value)
	
	def string(self, names):
		return str(self.value)
	
	def element_str(self, names):
		return str(self.value)
	
	def __repr__(self):
		return 'Number(%d)' % self.value

class BooleanConstant(Constant):
	_VALID_TYPES = bool
	def get_type(self, check, type_info):
		return BOOLEAN
	
	def string(self, names):
		return 'TRUE' if self.value else 'FALSE'
	
	def element_str(self, names):
		return self.string(names)
	
	def __repr__(self):
		return 'Boolean(%s)' % self.string(False)

################################################################################
#################################### Types #####################################
################################################################################

class Type(object):
	def __init__(self):
		raise Exception("This is an abstract class!")
	
	def __ne__(self, other):
		return not self.__eq__(other)
	
	def __eq__(self):
		raise Exception("Abstract method")
	
	def __hash__(self):
		raise Exception("Abstract method")
	
	def __str__(self):
		return self.string(False)

class Boolean(Type):
	def __init__(self):
		pass
	
	def string(self, names):
		return "boolean"
	
	def __eq__(self, other):
		return isinstance(other, Boolean)

	def __hash__(self):
		return 606177

BOOLEAN = Boolean()

class Word(Type):
	def __init__(self, signed, bits):
		assert signed == None or isinstance(signed, bool) #None meaning not specified
		assert isinstance(bits, (int, long))
		self.signed = signed
		self.bits = bits

	def __hash__(self):
		return hash((type(self), self.signed, self.bits))
	
	def __eq__(self, other):
		return isinstance(other, Word) and other.signed == self.signed
	
	def string(self, names):
		strn = "word[%d]" % self.bits
		if self.signed == None:
			return strn
		else:
			return ("signed " if self.signed else "unsigned ") + strn

class Enumeration(Type):
	def __init__(self, values):
		assert isinstance(values, list), values
		assert values
		assert all(isinstance(x, basestring) for x in values), values
		assert len(set(values)) == len(values)
		self.values = values
		self.values.sort()

	def __hash__(self):
		return hash((type(self), tuple(sorted(self.values))))
	
	def __eq__(self, other):
		return type(self) == type(other) and self.values == other.values
	
	def string(self, names):
		return "{%s}" % ", ".join(self.values)

class IntEnumeration(Type):
	def __init__(self, values):
		assert isinstance(values, list)
		assert values
		if all(isinstance(x, Number) for x in values):
			self.values = [x.value for x in values]
		else:
			assert all(isinstance(x, (int, long)) for x in values)
			self.values = values
		self.values.sort()
		assert len(self.values) == len(set(self.values))
	
	def __hash(self):
		return hash((type(self),) + tuple(self.values))
	
	def __eq__(self, other):
		return type(self) == type(other) and self.values == other.values
	
	def string(self, names):
		return '{%s}' % ', '.join(map(str, self.values))

class Array(Type):
	def __init__(self, low_index, high_index, typ):
		assert isinstance(low_index, (int, long))
		assert isinstance(high_index, (int, long))
		assert isinstance(typ, Type)
		self.low_index = low_index
		self.high_index = high_index
		self.type = typ

	def __hash__(self):
		return hash((type(self), self.low_index, self.high_index, self.type))
	
	def __eq__(self, other):
		return isinstance(other, Array) and self.low_index == other.low_index and self.high_index == other.high_index and self.type == other.type
	
	def string(self, names):
		return "array %d .. %d of %s" % (self.low_index, self.high_index, str(self.type))

class Range(Type):
	def __init__(self, low, high):
		assert isinstance(low, (int, long))
		assert isinstance(high, (int, long))
		self.low = low
		self.high = high
	
	def __hash__(self):
		return hash((type(self), self.low, self.high))
	
	def __eq__(self, other):	
		return type(self) == type(other) and self.low == other.low and self.high == other.high
	
	def string(self, names):
		return "%d .. %d" % (self.low, self.high)

class EnumRange(Range):
	# Replacement for enumeration types
	def __init__(self, values):
		Range.__init__(self, 0, len(values) - 1)
		self.values = values
	
	def string(self, names):
		return "enum(%d..%d):%s" % (self.low, self.high, str(self.values))
	
	def __getitem__(self, ind):
		'String to int and vice versa conversion'
		if isinstance(ind, basestring):
			assert ind in self.values
			return self.values.index(ind)
		else:
			assert isinstance(ind, (int, long))
			assert 0 <= ind and ind <= len(self.values)
			return self.values[ind]

class ModuleType(Type):
	def __init__(self, module, params, process):
		assert isinstance(module, basestring)
		assert isinstance(params, list)
		assert all(isinstance(x, Expression) for x in params)
		assert isinstance(process, bool)
		self.module = module
		self.params = params
		self.process = process

	def __hash__(self):
		return hash((self.module, tuple(self.params), self.process))
	
	def __eq__(self, other):
		return isinstance(other, ModuleType) and self.module == other.module and self.params == other.params and self.process == other.process
	
	def string(self, names):
		strn = self.module
		if self.params:
			strn +=  "(%s)" % ", ".join(x.string(names) for x in self.params)
		if self.process:
			strn = "process " + strn
		return strn

class Real(Type):
	def __init__(self):
		pass
	
	def __eq__(self, other):
		return type(self) == type(other)
	
	def __hash__(self):
		return 209629
	
	def string(self, names):
		return "real"
	
	def __repr__(self):
		return "Real"

REAL = Real()

class Integer(Type):
	def __init__(self):
		pass
	
	def __eq__(self, other):
		return type(self) == type(other)
	
	def __hash__(self):
		return 123692978
	
	def string(self, names):
		return "int"
	
	def __repr__(self):
		return "Integer"

INTEGER = Integer()

ZERO = Number(0)

################################################################################
################################################################################
################################################################################
################################################################################
################################################################################
################################################################################
################################################################################
if __name__ == "__main__":
	expr = AstExpression("*", "2", NamedExpression("named", "x"))
	print expr
	expr = CaseExpression([(AstExpression("a"), expr), (Variable("b", "int"), AstExpression("1"))])
	print expr
	print expr.string(False)
	print expr.string(True)
	expr = NamedExpression("expr", expr)
	print "-" * 80
	print expr
	print expr.string(False)
	print expr.string(True)

