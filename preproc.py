#!/usr/bin/python
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






import copy,sys

from expressions import *
from nusmv_modules import *

SUPPORTED_SECTIONS = ['INIT', 'VAR', 'INVARSPEC', 'LTLSPEC', 'INVAR', 'TRANS', 'CTLSPEC', 'DEFINE', 'CONSTANTS'] #, 'URGENT']
SPECIAL_CONSTANTS  = set(['TRUE', 'FALSE'])

PRIME_SUFFIX = '-prime'

class PreprocessingException(Exception):
	def __init__(self, *msg):
		self.msg = msg
	
	def __str__(self):
		return self.msg[0] % self.msg[1:]

class TypeException(Exception):
	def __init__(self, msg, expr, types=None):
		assert isinstance(msg, basestring)
		assert isinstance(expr, Expression)
		assert types == None or isinstance(types, list)
		assert types == None or all(isinstance(t, Type) for t in types)
		self.msg = msg
		self.expr = expr
		self.types = types
	
	def __str__(self):
		strn = '%s in expression %s' % (self.msg, str(self.expr))
		if self.types != None:
			if len(self.types) == 1:
				strn += '\nGot type: %s' % str(self.types[0])
			else:
				strn += '\nGot types: %s and %s' % (', '.join(map(str, self.types[:-1])), str(self.types[-1]))
		return strn

class BreakException(Exception):
	'Used for spaghetti code'
	def __init__(self, value):
		self.value = value
	def __str__(self):
		return '%s: %s' % (str(type(self)), str(self.value))

# Helpers
def _expect(cond, msg, *fmt):
	if not cond:
		raise PreprocessingException(msg % fmt)

def _iter_vars(module):
	'Turn two loops into one'
	for vs in module.get_all_iter('VAR'):
		for c in vs.content:
			yield c

def join_prefix(pref, name):
	if pref:
		return '%s.%s' % (pref, name)
	else:
		return name

def split_prefix(pref):
	if '.' in pref:
		ind = pref.rindex('.')
		return pref[:ind], pref[ind+1:]
	else:
		return '', pref

# Collecting iformation

def _get_variable_info(model, modname):
	'Returns variables, modules, resets'                           \
	'  variables: (prefix, name) -> type (with module types inlined'\
	'  modules:   prefix -> (module name, argument names, arguments)'\
	'  resets:    (prefix, clock name) -> reset condition'
	assert isinstance(model, Program)
	assert isinstance(modname, basestring)
	
	variables = {}
	modules   = {'' : ('main', [], [])}
	resets    = {}
	
	stk = [('', _iter_vars(model.modules[modname]))] # Stack with (prefix, module)
	while stk:
		prefix, iterator = stk[-1]
		for name, typ in iterator:
			if isinstance(typ, ModuleType):
				_expect(not typ.process, 'Process variables are not supported')
				if typ.module == 'clock':
					_expect(len(typ.params) == 1, 'Invalid number of arguments for clock %s; expected one', name)
					resets[(prefix, name)] = typ.params[0]
					typ = REAL
				else:
					_expect(typ.module in model.modules, 'Invalid type: %s', typ)
					nprefix = join_prefix(prefix, name)
					modules[nprefix] = (typ.module, model.modules[typ.module].params, typ.params)
					stk.append((nprefix, _iter_vars(model.modules[typ.module])))
					break
			variables[(prefix, name)] = typ
		else:
			stk.pop()
	return variables, modules, resets

def _get_declared_constants(model, modules):
	ret = set()
	for modname, _, __ in modules:
		for cs in model.modules[modname].get_all_iter('CONSTANTS'):
			ret.update(cs.constants)
	return ret

def _get_constraints(model, modules, typ):
	'Returns list of (prefix, constraint) with the constraint being an expression'
	ret = []
	for prefix, (modname, _, __) in modules.iteritems():
		for constr in model.modules[modname].get_all_iter(typ):
			assert isinstance(constr, Constraint)
			ret.append((prefix, constr.expression))
	return ret
	
def _add_assignments(model, modules, initials, transitions):
	for prefix, (modname, _, __) in modules.iteritems():
		for asgns in model.modules[modname].get_all_iter('ASSIGN'):
			for asgn in asgns.content:
				var = asgn.name
				if asgn.modifier == 'next':
					var = AstExpression('next', var)
					addto = transitions
				else:
					assert asgn.modifier == 'init', asgn.modifier
					addto = initials
				addto.append((prefix, AstExpression('=', var, asgn.value)))

def _get_invar_properties(model, modules):
	'Returns list of (prefix, property) with property being an invariant property given as an expression'
	ret = []
	for prefix, (modname, _, __) in modules.iteritems():
		for spec in model.modules[modname].get_all_iter('INVARSPEC'):
			assert isinstance(spec, Specification)
			ret.append((prefix, spec.expression))
	return ret

def _get_defs(model, modules):
	ret = {}
	for prefix, (modname, _, __) in modules.iteritems():
		for defs in model.modules[modname].get_all_iter('DEFINE'):
			assert isinstance(defs, AssignmentList)
			for asgn in defs.content:
				assert isinstance(asgn.name, basestring)
				assert isinstance(asgn.value, Expression)
				assert asgn.modifier == None
				ret[(prefix, asgn.name)] = asgn.value
	return ret


# Processing
def combine_types(a, b):
	'Returns a type that can take values of both types if possible or None otherwise'
	assert isinstance(a, (Enumeration, Range, Real, Boolean, IntEnumeration)), (a, type(a))
	assert isinstance(b, (Enumeration, Range, Real, Boolean, IntEnumeration)), (b, type(b))
	if a == b:
		return a
	elif type(a) == type(b):
		if isinstance(a, Enumeration):
			vals = copy.copy(a.values)
			for val in b.values:
				if not val in vals:
					vals.append(val)
			return Enumeration(vals)
		elif isinstance(a, IntEnumeration):
			return IntEnumeration(sorted(set(a.values).union(set(b.values))))
		else:
			assert isinstance(a, Range)
			return Range(min(a.low, b.low), max(a.high, b.high))
	elif isinstance(a, (Range, IntEnumeration)) and isinstance(b, (Range, IntEnumeration)):
		if isinstance(a, Range):
			b, a = a, b
		assert isinstance(a, IntEnumeration)
		assert isinstance(b, Range)
		return Range(min(min(a.values), b.low), max(max(a.values), b.high))

def get_type(variables, deftypes, constants, expr, typecheck):
	assert isinstance(expr, Expression)
	stk = [[None, -1, [expr], []]] # Frames: Surrounding expression, next index to check, subexpressions, types of expressions checked
	                               #         0                       1                    2               3
	                               # next index -1 means trying to infer without looking at subexpressions
	while True:
		frm = stk[-1]
		
		quick_check = frm[1] == -1 and not typecheck and frm[0] != None
		thorough_check = frm[1] >= len(frm[2])
		assert not thorough_check or len(frm[2]) == len(frm[3])
		if quick_check or thorough_check: ###### Check types (potentially) based on subexpression types
			tp = None
			expr = frm[0]
			types = frm[3]
			if expr == None: ### Done; return
				assert len(stk) == 1
				assert len(frm[3]) == 1
				return frm[3][0]
			assert isinstance(expr, (AstExpression, CaseExpression))
			if isinstance(expr, AstExpression): ### Ast expression
				if not (quick_check and expr[0] in ["+", '*', "mod", "-", "?:"]):
					if expr[0] in ["X", "G", "F", "Y", "Z", "H", "O", "EX", "AX", "EF", "AF", "EG", "AG", "!"]:
						assert quick_check or len(types) == 1
						if typecheck and types[0] != BOOLEAN:
							raise TypeException("Expecting boolean argument", expr)
						tp = BOOLEAN
					elif expr[0] == "next":
						assert quick_check or len(types) == 1
						tp = types[0]
					elif expr[0] in ["U", "V", "S", "T", "EU", "AU", "&", "|", "xor", "xnor", "->", "<->"]:
						assert quick_check or len(types) == 2
						if typecheck and (types[0] != BOOLEAN or types[1] != BOOLEAN):
							raise TypeException("Expected two boolean arguments", expr)
						tp = BOOLEAN
					elif expr[0] in ["=", "!="]:
						assert quick_check or len(types) == 2
						if typecheck and isinstance(types[0], (Range, IntEnumeration)):
							types[0] = INTEGER
						if typecheck and isinstance(types[1], (Range, IntEnumeration)):
							types[1] = INTEGER
						if typecheck and \
								types[0] != types[1] \
								and not (types[0] == INTEGER and types[1] == REAL) \
								and not (types[1] == INTEGER and types[0] == REAL) \
								and not (isinstance(types[0], Enumeration) and isinstance(types[1], Enumeration)):
							raise TypeException("Expected same type on both sides but got %s and %s" % (types[0], types[1]), expr)
						tp = BOOLEAN
					elif expr[0] in ["<", ">", "<=", ">="]:
						assert quick_check or len(types) == 2
						if typecheck and (not isinstance(types[0], (Range, Real, Integer, IntEnumeration)))\
						             and (not isinstance(types[1], (Range, Real, Integer, IntEnumeration))):
							raise TypeException("Expected two integer or clock arguments", expr, types)
						tp = BOOLEAN
					elif expr[0] in ["+", "*", "mod", "-"]:
						assert quick_check or len(types) == 2
						if typecheck and (not (isinstance(types[0], (Range, IntEnumeration, Integer)))
								 or (not (isinstance(types[1], (Range, IntEnumeration)) or types[1] == INTEGER))):
							raise TypeException("Expected two integer arguments", expr, types)
						if isinstance(types[0], IntEnumeration):
							types[0] = Range(min(types[0].values), max(types[0].values));
						if isinstance(types[1], IntEnumeration):
							types[1] = Range(min(types[1].values), max(types[1].values));
#						print '!!!!', expr, map(str, types), typecheck
						if isinstance(types[0], Range) and isinstance(types[1], Range):
							if expr[0] == "+":
								tp = Range(types[0].low + types[1].low, types[0].high + types[1].high)
							elif expr[0] == "-":
								tp = Range(types[0].low - types[1].high, types[0].high - types[1].low)
							elif expr[0] == "*":
								tp = Range(min(types[0].low * types[1].low, types[0].high * types[1].low, types[0].low * types[1].high, types[0].high * types[1].high), 
										     max(types[0].low * types[1].low, types[0].high * types[1].low, types[0].low * types[1].high, types[0].high * types[1].high))
							elif expr[0] == "mod":
								if typecheck and (types[0].low < 0 or types[1].low < 0):
									raise TypeException("Modulo for negative numbers is not safe with respect to semantics in different tools", self)
								tp = Range(0, types[1].high - 1)
							else:
								assert False
						else:
							tp = INTEGER
					elif expr[0] == "?:":
						assert quick_check or len(types) == 3
						if typecheck and types[0] != BOOLEAN:
							raise TypeException("Expecting first argument to be boolean", expr)
#						print '-'
#						print expr
#						print types[1]
#						print types[2]
						tp = combine_types(types[1], types[2])
						if typecheck and tp == None:
							raise TypeException("Expecting second and third argument to have compatible types", expr)
					elif expr[0] == 'count':
						assert quick_check or types
						if typecheck and not all(x == BOOLEAN for x in types):
							raise TypeException('Expecting boolean arguments', expr)
						tp = INTEGER
			else: ### Case expression
				assert isinstance(expr, CaseExpression) 
				if not quick_check:
					if typecheck: # check lhs is boolean
						for i in xrange(0, len(types), 2):
							if types[i] != BOOLEAN:
								raise TypeException('Left hand side expression of type %s in case expression -- should be boolean'\
															% str(types[i]), frm[2][i])
#					print '-'
#					print expr
#					print '\n'.join(map(str, types))
					tp = types[1]
					for i in xrange(3, len(types), 2):
						tp = combine_types(tp, types[i])
					if tp == None:
						raise TypeException('Incompatible right hand side types in case expression', expr, types)
			if tp != None: # "Return" type
				stk.pop()
				frm = stk[-1]
				frm[3][frm[1]-1] = tp
				continue
			elif thorough_check:
				raise TypeException('Could not determine type', expr)
			assert not thorough_check or tp != None
		elif frm[1] >= 0: ###### Check single instance
			expr = frm[2][frm[1]]
			assert isinstance(expr, (AstExpression, CaseExpression, Constant)), type(expr)
			if isinstance(expr, AstExpression):
				if len(expr) == 1: # Ast leaf
					strn = expr[0]
					if strn in variables:
						tp = variables[strn]
					elif strn in deftypes:
						tp = deftypes[strn]
					elif typecheck:
						_expect(strn in constants, 'Undeclared constant "%s" -- declare all constants in a CONSTANTS section', strn)
						tp = Enumeration([strn])
					else:
						raise TypeException('Could not determine type', expr)
				else: # Ast inner node -- recursion
					stk.append([expr, -1, list(expr[1:]), []])
					tp = None
			elif isinstance(expr, CaseExpression): # Case expression -- recursion
				exprs = []
				for (a, b) in expr.cases:
					exprs.append(a)
					exprs.append(b)
				stk.append([expr, -1, exprs, []])
				tp = None
			else: # Constants
				assert isinstance(expr, Constant)
				if isinstance(expr, Number):
					tp = IntEnumeration([expr.value])
				else:
					assert isinstance(expr, BooleanConstant)
					tp = BOOLEAN
			frm[3].append(tp)
		frm[1] += 1
		assert len(frm[3]) == frm[1], (frm[3], frm[1])

#variables, definitions, constants, expr, prefix
class RewriteExpr(object):
	'Decorator for iterating over expressions. Takes arguments variables, '\
	'definitions, constants, x, ... and calls the decorated function with '\
	'argument y, ... for any subexpression y of x that is of the expected type '\
	'If the decorated function returns an expression, it is used to replace y '\
	'and no subexpressions of the original or new y are passed to the decorated '\
	'function'
	
	def __init__(self, variables, definitions, ast_expressions=False):
		self.for_vars = variables
		self.for_defs = definitions
		self.for_ast = ast_expressions
	
	def actual_call(self, variables, definitions, constants, expr, prefix, *arguments):
		assert isinstance(variables, dict)
		assert all(isinstance(x, basestring) for x in variables)
		assert all(isinstance(x, Type) for x in variables.itervalues())
		assert all(isinstance(x, basestring) for x in definitions)
		assert all(isinstance(x, basestring) for x in constants)
		assert isinstance(expr, Expression)
		assert isinstance(prefix, basestring)
		newexp = None
		stk = [[None, 2, False, expr]] # Contains "frames": [original expression, next index to be processed, changes, subexpressions...]
		                               #                     0                    1                           2        3
		while True:
			# "Return value"
			frm = stk[-1]
			if newexp != None:
				assert frm[1] >= 3
				frm[frm[1]] = newexp
				frm[2] = True
			frm[1] += 1
			newexp = None
			
			# Process current expression
			if frm[1] < len(frm):
				cur = frm[frm[1]]
				assert isinstance(cur, Expression), (cur, type(cur))
				assert isinstance(cur, (AstExpression, CaseExpression, Constant)) # Note: no named expressions, no variables
				if isinstance(cur, AstExpression):
					if len(cur) == 1:
						assert isinstance(cur[0], basestring)
						qualified = join_prefix(prefix, cur[0])
						if qualified in definitions:
							if self.for_defs:
								newexp = self.func(frm[0], cur, prefix, True, *arguments)
						elif qualified in variables:
							if self.for_vars:
								newexp = self.func(frm[0], cur, prefix, False, *arguments)
						else:
							try:
								assert cur[0] in constants, (str(stk[0][3]), str(cur[0]))
							except:
								print
								print 'Expression:', expr
								print 'Vars: ', ', '.join(variables)
								print 'Defs: ', ', '.join(definitions)
								print 'Consts: ', ', '.join(constants)
								raise
					else:
						if self.for_ast:
							newexp = self.func(frm[0], cur, prefix, False, *arguments)
						if newexp == None:
							stk.append([cur, 2, False] + list(cur[1:])) # "Recursion"
				elif isinstance(cur, CaseExpression):
					frm = [cur, 2, False]
					for (a, b) in cur.cases:
						frm.append(a)
						frm.append(b)
					stk.append(frm)  # "Recursion"
				elif isinstance(cur, Constant):
					pass
				else:
					assert False, type(cur)
			else: #### Re-assmbly
				cur = frm[0]
				if cur == None:
					assert len(stk) == 1
					assert len(frm) == 4
					return frm[3]
				elif isinstance(cur, AstExpression):
					if frm[2]:
						newexp = AstExpression(cur[0], *frm[3:])
				else:
					assert isinstance(cur, CaseExpression)
					if frm[2]:
						assert (len(frm) - 3) % 2 == 0
						cases = []
						for i in xrange(3, len(frm), 2):
							cases.append((frm[i], frm[i+1]))
						newexp = CaseExpression(cases)
				stk.pop() # "Return"
	
	def __call__(self, func):
		self.func = func
		return self.actual_call

def _prefix_keys(dct):
	ret = {}
	for (pref, name), val in dct.iteritems():
		ret[join_prefix(pref, name)] = val
	return ret

@RewriteExpr(True, True)
def _prefix_expression(surrounding, expr, prefix, is_def, defs_used):
	assert isinstance(expr, AstExpression)
	assert len(expr) == 1
	assert isinstance(expr[0], basestring)
	if defs_used != None and is_def:
		defs_used.add(join_prefix(prefix, expr[0]))
	if prefix:
		return AstExpression(join_prefix(prefix, expr[0]))

@RewriteExpr(False, True)
def _count_def_usage(surrounding, expr, prefix, is_def, use_cnt):
	assert not prefix
	assert is_def
	assert isinstance(expr, AstExpression)
	assert len(expr) == 1
	assert isinstance(expr[0], basestring)
	use_cnt[expr[0]] = use_cnt.get(expr[0], 0)

@RewriteExpr(False, True)
def _inline_defs(surrounding, expr, prefix, is_def, definitions):
	assert not prefix
	assert is_def
	assert isinstance(expr, AstExpression)
	assert len(expr) == 1
	assert isinstance(expr[0], basestring)
	if expr[0] in definitions:
		return definitions[expr[0]]

@RewriteExpr(True, False)
def _get_clock_constants(surrounding, expr, prefix, is_def, variables, clock_constants):
	assert not prefix
	assert not is_def
	assert isinstance(expr, AstExpression)
	assert isinstance(expr[0], basestring)
	assert expr[0] in variables
	if variables[expr[0]] == REAL:
		assert surrounding != None # Should be ruled out by type checking
		assert isinstance(surrounding, AstExpression)
		assert surrounding[0] in ['=', '!=', '<', '<=', '>', '>=']
		assert len(surrounding) == 3
		other = surrounding[2] if surrounding[1] == expr else surrounding[1]
		assert isinstance(other, Number), (other, type(other))
		clock_constants[expr[0]] = max(clock_constants.get(expr[0], 0), other.value)

@RewriteExpr(True, True, False)
def primed(surrounding, expr, prefix, is_def):
	assert not prefix
	assert isinstance(expr, AstExpression)
	assert len(expr) == 1
	return AstExpression(expr[0] + PRIME_SUFFIX)

@RewriteExpr(False, False, True)
def non_primed(surrounding, expr, prefix, is_def, variables, definitions, constants):
	assert not is_def
	assert not prefix
	assert isinstance(expr, AstExpression)
	assert len(expr) > 1
	if expr[0] == 'next':
		assert len(expr) == 2
		return primed(variables, definitions, constants, expr[1], prefix)

@RewriteExpr(False, True, False)
def find_used_definitions(surrounding, expr, prefix, is_def, used):
	assert is_def
	assert isinstance(expr, AstExpression)
	assert len(expr) == 1
	assert isinstance(expr[0], basestring)
	assert not prefix
	assert isinstance(used, set)
	used.add(expr[0])

@RewriteExpr(False, False, True)
def uses_primed(surrounding, expr, prefix, is_def):
	assert not prefix
	assert isinstance(expr, AstExpression)
	assert len(expr) > 1
	assert not is_def
	if expr[0] == 'next':
		raise BreakException(True)

def _prefix_expressions(variables, definitions, constants, lst):
	assert isinstance(lst, list)
	for i in xrange(len(lst)):
		prefix, expr = lst[i]
		lst[i] = _prefix_expression(variables, definitions, constants, expr, prefix, None)

def _prefix_values(variables, definitions, constants, dct, get_def_use=False):
	def_use = {} if get_def_use else None
	for k in dct.iterkeys():
		dus = set() if get_def_use else None
		prefix, _ = k
		dct[k] = _prefix_expression(variables, definitions, constants, dct[k], prefix, dus)
		if get_def_use:
			def_use[k] = dus
	return def_use


#import debugging
def _prime_expressions(variables, defnames, constants, lst, prime=False):
	for i in xrange(len(lst)):
		if prime:
			nexp = primed(variables, defnames, constants, lst[i], '')
		else:
			nexp = non_primed(variables, defnames, constants, lst[i], '', variables, defnames, constants)
		if nexp != None:
			lst[i] = nexp

def _prime_values(variables, defnames, constants, dct, prime=False):
	for k in dct:
		if prime:
			nexp = primed(variables, defnames, constants, dct[k], '')
		else:
			nexp = non_primed(variables, defnames, constants, dct[k], '', variables, defnames, constants)
		if nexp != None:
			dct[k] = nexp

def preprocess(model, typecheck, def_vars, prop_interested_in, full_xinvariant, verbose = False, **kwargs):
	'Returns:'                                                              \
	'  Variables: name -> type\n'                                            \
	'  Initial constraint:      lists of expressions of type boolean\n'       \
	'  Invariant:               lists of expressions of type boolean\n'        \
	'  Urgency constraint:      lists of expressions of type boolean\n'         \
	'  Transition Constraint:   lists of expressions of type boolean\n'          \
	'  Reset conditions:        Clock name -> expression\n'                       \
	'  Specifications:          lists of expressions of type boolean\n'            \
	'  Original specifications: list of (prefix, expression) whit the expression\n' \
	'                           being unaltered, i.e. without argument replacement\n'\
	'                           or inlined definitions'
	global g_list_of_original_definitions
	
	try:
		###### Collect information  ################################################
	
		### Variables
		variables, modules, resets = _get_variable_info(model, 'main')
		if verbose:
			print 'Variables:'
			print ' ', '\n  '.join('%s %s %s' % (x, y, z) for (x, y), z in variables.iteritems())
			print
			print 'Modules:'
			print ' ', '\n  '.join('%s %s(%s)' % (x[0], x[1][0], ', '.join(map(str, x[1][1]))) for x in modules.iteritems())
			print
			print 'Resets:'
			print ' ', '\n  '.join('%s %s %s' % (x, y, z) for (x, y), z in resets.iteritems())
			print
	
		### Constants
		constants = _get_declared_constants(model, modules.itervalues())
		for typ in variables.itervalues():
			if isinstance(typ, Enumeration):
				constants.update(typ.values)
		if verbose:
			print 'Constants:'
			print ' ', ', '.join(constants)
			print
	
		### Initial constraint
		initials    = _get_constraints(model, modules, 'INIT')
	
		### Transition relation
		transitions = _get_constraints(model, modules, 'TRANS')
	
		### Assignments
		_add_assignments(model, modules, initials, transitions)
		if verbose:
			print 'Initial constraints:'
			print ' ', '\n  '.join(('%s %s' % x).replace('\n', '\n    ') for x in initials)
			print
			print 'Transition constraints:'
			print ' ', '\n  '.join(('%s %s' % x).replace('\n', '\n    ') for x in transitions)
			print
	
		### Invariant
		invariants  = _get_constraints(model, modules, 'INVAR')
		if verbose:
			print 'Invariants:'
			print ' ', '\n  '.join(('%s %s' % x).replace('\n', '\n    ') for x in invariants)
			print
	
		### Urgency constraints
		urgencies   = _get_constraints(model, modules, 'URGENT')
		if verbose:
			print 'Urgency constraints:'
			print ' ', '\n  '.join(('%s %s' % x).replace('\n', '\n    ') for x in urgencies)
			print
	
		### Properties
		properties = _get_invar_properties(model, modules)
		orgprops = copy.copy(properties)
	
		if verbose:
			print 'Properties:'
			print ' ', '\n  '.join(('%s %s' % x).replace('\n', '\n    ') for x in properties)
			print
		
		if prop_interested_in >= len(properties):
			raise PreprocessingException('No property %d', prop_interested_in)
		properties = [properties[prop_interested_in]]

		### Definitions
		definitions = _get_defs(model, modules)
		g_list_of_original_definitions = {}
		if 'get_original_def_info' in kwargs and kwargs['get_original_def_info']:
			for pref, n in definitions:
				g_list_of_original_definitions[join_prefix(pref, n)] = None
#			print g_list_of_original_definitions
	
		###### Process information #################################################
		
		### Arguments to definitions
		for prefix, (_, argnames, args) in modules.iteritems():
			pref, subpref = split_prefix(prefix)
			_expect(len(argnames) == len(args), 'Wrong number of arguments for variable %s', prefix)
			for i, aname in enumerate(argnames):
				definitions[(pref, '%s.%s' % (subpref, aname))] = args[i]
		
		if verbose:
			print 'Definitions:'
			print ' ', '\n  '.join(('%s %s %s' % (x, y, z)).replace('\n', '\n    ') for (x, y), z in definitions.iteritems())
			print
				
		### Inline modules
		variables = _prefix_keys(variables)
		defnames  = set(join_prefix(pref, name) for pref, name in definitions)
	
		_prefix_expressions(variables, defnames, constants, initials)
		_prefix_expressions(variables, defnames, constants, invariants)
		_prefix_expressions(variables, defnames, constants, transitions)
		_prefix_expressions(variables, defnames, constants, urgencies)
		_prefix_expressions(variables, defnames, constants, properties)
	
		def_use = _prefix_values(variables, defnames, constants, definitions, True)
		_prefix_values(variables, defnames, constants, resets)
		definitions = _prefix_keys(definitions)
		resets      = _prefix_keys(resets)
		def_use     = _prefix_keys(def_use)
	
		if verbose:
			print '-' * 80
			print 'Initial constraints:'
			print ' ', '\n  '.join(str(x).replace('\n', '\n    ') for x in initials)
			print
			print 'Transition constraints:'
			print ' ', '\n  '.join(str(x).replace('\n', '\n    ') for x in transitions)
			print
			print 'Invariants:'
			print ' ', '\n  '.join(str(x).replace('\n', '\n    ') for x in invariants)
			print
			print 'Definitions:'
			print ' ', '\n  '.join(('%s %s' % (x, z)).replace('\n', '\n    ') for x, z in definitions.iteritems())
			print
			print 'Urgency constraints:'
			print ' ', '\n  '.join(str(x).replace('\n', '\n    ') for x in urgencies)
			print
			print 'Properties:'
			print ' ', '\n  '.join(str(x).replace('\n', '\n    ') for x in properties)
			print
			print 'Resets:'
			print ' ', '\n  '.join('%s %s' % (x, z) for x, z in resets.iteritems())
			print
		
		multi_usage = set(variables).intersection(defnames)
		multi_usage.update(set(variables).intersection(constants))
		multi_usage.update(defnames.intersection(constants))
		if multi_usage:
			raise PreprocessingException('Identifier(s) used multiple times: %s' % ', '.join(multi_usage))
		
		### Prime things
		unprimed_vars = set(variables)
		_prime_expressions(variables, defnames, constants, initials)
		_prime_expressions(variables, defnames, constants, invariants)
		_prime_expressions(variables, defnames, constants, transitions)
		_prime_expressions(variables, defnames, constants, urgencies)
		_prime_expressions(variables, defnames, constants, properties)
	
		xinvariants = copy.copy(invariants)
		_prime_expressions(variables, defnames, constants, xinvariants, True)
		xinitials = copy.copy(initials)
		_prime_expressions(variables, defnames, constants, xinitials, True)
		xproperties = copy.copy(properties)
		_prime_expressions(variables, defnames, constants, xproperties, True)
		
		if 'get_original_def_info' in kwargs and kwargs['get_original_def_info']:
			for dn in g_list_of_original_definitions:
				g_list_of_original_definitions[dn] = definitions[dn]
		
		# Direct transition definitions (i.e. contain next() on right hand side)
		transdefs = set()
		for d, expr in definitions.items():
			try:
				uses_primed(variables, definitions, constants, expr, '')
			except BreakException, e:
				assert e.value
				transdefs.add(d)
		
		# Indirect transition definitions
		du_inv = {}
		for d, us in def_use.iteritems():
			for u in us:
				du_inv.setdefault(u, set()).add(d)
		todo = copy.copy(transdefs)
		while todo:
			nxt = set()
			for d in todo:
				nxt.update(du_inv.get(d, []))
			nxt -= transdefs
			transdefs.update(nxt)
			todo = nxt
		
		xdefs = {}
		for d, expr in definitions.iteritems():
			if not d in transdefs:
				xdefs[d] = expr
		_prime_values(variables, defnames, constants, resets)
		_prime_values(variables, defnames, constants, definitions)
		_prime_values(variables, defnames, constants, xdefs, True)
		for x, v in xdefs.iteritems():
			xl = x + PRIME_SUFFIX
			definitions[xl] = v
		for v, t in variables.items():
			variables[v + PRIME_SUFFIX] = t
		
		### Drop unused definitions
		if not ('get_original_def_info' in kwargs and kwargs['get_original_def_info']):
			used = set()
			for exprs in [initials, xinitials, transitions, invariants, xinvariants, urgencies, properties, xproperties, resets.itervalues()]:
				for expr in exprs:
					find_used_definitions(variables, definitions, constants, expr, '', used)
		
			if verbose:
				print 'Used by other:', ', '.join(used)
			def_use = {}
			left = copy.copy(used)
			done = set()
			while left:
				df = left.pop()
				done.add(df)
				dfdu = set()
				find_used_definitions(variables, definitions, constants, definitions[df], '', dfdu)
				def_use[df] = dfdu
				used.update(dfdu)
				left.update(dfdu - done)
			if verbose:
				print 'Used:', ', '.join(used)
	
			if full_xinvariant:
				additional = []
				for u in used:
					if not u in transdefs:
						if u.endswith(PRIME_SUFFIX):
							additional.append(u[:-len(PRIME_SUFFIX)])
						else:
							additional.append(u + PRIME_SUFFIX)
				used.update(additional)
	
			assert all(x in definitions for x in used)
	
			if verbose:
				print 'Kept:', ', '.join(used)
	
			for df in definitions.keys():
				if not df in used:
					if verbose:
						print 'Deleting', df
					del definitions[df]
	
			assert used == set(definitions.iterkeys()), (str(used), str(definitions.keys()))
		
		### Type checking
		# Make def_use transitive
		for k in def_use:
			to_add = copy.copy(def_use[k])
			while to_add:
				cur = to_add.pop()
				new = def_use[cur] - def_use[k]
				to_add.update(new)
				def_use[k].update(new)
			if k in def_use[k]:
				raise PreprocessingException('Self dependent definition: %s' % k)
	
		# Suitable order for checking definition types
		order = []
		in_order = set()
		while def_use:
			for df in def_use.keys():
				if not (def_use[df] - in_order):
					del def_use[df]
					order.append(df)
					in_order.add(df)
		if verbose:
			print '-' * 80
			print 'Order:', ', '.join(order)
	
		# Check types
		if typecheck or def_vars:
			deftypes = {}
			for dname in order:
				deftypes[dname] = get_type(variables, deftypes, constants, definitions[dname], typecheck)
			if full_xinvariant:
				for dname in definitions:
					if not dname in deftypes:
						if dname.endswith(PRIME_SUFFIX):
							odname = dname[:-len(PRIME_SUFFIX)]
						else:
							odname = dname + PRIME_SUFFIX
						deftypes[dname] = deftypes[odname]
			assert set(deftypes) == set(definitions), (map(str, deftypes), map(str, definitions))
		if typecheck:
			for i, exprs in enumerate([initials, xinitials, transitions, invariants, xinvariants, urgencies, properties, xproperties, resets.itervalues()]):
				                      #0         1          2            3           4            5          6           7            8
				for ex in exprs:
					try:
						if get_type(variables, deftypes, constants, ex, typecheck) != BOOLEAN:
							raise TypeError('None-boolean constraint', ex)
					except:
						raise
	
		if verbose:
			print 'Definition types:'
			for tpl in deftypes.iteritems():
				print '  %s %s' % tpl
			print
		
		if 'get_original_def_info' in kwargs and kwargs['get_original_def_info']:
			for dn in g_list_of_original_definitions:
				g_list_of_original_definitions[dn] = get_type(variables, deftypes, constants, g_list_of_original_definitions[dn], True)
		
		# Check clock usage
		if typecheck:
			if REAL in variables.itervalues():
				dct = {}
				for expr in initials:
					_get_clock_constants(variables, definitions, constants, expr, '', variables, dct)
					if dct:
						raise TypeException('Clock used in initial constraint', expr)
				for expr in urgencies:
					_get_clock_constants(variables, definitions, constants, expr, '', variables, dct)
					if dct:
						raise TypeException('Clock used in urgency constraint', expr)
		
		### Inline definitions
		#Always inline: used once only; variable or constant
		def_cnt = {}
		for exprs in [initials, xinitials, transitions, invariants, xinvariants, urgencies, properties, xproperties, resets.itervalues()]:
			for expr in exprs:
				_count_def_usage(variables, definitions, constants, expr, '', def_cnt)
	
		inline = set(d for d, c in def_cnt.iteritems() if c == 1)
		for d, expr in definitions.iteritems():
			if isinstance(expr, AstExpression) and len(expr) == 1:
				assert isinstance(expr[0], basestring)
				assert expr[0] in definitions or expr[0] in variables or expr[0] in constants
				inline.add(d)
			elif isinstance(expr, Constant):
				inline.add(d)
		
		if def_vars:
			definition_vars = set(definitions) - inline
		else:
			definition_vars = set()
		
		if verbose:
			print 'To be inlined:', ', '.join(inline)
			print
		
		# Inline definitions
		restr_defs = {}
		for dn in inline:
			restr_defs[dn] = definitions[dn]
#		print '\n'.join(inline)
		
#		print '-' * 80
#		print '\n'.join(invariants)
#		print '-' * 80
	
		for dn in order:
			definitions[dn] = _inline_defs(variables, definitions, constants, definitions[dn], '', restr_defs)
			if dn in restr_defs:
				restr_defs[dn] = definitions[dn]
		
		for k in resets:
			resets[k] = _inline_defs(variables, definitions, constants, resets[k], '', restr_defs)
		
		dnset = set(definitions)
		if def_vars:
			for dn, expr in definitions.iteritems():
				if not dn in inline:
#					print dn, expr
					variables[dn] = deftypes[dn]
					if dn in transdefs:
						assert not dn.endswith(PRIME_SUFFIX)
						transitions.append(AstExpression('=', dn, expr))
					elif dn.endswith(PRIME_SUFFIX):
						xinvariants.append(AstExpression('=', dn, expr))
					else:
						invariants.append(AstExpression('=', dn, expr))
			definitions = {}
				
#		print '=' * 80
#		print '\n '.join(map(lambda x : str(x).replace('\n', ' '),invariants))
#		print '-' * 80
		
		for lst in [initials, xinitials, transitions, invariants, xinvariants, urgencies, properties, xproperties]:
			for i in xrange(len(lst)):
#				strn = str(lst[i])
#				if strn.startswith('mod_C_D.OR4.BO1_FAULT-prime'):
#					print strn,
				lst[i] = _inline_defs(variables, dnset, constants, lst[i], '', restr_defs)
#				if strn.startswith('mod_C_D.OR4.BO1_FAULT-prime'):
#					print str(lst[i])
	
		if not ('get_original_def_info' in kwargs and kwargs['get_original_def_info']):
			for dn in inline:
				if dn in definitions:
					del definitions[dn]
					del deftypes[dn]
	
		deflist = [(dn, definitions[dn]) for dn in order if (dn in definitions and not dn in inline)]
	
		if verbose:
			print '-' * 80
			print 'Variables:'
			print ' ', '\n  '.join('%s::%s' % x for x in variables.iteritems())
			print
			print 'Initial constraints:'
			print ' ', '\n  '.join(str(x).replace('\n', '\n    ') for x in initials)
			print
			print 'next(Initial constraints):'
			print ' ', '\n  '.join(str(x).replace('\n', '\n    ') for x in xinitials)
			print
			print 'Transition constraints:'
			print ' ', '\n  '.join(str(x).replace('\n', '\n    ') for x in transitions)
			print
			print 'Invariants:'
			print ' ', '\n  '.join(str(x).replace('\n', '\n    ') for x in invariants)
			print 'next(Invariants):'
			print ' ', '\n  '.join(str(x).replace('\n', '\n    ') for x in xinvariants)
			print
			print 'Definitions:'
			for x, z in deflist:
				print ' ', 'T' if x in transdefs else ' ', ('%s %s' % (x, z)).replace('\n', '\n    ')
			print
			print 'Urgency constraints:'
			print ' ', '\n  '.join(str(x).replace('\n', '\n    ') for x in urgencies)
			print
			print 'Properties:'
			print ' ', '\n  '.join(str(x).replace('\n', '\n    ') for x in properties)
			print
			print 'next(Properties):'
			print ' ', '\n  '.join(str(x).replace('\n', '\n    ') for x in xproperties)
			print
			print 'Resets:'
			print ' ', '\n  '.join('%s %s' % (x, z) for x, z in resets.iteritems())
			print
				
		### Clock constants
		clock_constants = {}
		if REAL in variables.itervalues():
			for i, exprs in enumerate([(e for n, e in deflist), initials, xinitials, transitions, invariants, xinvariants, urgencies, resets.itervalues(), properties, xproperties]):
				for expr in exprs:
					_get_clock_constants(variables, definitions, constants, expr, '', variables, clock_constants)
			for clk in clock_constants.keys(): # Drop primes
				if clk.endswith(PRIME_SUFFIX):
					sclk = clk[:-len(PRIME_SUFFIX)]
					clock_constants[sclk] = max(clock_constants.get(sclk, 0), clock_constants[clk])
					del clock_constants[clk]
			for var in variables.keys(): # Drop unused clocks
				if variables[var] == REAL and not var.endswith(PRIME_SUFFIX):
					if not var in clock_constants:
						del variables[var]
						del resets[var]
		
			if verbose:
				print 'Clock constants:'
				for nm, cnst in clock_constants.iteritems():
					print ' ', nm, ' ', cnst
				print
		
		return (variables, unprimed_vars, definition_vars), (deflist, transdefs), (initials, xinitials, transitions, invariants, xinvariants, urgencies, resets, properties[0], xproperties[0]), orgprops, clock_constants
	except:
#		print typecheck, def_vars, prop_interested_in, full_xinvariant, verbose
		raise

if __name__ == '__main__':
	import sys
	import nusmv_yacc
	args = sys.argv[1:]
	if len(args) != 1:
		print 'Usage: <model-file>'
		sys.exit(1)
	
	inf = open(args[0], 'r')
	model = nusmv_yacc.parser.parse(inf.read())
	inf.close()
	
	preprocess(model, True, False, 0, True, True, get_original_def_info=True)

