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





import time, sys, re

import yicesfull
yicesfull.set_arith_only(True)
from yicesfull import _enable_log_file, YicesContext
from expressions import *

CHECK_TYPE_UNSPECIFIED = 0

NUM_LIT_RE = re.compile('\\d+')

TYPE_BOOLEAN = 0
TYPE_RANGE = 1
TYPE_REAL = 2

if sys.platform == 'win32':
	TIMER = time.clock
else:
	TIMER = time.time

class YicesException(Exception):
	pass

UNARY_OPS =  { #Both unary in yices and in NuSMV; operator -> handler
	'!' : yicesfull.YicesInternalExpression.mk_not,
}

BINARY_OPS = { #Both binary in yices and in NuSMV; operator -> handler
	'->'  : lambda x, y : x.mk_not().mk_or([y]),
	'<->' : yicesfull.YicesInternalExpression.mk_eq,
	'='   : yicesfull.YicesInternalExpression.mk_eq,
	'xor' : yicesfull.YicesInternalExpression.mk_diseq,
	'!='  : yicesfull.YicesInternalExpression.mk_diseq,
	'>'   : yicesfull.YicesInternalExpression.mk_gt,
	'>='  : yicesfull.YicesInternalExpression.mk_ge,
	'<'   : yicesfull.YicesInternalExpression.mk_lt,
	'<='  : yicesfull.YicesInternalExpression.mk_le,
}

TERNARY_OPS  = {
	'?:' : yicesfull.YicesInternalExpression.mk_ite
}

N_ARY_OPS = { #operator -> handler
	'|' : yicesfull.YicesInternalExpression.mk_or,
	'&' : yicesfull.YicesInternalExpression.mk_and,
	'+' : yicesfull.YicesInternalExpression.mk_sum,
	'*' : yicesfull.YicesInternalExpression.mk_mul,
	'-' : yicesfull.YicesInternalExpression.mk_sub,
}

JOINABLE = set(['|', '&', '*', '+'])

def join_n_ary_args(expr):
	assert isinstance(expr, AstExpression)
	assert expr[0] in JOINABLE
	
	op = expr[0]
	ret = []
	left = [expr]
	while left:
		cur = left.pop()
		if isinstance(cur, AstExpression) and cur[0] == op:
			left += list(reversed(cur[1:]))
		else:
			ret.append(cur)
	
	return ret

class FakeRa(object):
	def retract(self):
		pass

FAKE_RA = FakeRa()

class Yices(object):
	#################################
	### Yices
	context = None       # The yices context
		
	### Options
	outfile = None       # File for debug output
	
	### Variables
	vtypes = None          # variable id -> type
	vnames = None          # variable id -> name
	vars = None            # variable id -> yices internal variable
	id_by_name = None      # name -> variable id
	vtype_ids = None
	literals = None        # variable id -> as_clause -> value -> literal; not for reals
	
	### Constants
	constants = None
	const_ids = None
	const_encs = None
	
	### Defines
	defines = None # Name -> encoded expression
	
	### Debugging
	_may_push = True     # Can be used to find pushes
	
	#################################
	def __init__(self, outfile=None, cross_check = False, stats=None):
		if outfile != None:
			_enable_log_file(outfile)
		assert isinstance(cross_check, bool), (cross_check, type(cross_check))
		self.cross_check = cross_check
		
		self.context = YicesContext()
		
		self.vtypes = []
		self.vnames = []
		self.vars = []
		self.id_by_name = {}
		self.vtype_ids = []
		self.defines = {}
		self.literals = []
		self.constants = []
		self.const_ids = {}
		self.const_encs = []
		
		self.stats = stats
		if self.stats != None:
			self.stats.ycontexts += 1
	
	def add_def(self, name , enc):
		assert isinstance(name, basestring)
		assert isinstance(enc, yicesfull.YicesInternalExpression)
		assert not name in self.defines
		self.defines[name] = enc
	
	def add_constant(self, const):
		if not self.context.pushes == 0:
			raise Exception('Only at poplevel 0')
		assert not const in self.constants
		cid = len(self.constants)
		self.constants.append(const)
		self.const_ids[const] = cid
		self.const_encs.append(self.context.mk_num(cid))
		return cid
	
	def get_var(self, name):
		assert isinstance(name, basestring)
		assert name in self.id_by_name, (name, self.id_by_name.keys())
		return self.vars[self.id_by_name[name]]
	
	def add_var(self, name, typ):
		'Adds a new variable'
		assert isinstance(name, basestring)
		assert isinstance(typ, Type)
		if not self.context.pushes == 0:
			raise Exception('Only at poplevel 0')
		assert not name in self.vnames, (name, self.vnames)
		assert len(self.vtypes) == len(self.vnames)
		assert len(self.id_by_name) == len(self.vnames)
		assert len(self.vars) == len(self.vnames)
		assert len(self.vars) == len(self.vtype_ids)
		
		# Information
		vid = len(self.vtypes)
		self.vtypes.append(typ)
		if isinstance(typ, Boolean):
			self.vtype_ids.append(TYPE_BOOLEAN)
		elif isinstance(typ, Real):
			self.vtype_ids.append(TYPE_REAL)
		elif isinstance(typ, (Integer, IntEnumeration, Enumeration, Range)):
			self.vtype_ids.append(TYPE_RANGE)
		else:
			assert False
		self.vnames.append(name)
		self.id_by_name[name] = vid
		
		# Actual variable and literals
		if isinstance(typ, Boolean):
			enc = self.context.mk_bool(name)
			neg = enc.mk_not()
			#                      0,0  0,1    1,0  1,1
			self.literals.append([[neg, enc], [enc, neg]])
		elif isinstance(typ, Real):
			enc = self.context.mk_real(name)
			self.literals.append(None)
		elif isinstance(typ, Range) and typ.low >= 0:
			enc = self.context.mk_int(name)
			l = typ.low
			h = typ.high
			self.context.assertion(enc.mk_ge(self.context.mk_num(l)))
			self.context.assertion(enc.mk_le(self.context.mk_num(h)))
			if l == 0:
				asc = []
				nasc = []
				for i in xrange(l, h + 1):
					num = self.context.mk_num(i)
					nasc.append(enc.mk_eq(num))
					asc.append(enc.mk_diseq(num))
			else:
				asc = {}
				nasc = {}
				for i in xrange(l, h + 1):
					num = self.context.mk_num(i)
					nasc[i] = enc.mk_eq(num)
					asc[i] = enc.mk_diseq(num)
			self.literals.append([nasc, asc])
		elif isinstance(typ, Enumeration):
			enc = self.context.mk_int(name)
			valid_vals = [self.const_ids[x] for x in typ.values]
			assert valid_vals
			l = min(valid_vals)
			h = max(valid_vals)
			self.context.assertion(enc.mk_ge(self.context.mk_num(l)))
			self.context.assertion(enc.mk_le(self.context.mk_num(h)))
			assert l >= 0
			nasc = []
			asc = []
			for i in xrange(0, h + 1):
				assert len(nasc) == i
				assert len(asc) == i
				if i < l:
					nasc.append(None)
					asc.appen(None)
				elif not i in valid_vals:
					self.context.assertion(enc.mk_diseq(self.context.mk_num(i)))
					nasc.append(None)
					asc.appen(None)
				else:
					nasc.append(enc.mk_eq(self.context.mk_num(i)))
					asc.append(enc.mk_diseq(self.context.mk_num(i)))
			self.literals.append([nasc, asc])
		elif isinstance(typ, Integer):
			enc = self.context.mk_int(name)
			self.literals.append(None)
		elif isinstance(typ, IntEnumeration):
			enc = self.context.mk_int(name)
			vencs = []
			nasc = {}
			asc = {}
			for v in typ.values:
				num = self.context.mk_num(v)
				nasc[v] = enc.mk_eq(num)
				vencs.append(nasc[v])
				asc[v] = enc.mk_diseq(num)
			assert vencs
			
			if len(vencs) == 1:
				self.context.assertion(vencs[0])
			else:
				self.context.assertion(vencs[0].mk_or(vencs[1:]))
			self.literals.append([nasc, asc])
		else:
			raise YicesException('Variable %s has unsupported type %s' % (name, str(typ)))
		self.vars.append(enc)
		
		assert len(self.vars) == len(self.vtype_ids)
		assert len(self.vars) == len(self.vtypes)
		assert len(self.vars) == len(self.literals)
		assert enc.varid == vid
		return enc
	
	def get_time_str(self):
		return 'roughly %.2f s' % yicesfull.duration()
	
	def encode(self, expr):
		'Encodes an expression. Note that encoded expressions are cached, i.e.\n'\
		'encoding the same expression twice will not result in two interactions\n'\
		'with yices. Note, however, that popping causes all cached expressions\n'\
		'since the corresponding push to be lost. Thus, it may be efficient to\n'\
		'call encode() before pushing for exceptions that will only be used\n'\
		'after the push.'
		assert isinstance(expr, Expression), (expr, type(expr))
		stk = [[None, -1, [expr], []]]
		retval = None
		while True:
			frm = stk[-1]
			curind = frm[1]
			assert (curind == -1) == (retval == None), (curind, retval)
			if curind >= 0:
				assert len(frm[3]) == curind
				frm[3].append(retval)
			frm[1] += 1
			curind += 1
			retval = None
			if curind < len(frm[2]): # Disassemble
				expr = frm[2][curind]
				################################################################
				if isinstance(expr, Number): ###################################
					retval = self.context.mk_num(expr.value)
				################################################################
				elif isinstance(expr, BooleanConstant): ########################
					if expr.value:
						retval = self.context.mk_true()
					else:
						retval = self.context.mk_false()
				################################################################
				elif isinstance(expr, AstExpression): ##########################
					if len(expr) == 1:
						if expr[0] in self.id_by_name:
							retval = self.vars[self.id_by_name[expr[0]]]
						elif expr[0] in self.defines:
							retval = self.defines[expr[0]]
						elif expr[0] in self.const_ids:
							retval = self.const_encs[self.const_ids[expr[0]]]
						elif expr[0] in self.defines:
							retval = self.defines[expr[0]]
						else:
							print
							print 'Vars:', ', '.join(self.vnames)
							print
							print 'Definitions:', ', '.join(self.defines)
							print
							print 'Constants:', ', '.join(self.constants)
							raise YicesException('Invalid expression: %s' % str(expr))
					else:
						if expr[0] in JOINABLE:
							args = join_n_ary_args(expr)
						else:
							args = list(expr[1:])
						stk.append([expr, -1, args, []])
						continue
				################################################################
				elif isinstance(expr, CaseExpression): #########################
					assert expr.cases
					c0 = expr.cases[-1]
					assert isinstance(c0[0], BooleanConstant) and c0[0].value
					subexp = []
					for i in xrange(len(expr.cases)):
						if i < len(expr.cases) - 1:
							subexp.append(expr.cases[i][0])
						subexp.append(expr.cases[i][1])
					stk.append([expr, -1, subexp, []])
					continue
				################################################################
				else: ##########################################################
					raise YicesException('Expression %s of unsupported type %s' % (str(expr), str(type(expr))))
	
			else: # Assemble
				expr = frm[0]
				retvals = frm[3]
				assert len(retvals) == curind
				assert len(frm[2]) == curind, (curind, frm[2])
				if expr == None:
					assert len(retvals) == 1
					assert len(stk) == 1
					return retvals[0]
				else:
					if isinstance(expr, AstExpression):
						if len(expr) == 2 and expr[0] == '-': #UNARY MINUS:
							retval = self.context.mk_num(0).mk_sub([retvals[0]])
						elif expr[0] in UNARY_OPS:
							assert len(expr) == 2
							retval = UNARY_OPS[expr[0]](retvals[0])
						elif expr[0] in BINARY_OPS:
							assert len(expr) == 3
							retval = BINARY_OPS[expr[0]](retvals[0], retvals[1])
						elif expr[0] in TERNARY_OPS:
							assert len(expr) == 4
							retval = TERNARY_OPS[expr[0]](retvals[0], retvals[1], retvals[2])
						elif expr[0] in N_ARY_OPS:
							retval = N_ARY_OPS[expr[0]](retvals[0], retvals[1:])
						elif expr[0] == 'count':
							zero = self.context.mk_num(0)
							one =  self.context.mk_num(1)
							for i in xrange(len(retvals)):
								retvals[i] = retvals[i].mk_ite(one, zero)
							if len(retvals) > 1:
								retval = retvals[0].mk_sum(retvals[1:])
							else:
								retval = retvals[0]
					elif isinstance(expr, CaseExpression):
						assert len(retvals) % 2 == 1
						assert len(retvals) > 1
						retval = retvals[-1]
						for i in xrange(-3, -len(retvals)-1, -2):
							retval = retvals[i].mk_ite(retvals[i + 1], retval)
					stk.pop()
			if retval == None:
				raise YicesException('Expression %s is unsupported' % str(expr))
	
	def assertion(self, expr, retractable=False):
		assert isinstance(expr, yicesfull.YicesInternalExpression)
		if self.stats != None:
			self.stats.yassertions += 1
		if retractable:
			ret = self.context.retractable_assertion(expr)
			return ret
		else:
			self.context.assertion(expr)
	
	def assert_clause(self, clause, as_clause, primes, activation_var=None, retractable=False, single=False):
		'If retractable, a list of corresponding retractable assertions is returned'
		assert isinstance(clause, states.Clause)
		
		#Encode
		if any(x != None for x in clause):
			encs = []
			if activation_var != None:
				assert as_clause
				encs.append(activation_var.mk_not())
			
			clause.encode_lits(self, as_clause, primes, encs)
			assert len(encs) in [len(clause), len(clause) + 1]
			
			#Assert
			if as_clause:
				encs = [x for x in encs if x != None]
				if len(encs) == 1:
					enc = encs[0]
				else:
					enc = encs[0].mk_or(encs[1:])
				if retractable:
					return self.context.retractable_assertion(enc)
				else:
					self.context.assertion(enc)
			else:
				if not (retractable and single):
					ret = []
					for enc in encs:
						if enc != None:
							if retractable:
								ret.append(self.context.retractable_assertion(enc))
							else:
								self.context.assertion(enc)
						elif retractable:
							ret.append(None)
					if retractable:
						return ret
				else:
					encs = [x for x in encs if x != None]
					assert encs
					enc = encs[0]
					if len(encs) > 1:
						enc = enc.mk_and(encs[1:])
					return self.context.retractable_assertion(enc)
		else:
			#Empty list
			if as_clause:
				self.context.assertion(self.context.mk_false()) #(no need to assert true in case not negated)
			
			if retractable:
				if single or as_clause:
					return FAKE_RA
				else:
					return [None] * len(clause)
	
	def check(self, typ=None):
		if self.stats != None:
			self.stats.yqueries += 1
			if typ != None:
				self.stats.yqueries_by_type[typ] += 1
		ret = self.context.check()
		assert isinstance(ret, bool) #What does return value None mean??
		return ret
	
	def get_model(self):
		try:
			return self.context.get_model()
		except yicesfull.YicesFullException, e:
			print '\n'.join(map(str, enumerate(self.vnames)))
			raise
	
	def get_dict_model(self):
		try:
			m = self.context.get_model()
		except yicesfull.YicesFullException, e:
			print '\n'.join(map(str, enumerate(self.vnames)))
			raise
		if m == None:
			return None
		assert isinstance(m, list)
		ret = {}
		for i in xrange(len(m)):
			if m[i] != None:
				ret[self.vnames[i]] = m[i]
		return ret
	
	def is_inconsistent(self):
		return self.context.is_inconsistent()
	
	def unsat_core(self):
		ret = self.context.unsat_core()
		return ret
	
	def push(self):
		assert self._may_push
		if self.stats != None:
			self.stats.ypushes += 1
		self.context.push()
	
	def pop(self):
		if self.stats != None:
			self.stats.ypops += 1
		if self.context.pushes > 0:
			self.context.pop()
		else:
			raise YicesException('To many pops')
	
	def poplevel(self):
		return self.context.pushes



def __dbg_mem(strn):
	if __DBGMEM:
		import gc, objgraph
		print
		print '#' * 80
		print '#' * 80
		print '##', strn
		print 'Collect', gc.collect()
		print 'Collect', gc.collect()
	
		roots = objgraph.get_leaking_objects()
		if roots:
			print len(roots)
			objgraph.show_most_common_types(objects=roots)
			objgraph.show_refs(roots[:3], refcounts=True, filename='tmp/%s.png' % strn.lower())
		else:
			print 'Nothing'
		print '#' * 80	
		print '#' * 80
		print

__DBGMEM = False

import states

if __name__ == '__main__':
	expr = AstExpression('+', ('+', ('+', 'a', ('*', ('+', 'b', 'c'), 'd')), ('-', ('+', 'e', 'f'), 'g')), ('+', 'h', 'i'))
	print expr
	print '(', ' ) + ( '.join(map(str, join_n_ary_args(expr))), ')'
	
	yi = Yices('y.txt')
	yi.add_var('a', BOOLEAN)
	yi.add_var('b', BOOLEAN)
	yi.add_var('c', BOOLEAN)
	exprs = [AstExpression('->', 'a', 'b'), AstExpression('->', 'c', ('!','b')), AstExpression('->', ('!', 'b'), ('!', 'c')), AstExpression('->', ('!', 'c'), 'b'), AstExpression('=', 'a', 'b')]
	ras = []
	for ex in exprs:
		ras.append(yi.assertion(yi.encode(ex), retractable=True))
	
	for i in xrange(len(exprs)):
		print i, ras[i], exprs[i]
	
	print
	print 'Check', yi.check()
	print 'Model:', yi.get_model()
	print 'Dict model:', yi.get_dict_model()
	print
	
	yi.push()
	expr = AstExpression('->', 'b', 'c')
	print expr
	ras.append(yi.assertion(yi.encode(expr), retractable=True))
	exprs.append(expr)
	
	print
	print 'Check', yi.check()
	print
	
	print 'Unsat core'
	usc = yi.unsat_core()
	print '\n'.join(map(str, usc))
	print
	for i in xrange(len(ras)):
		if ras[i] in usc:
			print exprs[i]
	
	yi.pop()
	print
	print yi.check()

