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





import sys, itertools, copy, operator
import config, preproc, expressions, byices, stats, states, brind

VAR_AT_STEP_FMT = '%s-%d'

VERBOSITY_DISEQ = 1
VERBOSITY_TRACES = 2

@preproc.RewriteExpr(True, True, False)
def at_step(surrounding, expr, prefix, is_def, index):
	assert not prefix
	assert isinstance(expr, expressions.AstExpression)
	assert len(expr) == 1
	assert isinstance(expr[0], basestring)
	base = expr[0]
	if base.endswith(preproc.PRIME_SUFFIX):
		base = base[:-len(preproc.PRIME_SUFFIX)]
		index += 1
	return expressions.AstExpression(VAR_AT_STEP_FMT % (base, index))

class BMC(object):
	FULL_XINVARIANT = True
	COMPLETE = False
	INT_FRAC_SPLIT = False
	def __init__(self, variables, clockmax, special_vars, constants, initials,    \
	             xinitials, invariants, xinvariants, transitions, prop, xproperty, \
	             definitions, transition_definitions, statistics):
		assert isinstance(variables, dict)
		assert all(isinstance(x, basestring) for x in variables)
		assert all(isinstance(y, expressions.Type) for y in variables.itervalues())
		assert isinstance(clockmax, dict)
		assert all(isinstance(x, basestring) for x in clockmax)
		assert all(isinstance(y, (int, long)) for y in clockmax.itervalues())
		assert all((not x in  variables) for x in clockmax)
		assert isinstance(special_vars, dict)
		assert all(isinstance(x, basestring) for x in special_vars)
		assert all(isinstance(y, expressions.Type) for y in special_vars.itervalues())
		assert all((not x in variables) for x in special_vars)
		if isinstance(constants, list):
			constants = set(constants)
		assert isinstance(constants, set)
		assert all(isinstance(x, basestring) for x in constants)
		assert all(isinstance(x, expressions.Expression) for x in initials)
		assert all(isinstance(x, expressions.Expression) for x in xinitials)
		assert all(isinstance(x, expressions.Expression) for x in invariants)
		assert all(isinstance(x, expressions.Expression) for x in xinvariants)
		assert all(isinstance(x, expressions.Expression) for x in transitions)
		assert isinstance(prop, expressions.Expression)
		assert isinstance(xproperty, expressions.Expression)
		assert all(isinstance(x, expressions.Expression) for x in invariants)
		assert isinstance(definitions, list)
		assert all(isinstance(x, tuple) for x in definitions)
		assert all(len(x) == 2 for x in definitions)
		assert all(isinstance(x[0], basestring) for x in definitions)
		assert all(isinstance(x[1], expressions.Expression) for x in definitions)
		assert all(any(a  == x[0] for x in definitions) for a in transition_definitions)
		assert isinstance(statistics, stats.BrindStats)
		
#		print '-' * 80
#		print 'init'
#		print '\n'.join(map(str, initials))
#		print
#		print '-' * 80
#		print 'xinit'
#		print '\n'.join(map(str, xinitials))
#		print
#		print '-' * 80
#		print 'invar'
#		print '\n'.join(map(str, invariants))
#		print
#		print '-' * 80
#		print 'xinvar'
#		print '\n'.join(map(str, xinvariants))
#		print
		
		# Configurations
		if type(self) == BMC:
			self.bound = config.bmc_bound
			assert self.bound > 0
		
		# Collect variables; etc.
		self.clockmaxdict = clockmax
		self.variables = variables.copy()
		for clk in self.clockmaxdict:
			self.variables[clk] = expressions.REAL
		# Split up variables if necessary
#		print 'a', self.variables.keys()
		self.variables.update(special_vars) # All variables are equal
		if self.INT_FRAC_SPLIT:
			for nm in self.variables.keys():
				if self.variables[nm] == expressions.REAL:
					del self.variables[nm]
					self.variables[nm + brind.INT_SUFFIX] = expressions.INTEGER
					self.variables[nm + brind.FRAC_SUFFIX] = expressions.REAL
#		print 'b', self.variables.keys()
		for v in self.variables.keys():
			self.variables[v + preproc.PRIME_SUFFIX] = self.variables[v]
#		print 'c', self.variables.keys()
		
#		# Drop primed vriables
#		self.variables = self.all_vars.copy()
#		for n, t in variables.items():
#			if n.endswith(preproc.PRIME_SUFFIX):
#				del self.variables[n]
		
#		print 'd', self.variables.keys()
		
		# Find valid variable order
		clocks = sorted(self.clockmaxdict)
		self.ordered_vars = clocks
		self.clockcount = len(self.ordered_vars)
		if self.INT_FRAC_SPLIT:
			self.clockvarcount = 2 * self.clockcount
		else:
			self.clockvarcount = self.clockcount
		self.clockmax = [self.clockmaxdict[x] for x in self.ordered_vars]
		if self.INT_FRAC_SPLIT:
			self.ordered_vars = reduce(operator.add, ([x + brind.INT_SUFFIX, x + brind.FRAC_SUFFIX] for x in self.ordered_vars))
		for vn in sorted(variables):
			assert not vn.endswith(preproc.PRIME_SUFFIX)
			assert not vn in self.ordered_vars
			if not vn in self.clockmaxdict:
				self.ordered_vars.append(vn)
		self.varcount = len(self.ordered_vars)
		if self.INT_FRAC_SPLIT:
			self.svnames = clocks + self.ordered_vars[self.clockvarcount:]
		else:
			self.svnames = self.ordered_vars
		for vn, t in special_vars.iteritems():
			assert not vn in self.ordered_vars
			if not vn.endswith(preproc.PRIME_SUFFIX):
				if self.INT_FRAC_SPLIT and t == expressions.REAL:
					self.ordered_vars.append(vn + brind.INT_SUFFIX)
					self.ordered_vars.append(vn + brind.FRAC_SUFFIX)
				else:
					self.ordered_vars.append(vn)
		self.special_vars = special_vars
		
		
		# Other stuff
		self.constants = constants
		self.initials = initials
		self.invariants = invariants
		self.transitions = transitions
		self.property = prop
		
		# Definitions
		self.all_defs = set(x[0] for x in definitions)
		self.definitions = definitions
		self.transition_definitions = transition_definitions
		
		# More other stuff
		self.statistics = statistics
		self.var_low = []
	
	def at_step(self, expr, index):
		ret = at_step(self.variables, self.all_defs, self.constants, expr, '', index)
		return ret
	
	def add_var(self, name, index, typ):
		self.yi.add_var(VAR_AT_STEP_FMT % (name, index), typ)
		
	
	def add_variables(self, index):
		assert len(self.var_low) == index
		self.var_low.append(len(self.yi.vnames))
		for (i, n) in enumerate(self.ordered_vars):
			t = self.variables[n]
			assert not n.endswith(preproc.PRIME_SUFFIX)
			if i >= self.varcount and not (n + preproc.PRIME_SUFFIX) in self.special_vars:
				# Special variables, basically adding is delayed by one step if they do not appear
				# in primd state; this is necessary to avoid adding unnecessary copies of the delta
				# variable that may cause trouble in getting models
				if index > 0:
					self.add_var(n, index - 1, t)
			else:
				self.add_var(n, index, t)
	
	def add_definitions(self, index):
		for n, expr in self.definitions:
			if n in self.transition_definitions or n.endswith(preproc.PRIME_SUFFIX):
				if index > 0:
					if n in self.transition_definitions:
						ni = VAR_AT_STEP_FMT % (n, index - 1)
					else:
						ni = VAR_AT_STEP_FMT % (n[:-len(preproc.PRIME_SUFFIX)], index)
					if not ni in self.yi.defines:
						self.yi.add_def(ni, self.yi.encode(self.at_step(expr, index-1)))
			else:
				ni = VAR_AT_STEP_FMT % (n, index)
				if not ni in self.yi.defines:
					self.yi.add_def(ni, self.yi.encode(self.at_step(expr, index)))
	
	def assertion(self, asns, index, activation_literal = None, activation_equivalence = False):
		assert isinstance(asns, list)
		assert all(isinstance(x, expressions.Expression) for x in asns)
		for asn in asns:
			enc = self.yi.encode(self.at_step(asn, index))
			if activation_literal == None:
				self.yi.assertion(enc)
			else:
				self.yi.assertion(activation_literal.mk_not().mk_or([enc]))
				if activation_equivalence:
					self.yi.assertion(activation_literal.mk_or([enc.mk_not()]))
	
	def get_counter_example(self, mdl, nontrace):
		dmdl = {}
		for (i, vn) in enumerate(self.yi.vnames):
			dmdl[vn] = mdl[i]
		
		ce = states.CounterExample()
		for (i, low) in enumerate(self.var_low):
			s = states.State(mdl, low, self)
			s.vnames = self.svnames
			if (not nontrace) and self.clockmaxdict:
				if self.INT_FRAC_SPLIT:
					if i == 0:
						vni = VAR_AT_STEP_FMT % (self.clockmaxdict.keys()[0]  + brind.INT_SUFFIX, 0)
						vnf = VAR_AT_STEP_FMT % (self.clockmaxdict.keys()[0]  + brind.FRAC_SUFFIX, 0)
						delta = dmdl[vni] + dmdl[vnf]
					elif i < len(self.var_low) - 1:
						vni = VAR_AT_STEP_FMT % (brind.DELTAVAR_NAME + brind.INT_SUFFIX, i - 1)
						vnf = VAR_AT_STEP_FMT % (brind.DELTAVAR_NAME + brind.FRAC_SUFFIX, i - 1)
						delta = dmdl[vni] + dmdl[vnf]
					else:
						delta = 0
				else:
					if i == 0:
						delta = dmdl[VAR_AT_STEP_FMT % (self.clockmaxdict.keys()[0], 0)]
						assert all(dmdl[VAR_AT_STEP_FMT % (x, 0)] == delta for x in self.clockmaxdict)
					elif i < len(self.var_low) - 1:
						delta = dmdl[VAR_AT_STEP_FMT % (brind.DELTAVAR_NAME, i - 1)]
					else:
						delta = 0
				
				if delta > 0:
					t = copy.copy(s)
					for j in xrange(self.clockcount):
						t[j] -= delta
					ce.append((None, t))
			ce.append((i, s))
		return ce
	
	def check(self, index):
		self.yi.push()
		self.assertion([expressions.AstExpression('!', self.property)], index)
		try:
			if self.yi.check():
				return False, self.get_counter_example(self.yi.get_model(), config.non_trace_counter_example)
			else:
				return True, None
		finally:
			self.yi.pop()
	
	def step(self, index, initial_act = None):
		'Encodes states s_i, ..., s_(i+count-1)'
		self.add_variables(index)
		self.add_definitions(index)
		self.assertion(self.invariants, index)
		if index == 0:
			# Initial constraint
			self.assertion(self.initials, 0, initial_act)
		else:
			# Transition from previous
			self.assertion(self.transitions, index - 1)
	
	def initialize_yices(self):
		self.yi = byices.Yices(config.yicesfile, stats=self.statistics)
		for (i, cnst) in enumerate(self.constants):
			ret = self.yi.add_constant(cnst)
			assert ret == i
	
	def check_emptyness(self, init_act_var=None):
		self.yi.push()
		try:
			if init_act_var != None:
				self.yi.assertion(init_act_var)
			# Initial empty ?
			zero = self.yi.context.mk_num(0)
			for i in xrange(self.clockvarcount):
				self.yi.assertion(self.yi.vars[self.var_low[0] + i].mk_eq(zero))
			return not self.yi.check()
		finally:
			self.yi.pop()
	
	def verify(self):
		assert self.bound > 0
		self.initialize_yices()
		for i in xrange(self.bound):
			self.step(i)
			if i == 0 and self.check_emptyness():
				holds = True
				ce = '(State space is empty)'
				break
			holds, ce = self.check(i)
			if i == 0:
				sys.stdout.write(' ')
			sys.stdout.write('.')
			sys.stdout.flush()
			if not holds:
				break
		k = i + 1
		return holds, k, ce


_LT = -2
_LEQ = -1
_GEQ = 1
_GT = 2
OPERATORS = {
	_LT  : lambda x, y : x.mk_lt(y),
	_LEQ : lambda x, y : x.mk_le(y),
	_GEQ : lambda x, y : x.mk_ge(y),
	_GT  : lambda x, y : x.mk_gt(y) 
}
STRICT_OPS = {
	_LT  : lambda x, y : x.mk_lt(y),
	_LEQ : lambda x, y : x.mk_lt(y),
	_GEQ : lambda x, y : x.mk_gt(y),
	_GT  : lambda x, y : x.mk_gt(y) 
}
def _diag_constr_helper(c_i_int, c_i_frac, c_j_int, op, d_i_int, d_i_frac, d_j_int, const):
	"Returns constraint c^i - c_int^j OP d^i - d_int^j + const"
	assert op in [_LT, _LEQ, _GEQ, _GT]
	# actual constraint:
	# c_int^i - d_int^i strict(op) c_int^j - d_int^j + const OR
	#		(c_int^i - d_int^i = c_int^j - d_int^j + const and c_frac^i op d_frac_i)
	lhs = c_i_int.mk_sub([d_i_int])
	rhs = c_j_int.mk_sub([d_j_int]).mk_sum([const])
	return STRICT_OPS[op](lhs, rhs).mk_or([
			lhs.mk_eq(rhs).mk_and([OPERATORS[op](c_i_frac, d_i_frac)])
		])

class TemporalInduction(BMC):
	COMPLETE = True
	INT_FRAC_SPLIT = True
	def __init__(self, *a):
		BMC.__init__(self, *a)
		self.diseqs = set()
	
	def add_diseq(self, i, j):
		assert i < j
		assert not (i, j) in self.diseqs
#		print self.diseqs, i, j, (i, j)
		if config.verbosity >= VERBOSITY_DISEQ:
			print 'Adding disequality s_%d != s_%d' %  (i, j)
		assert (i, j) not in self.diseqs
		encs = []
		
		### Clocks
		li, lj = self.var_low[i], self.var_low[j]
		zero = self.yi.context.mk_num(0)
		one = self.yi.context.mk_num(1)
		mone = zero.mk_sub([one])
		ismxis =[]
		ismxjs =[]
		for c in xrange(self.clockcount):
			ivi = self.yi.vars[li + 2 * c]
			ivj = self.yi.vars[lj + 2 * c]
			fvi = self.yi.vars[li + 2 * c + 1]
			fvj = self.yi.vars[lj + 2 * c + 1]
			mx = self.yi.context.mk_num(self.clockmax[c])
			ismxi = ivi.mk_gt(mx).mk_or([ivi.mk_eq(mx).mk_and([fvi.mk_gt(zero)])])
			ismxj = ivj.mk_gt(mx).mk_or([ivj.mk_eq(mx).mk_and([fvj.mk_gt(zero)])])
			del mx
			ismxis.append(ismxi)
			ismxjs.append(ismxj)
			if config.basic_regions:
				int_diff = ivi.mk_diseq(ivj) # integral part different
				fzero_diff = fvi.mk_eq(zero).mk_diseq(fvj.mk_eq(zero)) # fractional part zero in one but not both
				encs.append(ismxi.mk_ite(ismxj.mk_not(), int_diff.mk_or([fzero_diff])))
			else:
				#NOT max_c^j AND c_int^i >= c_int^j + 1
				encs.append(ismxj.mk_not().mk_and([ivi.mk_ge(ivj.mk_sum([one]))]))
				
				#NOT max_c^j AND c_frac^j == 0 AND
				#				(
				#					c_int^i > c_int^j
				#					OR
				#					(c_int^i == c_int^j AND c_fract^i > 0)
				#				)
				encs.append(ismxj.mk_not().mk_and([
							fvj.mk_eq(zero),
							ivi.mk_gt(ivj).mk_or([
								ivi.mk_eq(ivj).mk_and([fvi.mk_gt(zero)])
							])
						]))
				
				civi = ivi
				civj = ivj
				cfvi = fvi
				cfvj = fvj
				cismxi = ismxi
				cismxj = ismxj
				del ivi, ivj, fvi, fvj, ismxi, ismxj
				for d in xrange(self.clockcount):
					if c != d:
						divi = self.yi.vars[li + 2 * d]
						divj = self.yi.vars[lj + 2 * d]
						dfvi = self.yi.vars[li + 2 * d + 1]
						dfvj = self.yi.vars[lj + 2 * d + 1]
						dmx = self.yi.context.mk_num(self.clockmax[d])
						dismxi = divi.mk_gt(dmx).mk_or([divi.mk_eq(dmx).mk_and([dfvi.mk_gt(zero)])])
						dismxj = divj.mk_gt(dmx).mk_or([divj.mk_eq(dmx).mk_and([dfvj.mk_gt(zero)])])
					
						if c < d: #only once:
							######## Inner region ########
							# NOT max_c^j AND NOT max_d^j AND (
							encs.append(cismxj.mk_not().mk_and([dismxj.mk_not(), (
					
							###
							# 	c_frac^j < d_frac^j AND
							#		(c^i - c_int^j >= d^i - d_int^j OR c^i - c_int^j <= d^i - d_int^j - 1)
								cfvj.mk_lt(dfvj).mk_and([
										_diag_constr_helper(civi, cfvi, civj, _GEQ, divi, dfvi, divj, zero).mk_or([
										_diag_constr_helper(civi, cfvi, civj, _LEQ, divi, dfvi, divj, mone)
										])
							# OR
									]).mk_or([
					
							###
							# 	c_frac^j > d_frac^j AND
							#		(c^i - c_int^j <= d^i - d_int^j OR c^i - c_int^j >= d^i - d_int^j + 1)
								cfvj.mk_gt(dfvj).mk_and([
										_diag_constr_helper(civi, cfvi, civj, _LEQ, divi, dfvi, divj, zero).mk_or([
										_diag_constr_helper(civi, cfvi, civj, _GEQ, divi, dfvi, divj, one)
										])
							#OR
									]),
					
							###
							# 	c_frac^j == d_frac^j AND
							#		(c^i - c_int^j < d^i - d_int^j OR c^i - c_int^j > d^i - d_int^j)
								cfvj.mk_eq(dfvj).mk_and([
										_diag_constr_helper(civi, cfvi, civj, _LT, divi, dfvi, divj, zero).mk_or([
										_diag_constr_helper(civi, cfvi, civj, _GT, divi, dfvi, divj, zero)
										])
									])])
					
							# )
							)]))
					
						######## Outer region ########
						# NOT max_c^j AND max_d^j AND (
						encs.append(cismxj.mk_not().mk_and([dismxj, (
					
						# c_frac^j > 0 AND c^i - c_int^j >= d^i - m_d + 1
							cfvj.mk_gt(zero).mk_and([
									_diag_constr_helper(civi, cfvi, civj, _GEQ, divi, dfvi, dmx, one)
						# OR
								]).mk_or([
						
						# c_frac^j = 0 AND c^i - c_int^j > d^i - m_d
							cfvj.mk_eq(zero).mk_and([
									_diag_constr_helper(civi, cfvi, civj, _GT, divi, dfvi, dmx, zero)
								])])
						# )
						)]))
		
		if config.basic_regions:
			for k in xrange(self.clockcount): # ordering different ; simple quadratic size encoding
				fvki = self.yi.vars[li + 2 * k + 1]
				fvkj = self.yi.vars[lj + 2 * k + 1]
				ismxki = ismxis[k]
				for l in xrange(self.clockcount):
					if k != l:
						ismxli = ismxis[l]
						fvli = self.yi.vars[li + 2 * l + 1]
						fvlj = self.yi.vars[lj + 2 * l + 1]
						encs.append(ismxki.mk_not().mk_and([ismxli.mk_not(),
												fvki.mk_lt(fvli).mk_diseq(fvkj.mk_lt(fvlj))]))
		
		### Ordinary variables
		for k in xrange(self.clockvarcount, self.varcount):
			nm = self.ordered_vars[k]
			t = self.variables[nm]
			vara = self.yi.get_var(VAR_AT_STEP_FMT % (nm, i))
			varb = self.yi.get_var(VAR_AT_STEP_FMT % (nm, j))
			encs.append(vara.mk_diseq(varb))
		assert encs
		if len(encs) == 1:
			self.yi.assertion(encs[0])
		else:
			self.yi.assertion(encs[0].mk_or(encs[1:]))
		self.diseqs.add((i, j))
#		sys.exit(0)
	
	def add_selected_diseqs(self, index, trace):
		assert index + 1 == len(trace), (index, len(trace))
		cnt = 0
		for i in xrange(len(trace)):
			for j in xrange(i):
				assert j < i
				if trace[j][1].same_region(trace[i][1], config.basic_regions):
					self.add_diseq(j, i)
					cnt += 1
		return cnt
	
	def add_all_diseqs(self, index):
		for j in xrange(index):
			self.add_diseq(j, index)
	
	def verify(self):
		sys.stdout.write(' ')
		sys.stdout.flush()
		self.initialize_yices()
		
		act_init = self.yi.add_var('act-init', expressions.BOOLEAN)
		prop = [self.property]
		for i in itertools.count():
			try:
				self.step(i, act_init) # Takes care of I, T and Invar
				if i == 0 and self.check_emptyness(act_init):
					return True, i+1, '(State space is empty)'
				act_prop = self.yi.add_var('act-%d' % i, expressions.BOOLEAN)
				self.assertion(prop, i, act_prop, True)
				
				if config.all_diseq:
					self.yi.push() # Don't use pushes and pops if dynamically adding disequality contraints as they would get popped later
				
				nprop_ra = self.yi.assertion(act_prop.mk_not(), retractable=not config.all_diseq)
				while True: # Add diseq constraints until no more necessary (if corresponding flag set)
					if not self.yi.check():
						return True, i + 1, None
				
					if not config.all_diseq:
						trace = self.get_counter_example(self.yi.get_model(), True)
						if config.verbosity >= VERBOSITY_TRACES:
							print 'Trace:'
							print trace
							print
						if self.add_selected_diseqs(i, trace) == 0:
							break
					else:
						break
			
				init_ra = self.yi.assertion(act_init, retractable=not config.all_diseq)
				if self.yi.check():
					return False, i + 1, self.get_counter_example(self.yi.get_model(), config.non_trace_counter_example)
				if config.all_diseq:
					self.yi.pop()
				else:
					nprop_ra.retract()
					init_ra.retract()
				
				self.yi.assertion(act_prop)
				if config.all_diseq:
					self.add_all_diseqs(i)
			finally:
				sys.stdout.write('.')
				sys.stdout.flush()

