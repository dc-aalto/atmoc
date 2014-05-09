#!/usr/bin/python -O
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






import config
if __name__ == '__main__':
	config.parse_command_line()

################################################################################
PRINT_SKIPS = False

### Debugging -- by default everything should be False
_DEBUG_DONT_COUNT_CLAUSES      = False
_DEBUG_SKIP_DUPLICATE_CHECKING = False
_DEBUG_DUMP_TRACE              = False
_DEBUG_PROFILE                 = False

### Variable names; Note that meta variable names should contain dashes, as they are not permitted as parts of variable names in the NuSMV format and therefore prevent name collisions
DELTAVAR_NAME = 'delta-'
INT_SUFFIX = '-int'
FRAC_SUFFIX = '-frac'
INCREASE_PREFIX = 'inc-'
DELTA_INT = DELTAVAR_NAME + INT_SUFFIX
DELTA_FRAC = DELTAVAR_NAME + FRAC_SUFFIX

################################################################################
import os, sys, getopt, heapq, copy, random, copy
import preproc, expressions, states, yutil, colors, nusmv_yacc, stats, cseq, yicesfull, interactive, unrolling, nusmv_lex

if _DEBUG_DUMP_TRACE:
	_dbg_tracef = open('_brind_trace', 'w')
	def _dbg_trace(frame, event, arg):
		_dbg_tracef.write('%s, %s:%d\n' % (event, frame.f_code.co_filename, frame.f_lineno))
		_dbg_tracef.flush()
		return _dbg_trace
	sys.settrace(_dbg_trace)

################################################################################
# Error handling

ERR_INVALID_MODEL = 2

class BrindException(Exception):
	'For general exceptions'
	pass

class TerminateException(Exception):
	'Used to indicate an error message should be printed to stderr and then the '\
	'program terminated with an error code'
	def __init__(self, retval, msg):
		self.retval = retval
		self.msg = msg

OP_REVERSE = {
	'<' : '>',
	'<=' : '>=',
	'>' : '<',
	'>=' : '<=',
	'=' : '='
}

@preproc.RewriteExpr(False, False, True)
def split_clock_comparisons(surrounding, expr, prefix, is_def, clocks):
	assert isinstance(expr, expressions.AstExpression)
	assert len(expr) > 1
		
	if len(expr) != 3:
		return None
		
	if isinstance(expr[1], expressions.AstExpression)\
			and len(expr[1]) == 1                     \
			and expr[1][0] in clocks:
		pos = 1
		op = expr[0]
	elif isinstance(expr[2], expressions.AstExpression)\
			and len(expr[2]) == 2                        \
			and expr[2][0] in clocks:
		pos = 2
		op = OP_REVERSE[expr[0]]
	else:
		return None
	
	assert op in OP_REVERSE
	assert isinstance(expr[3 - pos], expressions.Number)
	clk = expr[pos][0]
	const = expr[3 - pos]
	
	if clk.endswith(preproc.PRIME_SUFFIX):
		clb = clk[:-len(preproc.PRIME_SUFFIX)]
		cli = clb + INT_SUFFIX + preproc.PRIME_SUFFIX
		clf = clb + INT_SUFFIX + preproc.PRIME_SUFFIX
	else:
		cli = clk + INT_SUFFIX
		clf = clk + FRAC_SUFFIX
	
	if op == '<':
		return expressions.AstExpression('<', cli, const)
	if op == '<=':
		return expressions.AstExpression('|', ('<', cli, const), ('&', ('=', cli, const), ('=', clf, expressions.ZERO)))
	if op == '>':
		return expressions.AstExpression('|', ('>', cli, const), ('&', ('=', cli, const), ('>', clf, expressions.ZERO)))
	if op == '>=':
		return expressions.AstExpression('>=', cli, const)
	if op == '=':
		return expressions.AstExpression('&', ('=', cli, const), ('=', clf, expressions.ZERO))
	else:
		assert False

################################################################################
############################## Bradley induction ###############################
################################################################################

class BradleyInduction(object):
	#Configuration
	EXCEPTION_TYPE     = BrindException #Used for exceptions
	yices_exec         = False          #Don't use yices as executable
	definitions        = None           # List of (name, expression) pairs in viable inlining order
	
	#Constructor
	def __init__(self, model):
		if config.use_k_ind:
			self.cls = unrolling.TemporalInduction
		elif config.bmc_bound != None:
			self.cls = unrolling.BMC
		else:
			self.cls = cseq.ClauseSequence
		
		self._init(model)
		self._generate_initial()
		self._generate_invar()
		self._generate_transition()
		
		
	def _init(self, model):#, spec_preproc_cb):
		'Initialize members: module, orgspecs, specs, clocks, clockmax, variables, used_types\n'\
		'Checks convexity if required\n'                                                         \
		'spec_preproc_cb should take one specification as an argument, and'                       \
		'preprocess the specification if supported or return None if it is not'                    \
		'supported'
		# Read model
		(self.variables, self.unprimed_vars, self.definition_vars),                         \
				(self.definitions, self.transition_definitions),                             \
				(self.initials, self.xinitials, self.transitions, self.invariants,            \
				self.xinvariants, self.urgencies, self.resets, self.property, self.xproperty), \
				self.orgspecs, self.clockmax =                                                  \
					preproc.preprocess(model, config.type_check, config.def_vars, config.check_property, self.cls.FULL_XINVARIANT, False)
		
		# Allocate constants
		self.constants = []
		for t in self.variables.itervalues():
			if isinstance(t, expressions.Enumeration):
				for v in t.values:
					if not v in self.constants:
						self.constants.append(v)
		
		# Convexity
		if not config.nochecks:
			for invar in self.invariants:
				(conv, mdl) = yutil.is_convex(self.variables, self.constants, self.definitions, invar)
				if not conv:
					raise TerminateException(ERR_INVALID_MODEL, 'Non-convex invariant: %s' % str(invar))
		
		# Split up comparisons
		if self.cls.INT_FRAC_SPLIT: #self.variables, self.unprimed_vars, self.definition_vars
			defnames = set(x[0] for x in self.definitions)
			clocks = set(self.resets)
			clocks.update(x + preproc.PRIME_SUFFIX for x in self.resets)
			for i in xrange(len(self.definitions)):
				dn, expr = self.definitions[i]
				self.definitions[i] = dn, split_clock_comparisons(self.variables, defnames, self.constants, expr, '', clocks)
			
			for lst in [self.initials, self.xinitials, self.transitions, self.invariants, self.xinvariants, self.urgencies]:
				for i in xrange(len(lst)):
					lst[i] = split_clock_comparisons(self.variables, defnames, self.constants, lst[i], '', clocks)
			
			self.property = split_clock_comparisons(self.variables, defnames, self.constants, self.property, '', clocks)
			self.xproperty = split_clock_comparisons(self.variables, defnames, self.constants, self.xproperty, '', clocks)
			
			for clk, expr in self.resets.items():
				self.resets[clk] = split_clock_comparisons(self.variables, defnames, self.constants, expr, '', clocks)
	
	#Generate relations
	def _generate_initial(self):
		if self.resets:
			clks = self.resets.keys()
			if self.cls.INT_FRAC_SPLIT:
				clk0i = clks[0] + INT_SUFFIX
				clk0f = clks[0] + FRAC_SUFFIX
			else:
				clk0 = clks[0]
			for clkname in clks[1:]:
				if self.cls.INT_FRAC_SPLIT:
					self.initials.append(expressions.AstExpression('=',  clkname + INT_SUFFIX,                         clk0i))
					self.initials.append(expressions.AstExpression('=',  clkname + FRAC_SUFFIX,                        clk0f))
					self.xinitials.append(expressions.AstExpression('=', clkname + INT_SUFFIX  + preproc.PRIME_SUFFIX, clk0i))
					self.xinitials.append(expressions.AstExpression('=', clkname + FRAC_SUFFIX + preproc.PRIME_SUFFIX, clk0f))
				else:
					self.initials.append(expressions.AstExpression('=',  clkname,                        clk0))
					self.xinitials.append(expressions.AstExpression('=', clkname + preproc.PRIME_SUFFIX, clk0))
			#NOTE: c >= 0 is already in invariant
	
	def _generate_invar(self):
		if self.resets:
			zero = expressions.Number(0)
			if self.cls.INT_FRAC_SPLIT:
				one = expressions.Number(1)
			for clk in self.resets: #NOTE: we're adding this for making backward search more reasonal
				if self.cls.INT_FRAC_SPLIT:
					clki = clk + INT_SUFFIX
					clkf = clk + FRAC_SUFFIX
					xclki = clk + INT_SUFFIX  + preproc.PRIME_SUFFIX
					xclkf = clk + FRAC_SUFFIX + preproc.PRIME_SUFFIX
					self.invariants.append(expressions.AstExpression('>=',  clki,  zero))
					self.invariants.append(expressions.AstExpression('>=',  clkf,  zero))
					self.invariants.append(expressions.AstExpression('<',   clkf,  one))
					self.xinvariants.append(expressions.AstExpression('>=', xclki, zero))
					self.xinvariants.append(expressions.AstExpression('>=', xclkf, zero))
					self.xinvariants.append(expressions.AstExpression('<',  xclkf, one))
				else:
					self.invariants.append(expressions.AstExpression('>=',  clk,                        zero))
					self.xinvariants.append(expressions.AstExpression('>=', clk + preproc.PRIME_SUFFIX, zero))
	
	def _generate_transition(self):
		if self.resets:
			# Individual elements
			zero = expressions.Number(0)
			if self.cls.INT_FRAC_SPLIT:
				one = expressions.Number(1)
				for clk in self.resets:
					dn = INCREASE_PREFIX + clk
					self.definitions.append((dn, expressions.AstExpression('?:', ('>=', ('+', clk + FRAC_SUFFIX, DELTA_FRAC), one), one, zero)))
					self.transition_definitions.add(dn)
				
				clock_diff_not_reset = []
				clock_diff_reset = []
				
				for (clk, r) in self.resets.iteritems():
					ci = clk + INT_SUFFIX
					xci = clk + INT_SUFFIX + preproc.PRIME_SUFFIX
					cf = clk + FRAC_SUFFIX
					xcf = clk + FRAC_SUFFIX + preproc.PRIME_SUFFIX
					inc = INCREASE_PREFIX + clk
					clock_diff_not_reset.append(expressions.AstExpression('->',
									('!', r),
									('=', xci, ('+', ('+', ci, DELTA_INT), inc))))
					clock_diff_not_reset.append(expressions.AstExpression('->',
									('!', r),
									('=', xcf, ('-', ('+', cf, DELTA_FRAC), inc))))
					clock_diff_reset.append(expressions.AstExpression('->',
									r,
									('=', xci, ('+', DELTA_INT, inc))))
					clock_diff_reset.append(expressions.AstExpression('->',
									r,
									('=', xcf, ('-', DELTA_FRAC, inc))))
				
				urgent_no_delay      = [expressions.AstExpression('->', u, ('=', DELTA_INT,  zero)) for u in self.urgencies] +\
				                       [expressions.AstExpression('->', u, ('=', DELTA_FRAC, zero)) for u in self.urgencies]
				
				delta_pos            = [expressions.AstExpression('>=', DELTA_INT,  zero),
				                        expressions.AstExpression('>=', DELTA_FRAC, zero),
				                        expressions.AstExpression('<', DELTA_FRAC, expressions.Number(1))]
				
			else:
				clock_diff_not_reset = []
				clock_diff_reset = []
				for (clk, r) in self.resets.iteritems():
					clock_diff_not_reset.append(expressions.AstExpression('->', ('!', r), ('=', clk + preproc.PRIME_SUFFIX, ('+', clk, DELTAVAR_NAME))))
					clock_diff_reset.append(    expressions.AstExpression('->', r ,       ('=', clk + preproc.PRIME_SUFFIX, DELTAVAR_NAME)))
				delta_pos            = [expressions.AstExpression('>=', DELTAVAR_NAME, zero)]
				urgent_no_delay      = [expressions.AstExpression('->', u, ('=', DELTAVAR_NAME, zero)) for u in self.urgencies]
						
			# Compose
			self.transitions += clock_diff_not_reset + clock_diff_reset + urgent_no_delay + delta_pos
	
	def verify(self, num, skip):
		global statistics
		assert isinstance(num, (int, long))
				
		if not skip or PRINT_SKIPS:
			print 'Property %d' % num, (colors.bold if skip else colors.bright_blue)(str(self.orgspecs[num][1])),
			if self.orgspecs[num][0]:
				print 'in', self.orgspecs[num][0]
		
		if skip:
			if PRINT_SKIPS:
				print 'was', colors.bold('skipped')
			return None, None
		else:			
			#Actual checking
			variables = {}
			for k, v in self.variables.iteritems():
				if k in self.unprimed_vars and not k in self.clockmax:
					variables[k] = v
			special_vars = {}
			if config.def_vars:
				if config.defs_in_clauses:
					for v in self.definition_vars:
						if not v.endswith(preproc.PRIME_SUFFIX):
							variables[v] = self.variables[v]
				else:
					for v in self.definition_vars:
						special_vars[v] = self.variables[v]
			if self.resets:
				special_vars[DELTAVAR_NAME] = expressions.REAL
			cs = self.cls(variables,
										self.clockmax,
										special_vars,
										self.constants,
										self.initials,
										self.xinitials,
										self.invariants,
										self.xinvariants,
										self.transitions,
										self.property,
										self.xproperty,
										self.definitions,
										self.transition_definitions,
										statistics)
			statistics.set_cs(cs)
			holds, k, counter = cs.verify()
			statistics.holds = holds
			statistics.k = k
		
			if not holds:
				statistics.ce_length = sum(1 for x in counter if x[0] != None)
				assert isinstance(counter, states.CounterExample)
				printinfo = '\n' + counter.string('\t', config.short_states)
			else:
				printinfo = counter
			
			sys.stdout.write(' ')
			if holds:
				if self.cls.COMPLETE:
					sys.stdout.write(colors.green('holds'))
				else:
					sys.stdout.write(colors.yellow('maybe holds'))
			else:
				sys.stdout.write(colors.red('does not hold'))
			if printinfo == None:
				print
			else:
				print ' %s' % printinfo
			return holds, k
	
	def interactive(self):
		inter = interactive.Interactor(self.variables,
										self.clockmax,
										nonprimed(self.init, self.prime_constants),
										nonprimed(self.trans, self.prime_constants),
										nonprimed(self.invar, self.prime_constants))
		inter.run()
	
	def speccount(self):
		return len(self.orgspecs)

	def list_specs(self, colored = False):
		for i in xrange(len(self.orgspecs)):
			if self.orgspecs[i][0]:
				print '%-8d %s in %s' % (i, str(self.orgspecs[i][1]), self.orgspecs[i][0])
			else:
				print '%-8d %s' % (i, str(self.orgspecs[i][1]))
			if self.orgspecs[i] == None:
				strn = '         (not supported)'
				if colored:
					print colors.red(strn)
				else:
					print strn
		sys.exit(0)
		
	def count_specs(self, colored = False):
		print len(self.orgspecs)
		sys.exit(0)

def model_check():
	global statistics
	
	try:
		
		# Model
		statistics = stats.BrindStats()
	
		# Parse file
		inf = open(config.filename, 'r')
		model = nusmv_yacc.parser.parse(inf.read())
		inf.close()
	
		# Actual Checking
		if config.show_stats and (not config.count_properties) and (not config.list_properties):
			print 'Version:', config.VERSION
			print 'File:', config.filename
			print 'Verification starting at', statistics.start
			print 'Using yices version', yicesfull.get_version()
		
		try:
			b = BradleyInduction(model)
			
			if config.list_properties:
				b.list_specs()
			elif config.count_properties:
				b.count_specs()
			elif config.interactive:
				b.interactive()
			else:
				for i in xrange(b.speccount()):
					skip = (not config.check_property in [None, i]) 
					holds, rbound = b.verify(i, skip)
			if config.show_stats:
				print statistics
		finally:
			statistics.write_tr(config.table_row_file)
	except Exception, e:
		if isinstance(e, TerminateException):
			sys.stdout.write('\n')
			sys.stderr.write('ERROR: ')
			sys.stderr.write(e.msg)
			sys.stderr.write('\n')
			sys.exit(e.retval)
		elif isinstance(e, (preproc.PreprocessingException, preproc.TypeException, nusmv_lex.ParsingException)):
			sys.stdout.write('\n')
			sys.stderr.write('ERROR: ')
			sys.stderr.write(str(e))
			sys.stderr.write('\n')
			sys.exit(ERR_INVALID_MODEL)
		else:
			print
			print '!!!', 'SEED', config.seed, '!!!'
			raise

def main():
	if _DEBUG_PROFILE:
		import cProfile
		cProfile.run('model_check()', 'brind_profile')
	else:
		model_check()

if __name__ == '__main__':
	main()

