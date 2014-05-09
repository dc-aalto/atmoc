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





import sys, fractions, copy, random, heapq
import expressions, config, byices, stats, states, preproc
from brind import DELTAVAR_NAME

################################################################################
# Constants

PROOF_FILE_VERSION = 1

# Variable names
ACTIVATION_PREFIX = 'act-'

ACTVAR_TRANS = '%sT' % ACTIVATION_PREFIX
ACTVAR_FMT = '%s%%d' % ACTIVATION_PREFIX
ACTVAR_XNOTPROP = '%sxNP' % ACTIVATION_PREFIX
ACTVAR_XINIT = '%sxinit' % ACTIVATION_PREFIX

# Verbosity
VERBOSITY_CLAUSES = 1 # Level at which added clauses are printed
VERBOSITY_PROPAGATION = 1
VERBOSITY_RESTART = 1
VERBOSITY_CLAUSE_DUMP = 1
VERBOSITY_SUM_UP_CLAUSES = 2
VERBOSITY_STATES  = 2 # Level at which information about excluded states is printed
VERBOSITY_GETTING_RID_CHECKS = 3
VERBOSITY_MAINLOOP_CHECKS = 3
VERBOSITY_MARKER_VARIABLES_IN_YICES = 5 #NOTE THAT THIS AFFECTS THE MODELS RETURNED BY YICES
VERBOSITY_DOWN    = 4
VERBOSITY_SOLVE_REL = 4


################################################################################
class Obligation(object):                                                      #
	def __init__(self, state, index, clause_num, parent):                      #
		assert isinstance(state, states.State)
		assert isinstance(index, (int, long))
		assert isinstance(clause_num, (int, long))
		assert parent == None or isinstance(parent, Obligation)
		self.state = state
		self.index = index
		self.parent = parent
		self.clause = state.literals()
		self.clause_num = clause_num
	
	def __lt__(self, other):
		assert isinstance(other, Obligation)
		return self.index < other.index
	
	def __le__(self, other):
		assert isinstance(other, Obligation)
		return self.index <= other.index
	
	def __gt__(self, other):
		assert isinstance(other, Obligation)
		return self.index > other.index
	
	def __ge__(self, other):
		assert isinstance(other, Obligation)
		return self.index >= other.index
	
	def get_counter_example(self):
		ret = states.CounterExample()
		cur = self
		num = 0
		while cur != None:
			ret.append((num, cur.state))
			cur = cur.parent
			num += 1
		return ret

################################################################################
class ClauseSequence(object):                                                  #
	#########################                                                  #
	### Options
	FULL_XINVARIANT = False
	COMPLETE = True
	INT_FRAC_SPLIT = False
	
	### Relations
	prop = None       # The property (Expression)
	xprop = None      # Primed property
	init = None       # Initial constraint
	trans = None      # Transition relation
	invar = None      # Invariant
	xinit = None      # Primed initial constraint
	
	### Activation literals
	act = None        # List of activation literals for F_i
	act_trans = None  # Transition relation activation literal
	act_xnp   = None  # next not property
	act_xinit = None  # next init
	
	### Variables and clocks
	variables = None   # List of variables; first clocks then non-clock variables
	additional_variables = None # List of variables that are not treated as actual variables (i.e. not included in the clauses)
	clockmax = None   # List of clock maximums
	diffmax = None    # clock pair -> difference, pairs in both orders (list of lists)
	
	### For remembering which variable ids correspond to the state variables of the system
	clockcount = None # Nummber of clocks
	varcount = None   # Total number of variables including clocks
	
	### Clauses
	clauses = None    # $F_i$s, list of sets of clauses, clauses[i] contains all
	                  # clauses that are in F_i __but not F_{i-+}__
	at_clauses = None # i of the F_i corresponding to the current assertions
	clauses_chronological = None # List of clauses in the order of them being added. Used for syntactic is_blocked checking
	                  # Reset for each time get_rid_of is executed
	
	### Yices
	yi = None         # Main yices object for most assertions
	yi_cnt = 0        # Number of yices contexts used so far
	yi_prev_pops = 0  # Number of pops attributed to previous yices contexts
	
	### Debugging / stats
	cnt_subsumption_drop = 0 # Number of clause drops based on subsumption
	cnt_rediscovered = 0     # Number of clauses rediscovered
	marks = 0         #Number of marking variables
	prooff = None
	clauses_in_prooff = 0
	
	#########################
	def __init__(self, variables, clockmax, def_var_names, constants, init, xinit, invar, xinvar,
		                 trans, spec, xspec, definitions, transition_defitions, statistics):
		assert isinstance(variables, dict)
		assert all(isinstance(x, basestring) for x in variables)
		assert not any(x.endswith(preproc.PRIME_SUFFIX) for x in variables)
		assert all(isinstance(x, expressions.Type) for x in variables.itervalues())
		assert isinstance(clockmax, dict)
		assert all(isinstance(x, basestring) for x in clockmax.keys())
		assert all(isinstance(x, (int, long, fractions.Fraction)) for x in clockmax.values())
		assert not set(clockmax).intersection(set(variables))
		assert isinstance(constants, list)
		assert all(isinstance(c, basestring) for c in constants)
		assert isinstance(init, list)
		assert all(isinstance(x, expressions.Expression) for x in init)
		assert isinstance(xinit, list)
		assert all(isinstance(x, expressions.Expression) for x in xinit)
		assert isinstance(invar, list)
		assert all(isinstance(x, expressions.Expression) for x in invar)
		assert isinstance(xinvar, list)
		assert all(isinstance(x, expressions.Expression) for x in xinvar)
		assert isinstance(trans, list)
		assert all(isinstance(x, expressions.Expression) for x in trans)
		assert isinstance(spec, expressions.Expression)
		assert isinstance(xspec, expressions.Expression)
		assert isinstance(definitions, list)
		assert all(isinstance(x, tuple) and len(x) == 2 for x in definitions)
		assert all(isinstance(x[0], basestring) for x in definitions)
		assert all(isinstance(x[1], expressions.Expression) for x in definitions)
		assert isinstance(statistics, stats.BrindStats)
		
		self.yi = None
		self.yi_cnt = 0
		self.yi_prev_pops = 0
		
		# Clocks and variables
		self.variables = [] #Soon to be filled
		self.clockmax = []
		self.def_var_names = def_var_names
		self.constants = constants
		
		# Relations
		self.prop        = spec
		self.xprop       = xspec
		self.init        = init
		self.trans       = trans + xinvar #Current state invariant stays asserted
		self.invar       = invar
		self.definitions = definitions
		self.xinit       = xinit + xinvar #Stays pushed unprimed
		
		# Statistics
		self.statistics = statistics
		
		# Variables
		self.additional_variables = def_var_names.items()
		for clk in sorted(clockmax):
			self.variables.append((clk, expressions.REAL))
			self.clockmax.append(clockmax[clk])
		self.clockcount = len(self.variables)
		assert len(self.clockmax) == self.clockcount
		
		assert not any(x == expressions.REAL for x in variables.iterkeys())
		
		for name in sorted(variables):
			self.variables.append((name, variables[name]))
		self.varcount = len(self.variables)
		
		#print len(self.variables), len(self.clockmax),
	
	def print_clauses(self):
		print '#### Clauses:'
		for j in xrange(len(self.clauses)):
			print 'F_%d:' % j,
			print '; '.join(map(str, self.clauses[j]))
		print
	
	def proof_init(self):
		if self.prooff != None:
			def wrexpr(descr, expr):
				self.prooff.write(descr)
				self.prooff.write('\n')
				if isinstance(expr, expressions.Expression):
					self.prooff.write(str(expr).replace('\n', ' '))
					self.prooff.write('\n')
				else:
					assert isinstance(expr, list)
					assert all(isinstance(x, expressions.Expression) for x in expr)
					self.prooff.write(str(len(expr)))
					self.prooff.write('\n')
					for ex in expr:
						self.prooff.write(str(ex).replace('\n', ' '))
						self.prooff.write('\n')
					self.prooff.write('\n')
			self.prooff.write('brind proof version %d\n' % PROOF_FILE_VERSION)
			self.prooff.write('DETAIL %d\n' % config.proof_detail)
			self.prooff.write('++ SYSTEM ++\n')
			self.prooff.write('VARIABLES\n')
			varstrns = []
			for name, tp in self.variables + self.additional_variables:
				if tp == expressions.BOOLEAN:
					tstrn = 'BOOLEAN'
				elif isinstance(tp, expressions.Range):
					tstrn = 'RANGE\n%d\n%d' % (tp.low, tp.high)
				elif tp == expressions.REAL:
					tstrn = 'REAL'
				elif isinstance(tp, expressions.Enumeration):
					tstrn = 'ENUMERATION\n%d' % len(tp.values)
					for val in tp.values:
						tstrn += '\n' + val
				else:
					raise Exception('Unsupported type: %s' % str(tp))
				varstrns.append((tstrn, name))
				varstrns.append((tstrn, name + preproc.PRIME_SUFFIX))
			if self.clockmax:
				varstrns.append(('BOOLEAN', DELTAVAR_NAME))
			
			self.prooff.write(str(len(varstrns)))
			self.prooff.write('\n')
			for vs in varstrns:
				self.prooff.write('%s\n%s\n' % vs)
			self.prooff.write('\n')
			
			self.prooff.write('DEFINITIONS\n')
			if self.definitions != None:
				self.prooff.write(str(len(self.definitions)))
				self.prooff.write('\n')
				for name, expr in self.definitions:
					wrexpr(name, expr)
				self.prooff.write('\n')
			else:
				self.prooff.write('0\n\n')
			
			self.prooff.write('CONSTANTS\n')
			self.prooff.write('%d\n' % len(self.constants))
			for c in self.constants:
				self.prooff.write(c)
				self.prooff.write('\n')
			self.prooff.write('\n')
			
			wrexpr('INIT', self.init)
			wrexpr('INVAR', self.invar)
			wrexpr('TRANS', self.trans)
			wrexpr('PROP', self.prop)
			wrexpr('XPROP', self.xprop)
			self.prooff.write('\n')
			self.prooff.flush()
	
	def proof_update(self, occasion, counterexample=None):
		assert counterexample == None or isinstance(counterexample, states.CounterExample), (counterexample, type(counterexample))
		if self.prooff != None:
			def _dmp_cls_st(st):
				self.prooff.write(str(len(st)))
				self.prooff.write('\n')
				for cls in st:
					self.prooff.write(cls.string(False).replace('\n', ' ').replace('\r', ' '))
					self.prooff.write('\n')
		
			if config.proof_detail >= occasion:
				assert occasion == config.PROOF_DETAIL_FINAL or counterexample == None
				if counterexample != None:
					counterexample = copy.deepcopy(counterexample)
					counterexample.make_feasible(self)
					counterexample = [x for x in counterexample if x[0] != None]
					self.prooff.write('++ COUNTER EXAMPLE ++\n')
					self.prooff.write(str(len(counterexample)))
					self.prooff.write('\n')
					i = 0
					for st in counterexample:
						self.prooff.write(st[1].string(False))
						self.prooff.write('\n')
						i += 1
					self.prooff.write('\n')
				elif occasion == config.PROOF_DETAIL_FINAL:
					self.prooff.write('++ PROOF ++\n')
					for i in xrange(1, len(self.clauses) - 1): # Search for empty set
						if not self.clauses[i]:
							break
					else:
						assert False
					_dmp_cls_st(reduce(list.__add__, self.clauses[i+1:]) + [self.prop])
				elif occasion == config.PROOF_DETAIL_K or occasion == config.PROOF_DETAIL_CLAUSE:
					self.clauses_in_prooff += 1
					if config.verbosity >= VERBOSITY_CLAUSE_DUMP:
						print '@ clause set %d' % self.clauses_in_prooff
					if occasion == config.PROOF_DETAIL_K:
						self.prooff.write('++ CLAUSES %d K ++\n' % self.clauses_in_prooff)
					else:
						self.prooff.write('++ CLAUSES %d ++\n' % self.clauses_in_prooff)
					self.prooff.write('CLAUSE SET COUNT\n')
					self.prooff.write(str(len(self.clauses)))
					self.prooff.write('\n')
					for (i, cls) in enumerate(self.clauses):
						self.prooff.write('SET %d\n' % i)
						_dmp_cls_st(self.clauses[i])
					self.prooff.write('\n')
				else:
					assert False
	
	def add_clause(self, clause, clind, based_on = None, subsumption_checked_up_to=None, dont_dump=False):
		assert isinstance(clause, states.Clause)
		assert clause
		assert clind > 0
		assert based_on == None or isinstance(based_on, states.State)
		if subsumption_checked_up_to == None:
			subsumption_checked_up_to = 0
		
		self.mark_y('add-clause')
		
		if config.verbosity >= VERBOSITY_CLAUSES:
			print '%sdding clause' % ('A' if based_on == None else \
					'Based on %s a' % (based_on.short_str() if config.short_states else str(based_on))), clause, 'to F_%d' % clind
		
		for i in xrange(subsumption_checked_up_to + 1, clind+1):
			for j in xrange(len(self.clauses[i])):
				if clause.subsumes(self.clauses[i][j]):
					if config.verbosity >= VERBOSITY_CLAUSES:
						print '    Dropping from', i, ':', self.clauses[i][j]
					if clause == self.clauses[i][j]:
						self.cnt_rediscovered += 1
					else:
						self.cnt_subsumption_drop += 1
					self.clauses[i][j] = None
			self.clauses[i] = [x for x in self.clauses[i] if x != None]
		assert all(not None in cs for cs in self.clauses)
		
		self.to_clauses(None)
		assert self.yi.poplevel() == 0
		
		self.yi.assert_clause(clause, True, False, self.act[clind])
		self.clauses[clind].append(clause)
		
		if self.clauses_chronological != None:
			self.clauses_chronological.append((clind, clause))
		
		if config.check_alot:
			self.yi.check(stats.CHECK_TYPE_OPTIMIZATION)
		
		if not dont_dump:
			self.proof_update(config.PROOF_DETAIL_CLAUSE)
	
	def lic(self, clind, clause, may_drop, first):
		'Performs the LIC algorithm, returns new clause; may_drop sets if successful, otherwise None'
		assert self.yi.poplevel() == 0
		assert not clause.empty()
		
		if config.verbosity >= VERBOSITY_DOWN:
			print 'LIC', clause
		
		may_drop = copy.copy(may_drop)
		while True:
			#Initiation
			if (not first):
				self.mark_y('LIC-initiation')
				self.to_clauses(0) #I and invar and P
				assert self.yi.poplevel() == 1
				
				self.yi.assert_clause(clause, False, False)
				
				ret = self.yi.check(stats.CHECK_TYPE_INITIATION)
				assert not (first and ret)
				
				if config.verbosity >= VERBOSITY_DOWN:
					print 'Initiation %ssatisfied' % ('not ' if ret else ''), clause				
				self.to_clauses(None)
				assert self.yi.poplevel() == 0
				
				if ret:
					#Initiation violated; Failure
					return None, None
			
			assert self.yi.poplevel() == 0
			
			#Consecution
			if (not first):
				self.mark_y('LIC-consecution')
				
				rc, ri, rm = self.solve_relative(clause, clind, extract_model=True, drop_candidates=may_drop)
				assert not (first and rc == None)
				if rc != None: # consec holds; return clause
					assert rm == None
					clause = rc
					if config.verbosity >= VERBOSITY_DOWN:
						print 'Consecution satisfied, returning', clause
					break
				else: #consec does not hold; retain literals not satisfied by counterexample
					assert rm != None, (rc, ri, rm)
					s = states.State(rm, False, self)
					clause.drop_lits_satisfied_by(s)
					
					if config.verbosity >= VERBOSITY_DOWN:
						print 'Consecution violated:', s
						print 'State', s, '->', clause

					if clause.empty():
						return None, None
					
					continue
			else:
				break
		
		# Update may_drop and return
		may_drop = [x for x in may_drop if clause[x] != None]
		return clause, may_drop
	
	def add_generalization(self, clause, clind, based_on):
		assert isinstance(clause, states.Clause)
		assert clause
		
		# Generalize
		may_drop = [x for x in xrange(len(clause)) if clause.may_drop[x]]
		
		first = True
		if config.verbosity >= VERBOSITY_DOWN:
			print
			print '#######'
			print '# DOWN', clause #', '.join(x.string(True) for x in lits)
			print
		failures = 0
		while True:
			### LIC
			rc, rmd = self.lic(clind, clause, may_drop, first)
			assert not (first and rc == None)
			if rc == None:
				clause = worked
				failures += 1
			else:
				assert rmd != None
				clause = rc
				may_drop = rmd
			
			first = False
			
			### DROP
			if len(may_drop) == 1 and clause.litcnt() == 1: # Don't drop the last literal; First check prevents execution of second
				may_drop = []
			
			if not may_drop or failures >= config.max_drop_lit_failures:
				if config.verbosity >= VERBOSITY_DOWN:
					print ('Drop failure threshold of %d has been reached' % config.max_drop_lit_failures) \
																	if may_drop else 'Nothing more to drop -->',
					print clause
				break #Now lits minimal / stop trying
			else:
				dind = random.randint(0, len(may_drop) - 1)
				dlitind = may_drop[dind]
				
				may_drop[dind:dind+1] = [] # Don't drop again
				worked = clause
				clause = copy.copy(clause)
				clause[dlitind] = None
				
				if config.verbosity >= VERBOSITY_DOWN:
					print
					print 'Dropping literal', dlitind, '->', clause
			
			if config.verbosity >= VERBOSITY_DOWN:
				print
		
		if config.verbosity >= VERBOSITY_DOWN:
			print
			print 'Final clause:', clause
			print
		
		clause.drop_nones()
		self.add_clause(clause, clind, based_on)
	
	def to_clauses(self, clind):
		'Returns a list of retractable assertions if the actiavation literals '\
		'are asserted retractably and None otherwise. Note that the list may '\
		'even be returned if the retractable is False, due to the same clause '\
		'index having been asserted retractably before\n'\
		'NOTE: May create a new yices context and thus invalidate anything '\
		'encoded!!!!'
		assert clind == None or (isinstance(clind, (int, long)) and clind >= 0)
		assert (self.at_clauses == None and self.yi.poplevel() == 0) or (self.at_clauses >= 0 and self.yi.poplevel() == 1)
		
		if clind != self.at_clauses:
			if clind != None and clind < self.at_clauses:
				#Quick
				if config.actvar_impl:
					self.yi.assertion(self.act[clind])
				else:
					if clind == 0:
						self.yi.assertion(self.act[0])
					else:
						for i in xrange(clind, self.at_clauses):
							self.yi.assertion(self.act[i])
				self.at_clauses = clind
			else:
				if self.at_clauses != None:
					assert self.yi.poplevel() == 1
					self.yi.pop()
			
				assert self.yi.poplevel() == 0
			
				# Restarts
				if self.statistics.ypops - self.yi_prev_pops >= config.restart_ratio * len(self.yi.vars):
					self.fresh_context()
				
				# Assertions
				if clind != None:
					self.yi.push()
					if config.actvar_impl:
						self.yi.assertion(self.act[clind])
					else:
						for i in xrange(clind, len(self.act)):
							self.yi.assertion(self.act[i])
			self.at_clauses = clind
		assert (self.at_clauses == None and self.yi.poplevel() == 0) or (self.at_clauses >= 0 and self.yi.poplevel() == 1)
	
	def solve_relative(self, clause, index, extract_model=False, no_ind=False, drop_candidates=None):
		'Return (new clause, new index, model); the index and clause are None if '
		'SAT while the model is None if UNSAT or True if SAT but extract_model is False\n'
		'\n'
		'drop_candidates is a list of indices of literals that are considered for '
		'(near) future dropping. Indices may be dropped from drop_candidates in '
		'case dropping them would be unsuccessful. '
		'\n'
		'Note that the returned clause may return None elements'
		assert isinstance(clause, states.Clause)
		assert isinstance(index, (int, long))
		assert isinstance(extract_model, bool)
		assert isinstance(no_ind, bool)
		assert drop_candidates == None or all(isinstance(x, (int, long)) for x in drop_candidates)
		assert drop_candidates == None or len(drop_candidates) == len(set(drop_candidates)) # No double elements
		
		# Output
		self.mark_y('solve-rel-%d' % index)
		if config.verbosity >= VERBOSITY_SOLVE_REL:
			print '#####'
			print '# Solve relative', index, clause
		
		self.to_clauses(None)
		
		# Prep
		if clause.may_drop == None:
			clause.may_drop = [True] * len(clause)
		
		# Consecution
		self.yi.push() # vvvvvvvvvvvvvvv X
		lits = clause.encode_lits(self.yi, False, True, [])
		ids = [(self.yi.assertion(lit, retractable=True) if lit != None else lit) for lit in lits]
		
		self.yi.push() # vvvvvvvvvvvvvvv A
		act_ras = [None] * len(self.act) # "to_clauses(index -1)
		for i in xrange(index-1, len(self.act)):
			act_ras[i] = self.yi.assertion(self.act[i], retractable=True)
		
		#c
		if not no_ind:
			self.yi.assert_clause(clause, True, False)
		
		#not c'
		assert isinstance(ids, list)
		assert len(ids) == len(clause)
		
		#T
		self.yi.assertion(self.act_trans)
		
		ret = self.yi.check(stats.CHECK_TYPE_CONSECUTION)
		
		if ret: ### Consec does not hold
			if extract_model:
				m = self.yi.get_model()
				assert m != None
			else:
				m = True
			self.yi.pop() # ^^^^^^^^^^^^^^^^ A(1)
			self.yi.pop() # ^^^^^^^^^^^^^^^^ X
			return (None, None, m)
		else: ### Consec holds
			usc = self.yi.unsat_core()
			maybe = [] #indices of literals
		
			# Identify droppable literals from unsat core
			if config.verbosity >= VERBOSITY_SOLVE_REL:
				print 'Potentially droppable literals:',
			for i in xrange(len(clause)):
				if clause[i] != None and clause.may_drop[i] and not ids[i] in usc:
					if config.verbosity >= VERBOSITY_SOLVE_REL:
						print i,
					maybe.append(i)
			random.shuffle(maybe)
			
			if config.verbosity >= VERBOSITY_SOLVE_REL:
				print
		
			# Identify index
			for i in xrange(index-1, len(self.clauses)-1):
				if act_ras[i] in usc:
					break
			assert i >= index-1
			assert i < len(self.clauses)
			if config.verbosity >= VERBOSITY_SOLVE_REL:
				print 'Index:', index, '->', i+1
			index = i+1
			if index >= len(self.clauses): # F_inf
				sys.stdout.flush()
				index = len(self.clauses) - 1
			
			self.yi.pop() # ^^^^^^^^^^^^^^^^ A (2)
			if config.verbosity >= VERBOSITY_SOLVE_REL:
				print 'Actually dropped (permitted by initiation):',
			self.yi.assertion(self.act_xinit) # Initiation
			clause = copy.copy(clause)
			
			while maybe:
				if len(maybe) == 1 and clause.litcnt() == 1: # Avoid dropping last literal
					break
				
				# Take out
				litind = maybe.pop()
				lit = clause[litind]
				clause[litind] = None
				ids[litind].retract()
				
				assert self.yi.poplevel() == 1
				
				ret = self.yi.check(stats.CHECK_TYPE_INITIATION)
			
				if config.verbosity >= VERBOSITY_SOLVE_REL and not ret:
					print litind,
				if ret:
					clause[litind] = lit # put it back
					if drop_candidates != None and litind in drop_candidates:
						drop_candidates.remove(litind)
					ids[litind] = self.yi.assertion(lits[litind], retractable=True)
					clause.may_drop[litind] = False
				
				assert self.yi.poplevel() == 1
			if config.verbosity >= VERBOSITY_SOLVE_REL:
				print '\nRemaining:', clause #Clause(retain)
				print
			
			self.yi.pop() # ^^^^^^^^^^^^^^^^ X
			
			return (clause, index, None)
	
	def get_rid_of(self, state, index, bad_state):
		'Roughly corresponds to "pushGeneralization"'
		assert isinstance(state, states.State)
		assert isinstance(index, (int, long))
		
		self.clauses_chronological = []
		
		try:
			if config.verbosity >= VERBOSITY_STATES:
				print
				print '#' * 80
				print '#' * 4, 'New series', '#' * (80 - 2 - len('New series') - 4)
				print '#' * 80
				print
				print
		
			heap = []
			next = Obligation(state, index, len(self.clauses_chronological), \
								Obligation(bad_state, index+1, len(self.clauses_chronological), None))
			while heap or next != None:
				#One iteration roughly corresponds to 'Inductively generalize'
				if next == None:
					cur = heapq.heappop(heap)
					
					assert cur.index < len(self.clauses)
					for i in xrange(cur.clause_num, len(self.clauses_chronological)):
						clind, cl = self.clauses_chronological[i]
						if clind >= cur.index and cl.subsumes(cur.clause):
							cur.index = clind + 1
							if cur.index >= len(self.clauses):
								break
					if cur.index >= len(self.clauses):
						continue
				
					if config.avoid_drops:
						# SAT check for blocked (at least Een does this too)
						self.to_clauses(len(self.clauses) - 1)
						self.yi.assert_clause(cur.clause, False, False)
						psbl = self.yi.check()
						assert psbl != None
						self.to_clauses(None)
						if not psbl:
							continue
				else:
					cur = next
					next = None
			
				#Verbose output
				if config.verbosity >= VERBOSITY_STATES:
					print '#' * 80
					print '# %d: Trying to get rid of %s' % (cur.index, cur.state.short_str() if config.short_states else str(cur.state))
			
				#Counter example found?
				if cur.index == 0:
					counter = cur.get_counter_example()
					return counter
			
				#### Otherwise, see how far we can get rid of the trouble state
				previndex = cur.index #To see whether we pushed
				index = cur.index
			
				self.mark_y('push-')
			
				#Push as far as possible
				clause = copy.copy(cur.clause)
				while True:
					nc, index, model = self.solve_relative(clause, index, extract_model=True)
					if model != None:
						assert index == None
						break
					else:
						assert index != None
						clause = nc
						index += 1
						cur.index = index # this deviates from Een -- but Een should be wrong
						if index >= len(self.clauses):
							break
				del index
			
				# Add generalization
				if cur.index > previndex:
					if config.verbosity >= VERBOSITY_STATES:
						print 'Pushed', previndex, '->', cur.index
					self.add_generalization(clause, cur.index - 1, cur.state)
				elif config.verbosity >= VERBOSITY_STATES:
					print 'No success in pushing'
			
				assert (model == None) == (cur.index == len(self.clauses)), (cur.index, len(self.clauses), model)
			
				# Enqueue obligations
				if not (cur.index > previndex):
					assert model != None
					s = states.State(model, False, self)
					if config.verbosity >= VERBOSITY_STATES:
						print 'Queuing at %d: %s' % (cur.index - 1, s.short_str() if config.short_states else str(s))
					next = Obligation(s, cur.index - 1, len(self.clauses_chronological), cur)
			
				if not (cur.index >= len(self.clauses)):
					if config.verbosity >= VERBOSITY_STATES:
						print 'Queuing at %d: %s' % (cur.index, cur.state.short_str() if config.short_states else str(cur.state))
					heapq.heappush(heap, cur)
			
				if config.verbosity >= VERBOSITY_STATES:
					print '#' * 80
					print
		
			return None
		finally:
			self.clauses_chronological = None
	
	def mark_y(self, strn, fmt=tuple()):
		if config.verbosity >= VERBOSITY_MARKER_VARIABLES_IN_YICES:
			self.yi.add_var('_' * 20 + (strn % fmt) + ('-%d' % self.marks), expressions.BOOLEAN)
			self.marks += 1
	
	def increase_k(self, restarting):
		#Add one clause set
		self.to_clauses(None)
		assert self.yi.poplevel() == 0
		clind = len(self.act)
		self.act.append(self.yi.add_var(ACTVAR_FMT % clind, expressions.BOOLEAN))
		if config.actvar_impl and len(self.act) > -1:
			self.yi.assertion(self.act[-2].mk_not().mk_or([self.act[-1]]))
		
		if restarting:
			for cl in self.clauses[clind]:
				self.yi.assert_clause(cl, True, False, self.act[clind])
		else:
			self.clauses.append([])
			assert len(self.clauses) == len(self.act)
			if config.verbosity >= config.VERBOSITY_ANY:
				print '\n', '*'*35, 'k = ', len(self.clauses), '*'*35,
	
	def propagate(self):
		'Returns True if done, False otherwise'
		if config.verbosity >= VERBOSITY_PROPAGATION:
			print
			print '#### Propagation'
		
		assert all(not None in cs for cs in self.clauses)				
		self.mark_y('propagation')
		for i in xrange(1, len(self.clauses) - 1):
			if config.verbosity >= VERBOSITY_PROPAGATION:
				print 'Pushed %d ->:' % i
			newclauses = []
			
			move = []
			if config.simple_propagation:
				self.to_clauses(i)
				self.yi.assertion(self.act_trans)
				for c in self.clauses[i]:
					self.yi.push()
					self.yi.assert_clause(c, False, True)
					if self.yi.check(stats.CHECK_TYPE_CONSECUTION):
						newclauses.append(c)
					else:
						move.append((i + 1, c))
					self.yi.pop()
				self.to_clauses(None)
			else:
				for c in self.clauses[i]:
					clause, index, _ = self.solve_relative(c, i+1, no_ind=True)
					if clause != None:
						assert index > i
						if config.verbosity >= VERBOSITY_PROPAGATION:
							print '  -> %d:' % index, clause
						pushed = True
						clause.drop_nones()
						move.append((index, clause))
					else:
						newclauses.append(c)
			if config.verbosity >= VERBOSITY_PROPAGATION and not move:
				print '-- nothing --'
			
			self.clauses[i] = newclauses
			
			for (index, clause) in move:
				self.add_clause(clause, index, subsumption_checked_up_to=index-1, dont_dump=True)
			
			self.proof_update(config.PROOF_DETAIL_CLAUSE)
			if not self.clauses[i]:
				return True
			
		if config.verbosity >= VERBOSITY_PROPAGATION:
			print '\n'
		
		return False
	
	def fresh_context(self):
		if config.verbosity >= VERBOSITY_RESTART:
			print '\n/////////////////////////// Fresh yices context %d \\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\n'\
						% (self.yi_cnt + 1)
		
		#Yices file
		oldyi = self.yi
		yfn = config.yicesfile
		if yfn != None:
			if '.' in yfn:
				dotind = yfn.rindex('.')
				yfn = '%s-%d%s' % (yfn[:dotind], self.yi_cnt + 1, yfn[dotind:])
			else:
				yfn = '%s-%d' % (yfn, self.yi_cnt + 1)
		
		# New context
		self.yi = byices.Yices(yfn, stats=self.statistics)
		
		# Update stats
		if oldyi != None:
			self.yi_prev_pops = self.statistics.ypops
		del oldyi
		
		# Constants
		for c in self.constants:
			ret = self.yi.add_constant(c)
			assert ret == self.constants.index(c)
		
		# Variables
		assert len(self.yi.vars) == 0
		for v, t in self.variables:
			self.yi.add_var(v, t)
		for v, t in self.variables:
			self.yi.add_var(v + preproc.PRIME_SUFFIX, t)
		assert len(self.yi.vars) == len(self.variables) * 2
		
		for name, typ in self.additional_variables:
			self.yi.add_var(name, typ)
		
		# Activation variables
		self.act       = [self.yi.add_var(ACTVAR_FMT % 0,  expressions.BOOLEAN)]
		self.act_trans =  self.yi.add_var(ACTVAR_TRANS,    expressions.BOOLEAN)
		self.act_xnp   =  self.yi.add_var(ACTVAR_XNOTPROP, expressions.BOOLEAN)
		self.act_xinit =  self.yi.add_var(ACTVAR_XINIT,    expressions.BOOLEAN)
		
		# Definitions
		for name, expr in self.definitions:
			self.yi.add_def(name, self.yi.encode(expr))
		
		# Relations
		for it in self.init:
			self.yi.assertion(self.act[0].mk_not().mk_or([self.yi.encode(it)]))
		for inv in self.invar:
			self.yi.assertion(self.yi.encode(inv))
		for tr in self.trans:
			self.yi.assertion(self.act_trans.mk_not().mk_or([self.yi.encode(tr)]))
		
		self.yi.assertion(self.act_xnp.mk_not().mk_or([self.yi.encode(self.xprop).mk_not()]))
		for xi in self.xinit:
			self.yi.assertion(self.act_xinit.mk_not().mk_or([self.yi.encode(xi)]))
		
		if self.yi_cnt == 0:
			self.yi.push() # vvvv X
			try:
				self.yi.assertion(self.act[0])
				self.yi.push() # vvvv Y
				try:
					# Initial empty ?
					zero = self.yi.context.mk_num(0)
					for i in xrange(self.clockcount):
						self.yi.assertion(self.yi.vars[i].mk_eq(zero))
					if not self.yi.check():
						return (True, 1, '(EMPTY STATE SPACE!)')
				finally:
					self.yi.pop() # ^^^^ Y
			
				# 0 step
				self.yi.assertion(self.yi.encode(self.prop).mk_not()) #I and not P
				ret = self.yi.check() #I and not P
				if ret:
					return (False, 0, states.CounterExample(states.State(self.yi.get_model(), False, self)))
			finally:
				self.yi.pop() # ^^^^ X
		
		###############
		self.mark_y('prop')
		self.yi.assertion(self.yi.encode(self.prop))  # P and invar
	
		# P stays pushed permantently
		
		## Clauses
		
		self.at_clauses = None
		for clind in xrange(1, len(self.clauses)):
			self.increase_k(True)
		if config.check_alot:
			self.yi.check()
		self.yi_cnt += 1
	
	def make_feasible_annotation(fn):
		def rfn(self):
			holds, k, ce = fn(self)
			if not holds:
				if self.clockmax and not config.non_trace_counter_example:
					ce.make_feasible(self)
			return holds, k, ce 
		return rfn
	
	@make_feasible_annotation
	def verify(self):
		'Returns (holds?, k, counter example or string comment)'
		if config.verbosity >= config.VERBOSITY_ANY:
			print
		
		#Yices
		try:
			if config.proof_file != None:
				self.prooff = open(config.proof_file, 'w')
			else:
				self.prooff = None
			
			self.proof_init()
			
			self.clauses = [[]]
			if config.verbosity <= config.VERBOSITY_NONE:
				sys.stdout.write(' .')
				sys.stdout.flush()
			
			ret = self.fresh_context()
			if ret != None:
				self.proof_update(config.PROOF_DETAIL_FINAL, None if ret[0] else ret[2])
				return ret
			
			#Actual Bradley induction
			while True:
				self.mark_y('k-equals-%d', len(self.clauses))
				
				#Clause output
				if config.verbosity >= config.VERBOSITY_ANY:
					print
					self.print_clauses()
				
				#Get rid of states
				if config.verbosity >= config.VERBOSITY_ANY:
					print '#### Getting rid of states'
				while True:
					self.mark_y('initial-bad-state')
					
					# vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv A
					self.to_clauses(len(self.clauses) - 1) #F_k and P
					self.yi.assertion(self.act_trans) #F_k and P and T
					self.yi.assertion(self.act_xnp)
					ret = self.yi.check()
					
					if ret:
						m = self.yi.get_model()
						s = states.State(m, False, self)
					if config.verbosity >= VERBOSITY_MAINLOOP_CHECKS:
						print '-'*80
						print '-'*80
						print '- Checking for states that or one step away from a bad state'
						print ('SAT -- %s' % s) if ret else 'UNSAT'
					self.to_clauses(None) #P
					# ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ A
					
					if not ret:
						break
					
					ret = self.get_rid_of(s, len(self.clauses) - 1, states.State(m, True, self))
					if ret != None:
						self.proof_update(config.PROOF_DETAIL_K)
						self.proof_update(config.PROOF_DETAIL_FINAL, ret)
						return (False, len(self.clauses), ret)
				
				#Clause output
				if config.verbosity >= config.VERBOSITY_ANY:
					print
					self.print_clauses()
				
				#Increase k without breaking pushes and pops
				self.proof_update(config.PROOF_DETAIL_K)
				if config.verbosity <= config.VERBOSITY_NONE:
					sys.stdout.write('.')
					sys.stdout.flush()
				
				self.increase_k(False)
				if self.propagate():
					if config.verbosity >= VERBOSITY_SUM_UP_CLAUSES:
						print '\n\n'
						print '#' * 80
						print '# Clauses:\n'
						self.print_clauses()
					self.proof_update(config.PROOF_DETAIL_K)
					self.proof_update(config.PROOF_DETAIL_FINAL)
					return (True, len(self.clauses), None)
		finally:
			if self.prooff != None:
				self.prooff.write('++ END OF PARSER FRIENDLY PART ++\n')
				self.prooff.write('Command:\n')
				for a in sys.argv:
					self.prooff.write(a)
					self.prooff.write('\n')
				self.prooff.write('\n')
				self.prooff.write('Stats:\n')
				self.prooff.write(str(self.statistics))
				self.prooff.write('\n\n')
				self.prooff.close()

