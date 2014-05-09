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





import random, readline, fractions
import expressions, byices, config, brind, states, signal, sys

DISCRETE_STEP = 0
ELAPSE_STEP = 1

class DelayBound(object):
	def __init__(self, bound, strict=None):
		assert bound == None or isinstance(bound, (int, long, fractions.Fraction))
		assert strict == None or isinstance(strict, bool)
		assert (bound == None) == (strict == None)
		assert bound >= 0
		assert bound != 0 or not strict
		self.bound = bound
		self.strict = strict
	
	def __str__(self):
		if self.bound == None:
			return 'unbounded'
		else:
			return '%s %s unit%s' % ('less than' if self.strict else 'at most', str(self.bound), 's' if self.bound != 1 else '')
	
	def satisfied(self, num):
		return self.bound == None or num < self.bound or (num == self.bound and not self.strict)

def num_to_letters(num):
	assert isinstance(num, (int, long))
	assert num >= 0
	if num == 0:
		return 'A'
	else:
		ret = ''
		while num > 0:
			ret = chr(ord('A') + (num % 26)) + ret
			num /= 26
		return ret

def letters_to_num(strn):
	assert isinstance(strn, basestring)
	strn = strn.lower()
	assert all((ord('a') <= ord(x) <= ord('z')) for x in strn)
	return sum(((ord(x) - ord('a')) * (26**(len(strn) - 1 - i))) for i, x in enumerate(strn))

class Interactor(object):
	def __init__(self, variables, clockmax, init, trans, invar):
		assert isinstance(variables, set)
		assert all(isinstance(x, expressions.Variable) for x in variables)
		assert isinstance(clockmax, dict)
		assert all(isinstance(x, expressions.Variable) for x in clockmax.keys())
		assert all(isinstance(x, (int, long, fractions.Fraction)) for x in clockmax.values())
		assert all(x.type == expressions.REAL for x in clockmax.keys())
		assert isinstance(init, expressions.Expression)
		
		self.varcount   = len(variables)
		self.clockcount = len(clockmax)
		self.variables  = [] #Soon to be filled
		self.clockmax   = []
		self.init       = init
		self.trans      = trans
		self.invar      = invar
		
		# Variables
		stfnc = lambda x, y : cmp(x.name, y.name)
		for clk in sorted(clockmax, stfnc):
			self.variables.append(clk)
			self.clockmax.append(clockmax[clk])
		self.clockcount = len(self.variables)
		assert len(self.clockmax) == self.clockcount
		
		for var in sorted(variables, stfnc):
			self.variables.append(var)
		self.varcount = len(self.variables)
	
	### Initial stuff
	def init_yices(self):
		self.yi         = byices.Yices(config.yicesfile)
		
		assert len(self.yi.vars) == 0
		for v in self.variables:
			self.yi.add_var(v.name, v.type)
		for v in self.variables:
			self.yi.add_var(v.name + brind.PRIME_SUFFIX, v.type)
		assert len(self.yi.vars) == len(self.variables) * 2
		
		if self.clockmax:
			self.deltaind = len(self.yi.vars)
			self.yi.add_var(brind.DELTAVAR_NAME, expressions.REAL)
		
		self.yi.encode(self.trans) # to get variables allocated
	
	### State searching
	def full_states(self, s):
		'Replaces all None values with actual values'
		s += [None] * (self.varcount - len(s))
		
		# Find combinations
		svals = []
		for i in xrange(len(s)):
			if s[i] == None:
				if self.yi.vtypes[i] == expressions.BOOLEAN:
					svals.append([False, True])
				elif self.yi.vtypes[i] == expressions.REAL:
					svals.append([0])
				else:
					raise Exception('Unsupported type: self.yi.vtypes[i]')
			else:
				svals.append([s[i]])
		assert len(svals) == len(s)
		assert len(svals) >= 1
		
		# Products
		comb = [[]]
		for vals in svals:
			ncomb = []
			for c in comb:
				for val in vals:
					ncomb.append(c + [val])
			comb = ncomb
		return [states.State(x, False, self) for x in comb]
	
	def get_all_states(self, primed):
		ret = []
		while self.yi.check():
			# Get states
			s = states.State(self.yi.get_model(), primed, self)
			ret += self.full_states(s)
			
			# Encode negation minus clocks
			for i in xrange(self.clockcount):
				s[i] = None
			enc = s.encode_exact(self.yi, primed)
			if len(enc) == 0: #'Anything possible'
				break
			elif len(enc) == 1:
				enc = enc[0]
			else:
				enc = enc[0].mk_and(enc[1:])
			self.yi.assertion(enc.mk_not())
		return ret
	
	def get_delay_bound(self):
		'Returns delay bound for unbounded'
		# Find relevant values
		if not self.clockmax:
			return None
		relevant_values = [0]
		for ci in xrange(self.clockcount):
			mx = self.clockmax[ci]
			v = self.state[ci]
			assert v != None
			rval = mx - v
			while rval > 0:
				relevant_values.append(rval)
				rval -= 1
		relevant_values = sorted(set(relevant_values))
		
		# Check them
		try:
			self.yi.push()
			self.yi.assertion(self.yi.encode(self.invar))
			for i in xrange(len(relevant_values)):
				# Values
				rv = relevant_values[i]
				last = i >= len(relevant_values) - 1
				if last:
					rvp = rv + fractions.Fraction(1, 2)
				else:
					rvp = (rv + relevant_values[i+1]) / fractions.Fraction(2)
				
				# rv
				try:
					self.yi.push()
					for enc in self.state.elapse(rv).encode_exact(self.yi, False):
						self.yi.assertion(enc)
					
					if not self.yi.check():
						return DelayBound(rv, True)
				finally:
					self.yi.pop()
			
				#rvp
				try:
					self.yi.push()
					for enc in self.state.elapse(rvp).encode_exact(self.yi, False):
						self.yi.assertion(enc)
					
					if not self.yi.check():
						return DelayBound(rv, False)
				finally:
					self.yi.pop()
		finally:
			self.yi.pop()
		
		return DelayBound(None)
		
	## Selection
	def select_state(self, typ, states, delay_bound=None):
		'Returns selected state (or None to quit)'
		# Print options
		if (not states) and ((delay_bound == None ) or (delay_bound.bound == 0)):
			print 'DEADLOCK -- No %s state' % typ
			sys.exit(0)
		
		if states:
			print 'Please select a%s %s state' % ('n' if typ[0].lower() in 'aiouey' else '', typ)
			strns = [str(s) for s in states]
			multiline = any(('\n' in x) for x in strns)
			for i, strn in enumerate(strns):
				print '  State %s: %s%s' % (num_to_letters(i), strn, '\n' if multiline else '')
		if delay_bound != None and (delay_bound.bound == None or delay_bound.bound > 0):
			print '%s perform a time elapse step by entering a number (%s)' % ('Or' if states else 'Please', str(delay_bound))
		
		# State selection
		try:
			while True:
				try:
					print
					inp = raw_input('Your choice: ')
				except EOFError, e:
					return None
				
				oinp = inp
				inp = inp.lower().strip()
				if inp == '':
					if states:
						selected = random.randint(0, len(states) - 1)
						print 'Selected state', num_to_letters(selected), 'randomly'
						return states[selected]
				elif all((ord('a') <= ord(c) <= ord('z')) for c in inp):
					num = letters_to_num(inp)
					if 0 <= num < len(states):
						return states[num]
				elif delay_bound != None:
					try:
						if '/' in inp:
							inp = inp.split('/')
							inp = fractions.Fraction(int(inp[0]), int(inp[1]))
						elif '.' in inp:
							[l, r] = inp.split('.')
							den = 10**len(r)
							if len(l) == 0:
								l = '0'
							inp = fractions.Fraction(int(l) * den + int(r), den) # Avoid using fractions to avoid rounding errors
						else:
							inp = int(inp)
						if inp >= 0 and delay_bound.satisfied(inp):
							return self.state.elapse(inp)
					except ValueError, e:
						pass
				print 'INVALID SELECTION:', repr(oinp)
		finally:
			print
		assert False
	
	def select_successor(self):
		# Delay bound
		delay_bound = self.get_delay_bound()
		
		# Successors
		self.yi.push()
		for enc in self.state.encode_exact(self.yi, False):
			self.yi.assertion(enc)
		self.yi.assertion(self.yi.encode(self.invar))
		self.yi.assertion(self.yi.encode(self.trans))
		if self.clockmax:
			zero = self.yi.context.mk_num(0)
			self.yi.assertion(self.yi.vars[self.deltaind].mk_eq(zero))
			for i in xrange(self.clockcount):
				self.yi.assertion(self.yi.vars[i].mk_ge(zero))
				self.yi.assertion(self.yi.vars[i + self.varcount].mk_ge(zero))
		successors = self.get_all_states(True)
		self.yi.pop()
		
		# Choice
		self.state = self.select_state('successor', successors, delay_bound)
		
			
	
	def get_initial_states(self):
		self.yi.push()
		self.yi.assertion(self.yi.encode(self.init))
		self.yi.assertion(self.yi.encode(self.invar))
		if self.clockmax:
			# Note that all clocks are set to zero due to real valued variables being unused leading to trouble
			zero = self.yi.context.mk_num(0)
			for i in xrange(self.clockcount):
				self.yi.assertion(self.yi.encode(expressions.AstExpression('=', self.variables[i], '0')))
				self.yi.assertion(self.yi.vars[i + self.varcount].mk_eq(zero))
			self.yi.assertion(self.yi.vars[self.deltaind].mk_eq(zero))
		ret = self.get_all_states(False)
		self.yi.pop()
		return ret
		
	
	### Control flow
	def print_instructions(self):
		print 'Commands:'
		print '  <number> : Select option <number>. Supported formats: 1.5, 3/2'
		print '  <enter>  : Select random option'
		print '  EOF      : Quit'
		print
	
	def run(self):
		prev_sig = signal.signal(signal.SIGINT, lambda _, __ : sys.exit(0))
		try:
			self.print_instructions()
		
			self.init_yices()
		
			inits = self.get_initial_states()
			self.state = self.select_state('initial', inits)
		
			while self.state != None:
				print 'Current state:', self.state
				print
				self.select_successor()
		finally:
			signal.signal(signal.SIGINT, prev_sig)

if __name__ == '__main__':
	for n in xrange(100):
		strn = num_to_letters(n)
		print n, strn, letters_to_num(strn)


