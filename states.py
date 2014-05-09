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





import sys, copy, fractions, operator
import byices, brind, expressions, config
from yicesfull import YicesInternalExpression

MULTILINE_STRING_THRESHOLD = 20
MULTILINE_STRING_ITEMS_PER_LINE = 4

TYPE_BOOLEAN = byices.TYPE_BOOLEAN
TYPE_RANGE = byices.TYPE_RANGE
TYPE_CLOCK = byices.TYPE_REAL
assert TYPE_BOOLEAN >= 0
assert TYPE_RANGE >= 0
assert TYPE_CLOCK >= 0

################################################################################
# Helpers                                                                      #
def chunks(lst, num):                                                          #
	return [lst[num*i:num*i+num] for i in xrange(len(lst) / num + (1 if len(lst) % num > 0 else 0))]


_LT  = -2
_LEQ = -1
_GEQ = 0
_GT  = 1
_OPS = {
	_LT  : operator.lt,
	_LEQ : operator.le,
	_GEQ : operator.ge,
	_GT  : operator.gt
}
################################################################################
class Clause(list):                                                            #
	'Clause representation '                                                                                      \
	'Clauses may contain None entries which are ignored by some functions but not '                                \
	'by all '                                                                                                       \
	'Tuple (boolean literals; range literals; clock literals; clockdiff_literals)\n'                                 \
	'Boolean literals:    -1-id for negated, 1+id for non-negated\n'                                                  \
	'Range literals:      (id, val) for id != val\n'                                                                   \
	'Clock literals:      (id, const, strict) for clk_id > const (if strict) or clk_id >= const (otherwise)\n'          \
	'Upper bound clock literals: (id, const, -1-strict) for clk-id < const or clk-id <= const\n'                         \
	'Clk diff literals:   (ida, idb, const, strict) for clk_ida - clk_idb > const (if strict) or ... >= ... (otherwise)\n'\
	'Sorting: boolean literals by variable id; clock literals by clock id (upper bound before lower); difference literals lexicographically\n'        \
	'by clock id 0 -> clock id 1\n'
	may_drop = None
	def __init__(self, varcount, vnames, vtypes, constants):
		'Constructs a new (empty) clause. Note that the order of literals has to '\
		'be maintained and the num_* variables have to be updated when adding '    \
		'literals'
		assert isinstance(vnames, list)
		assert all(isinstance(x, basestring) for x in vnames)
		self.num_bool_lits  = 0
		self.num_range_lits = 0
		self.num_clock_lits = 0
		self.num_diff_lits = 0
		self.vnames = vnames
		self.varcount = varcount
		self.vtypes = vtypes
		self.constants = constants
	
	def empty(self):
		return all(x == None for x in self)
	
	def litcnt(self):
		return sum(0 if x == None else 1 for x in self)
	
	def _correct_order(self):
		cpy = copy.copy(self)
		cpy.drop_nones()
		low = 0
		
		# Boolean literals
		for i in xrange(low, low + cpy.num_bool_lits - 1):
			if abs(cpy[i]) >= abs(cpy[i+1]):
				return False
		low += cpy.num_bool_lits
		
		# Range literals
		for i in xrange(low, low + cpy.num_range_lits - 1):
			if cpy[i][0] >= cpy[i+1][0]:
				return False
		low += cpy.num_range_lits
		
		# Clock literals
		for i in xrange(low, low + cpy.num_clock_lits - 1):
			if cpy[i][0] > cpy[i+1][0]:
#				print 1
				return False
			if cpy[i][0] == cpy[i+1][0] and cpy[i][2] >= cpy[i+1][2]:
#				print 2, i, cpy[i], cpy[i+1]
				return False
		low += cpy.num_clock_lits
		
		# Difference literals
		for i in xrange(low, low + cpy.num_diff_lits - 1):
			if cpy[i][0] > cpy[i+1][0] or (cpy[i][0] == cpy[i+1][0] and cpy[i][1] >= cpy[i+1][1]):
				return False
		low += cpy.num_diff_lits
		assert low == len(cpy)
		
		return True
	
	def __repr__(self):
		'tolerates None entries'
#		assert self._correct_order(), str(self)
		return '%s;%d;%d;%d;%d' % (list.__repr__(self), self.num_bool_lits, self.num_range_lits, self.num_clock_lits, self.num_diff_lits)
	
	def __str__(self):
		return self.string()
	
	def string(self, use_enum_consts = True):
		'tolerates None entries'
		if any(x != None for x in self):
#			assert self._correct_order(), repr(list(self))
			strn = []
			low = 0
		
			# Boolean literals
			for i in xrange(low, low + self.num_bool_lits):
				if self[i] != None:
					var = abs(self[i]) - 1
					if self[i] < 0:
						strn.append("!%s" % self.vnames[var])
					else:
						assert self[i] > 0
						strn.append(self.vnames[var])
			low += self.num_bool_lits
		
			# Range literals
			for i in xrange(low, low + self.num_range_lits):
				if self[i] != None:
					if use_enum_consts and isinstance(self.vtypes[self[i][0]], expressions.Enumeration):
						val = self.constants[self[i][1]]
					else:
						val = str(self[i][1])
					strn.append('%s != %s' % (self.vnames[self[i][0]], val))
			low += self.num_range_lits
		
			# Clock literals
			for i in xrange(low, low + self.num_clock_lits):
				if self[i] != None:
					(var, const, strict) = self[i]
					if strict == _GT:
						op = '>'
					elif strict == _GEQ:
						op = '>='
					elif strict == _LEQ:
						op = '<='
					else:
						assert strict == _LT
						op = '<'
					strn.append('%s %s %d' % (self.vnames[var], op, const))
			low += self.num_clock_lits
		
			# Difference literals
			for i in xrange(low, low + self.num_diff_lits):
				if self[i] != None:
					(vara, varb, const, strict) = self[i]
					el = '%s >%s %s' % (self.vnames[vara], '' if strict else '=', self.vnames[varb])
					if const != 0:
						el += ' %s %d' % ('-' if const < 0 else '+', abs(const))
					strn.append(el)
			low += self.num_diff_lits
			assert low == len(self)
		
			return ' | '.join(strn)
		else:
			return 'FALSE'
		
	def encode_lits(self, yi, as_clause, primed, encs):
		'Encodes all literals and appends then corresponding handles to encs' \
		'tolerates None entries'
		
		assert self._correct_order(), repr(self) + '\n\n' + str(self)
		
		# Boolean literals
		low = 0
		for i in xrange(low, low + self.num_bool_lits):
			if self[i] == None:
				encs.append(None)
			else:
				var = abs(self[i]) - 1
				if primed:
					var += self.varcount
				encs.append(yi.literals[var][as_clause][self[i] < 0])
				assert encs[-1].varid == (var if ((self[i] > 0 and as_clause) or (self[i] < 0 and not as_clause)) else -1)
		low += self.num_bool_lits
		
		# Range literals
		for i in xrange(low, low + self.num_range_lits):
			if self[i] == None:
				encs.append(None)
			else:
				var, val = self[i]
				if primed:
					var += self.varcount
				encs.append(yi.literals[var][as_clause][self[i][1]])
		low += self.num_range_lits
		
		# Clock literals + difference literals
		for i in xrange(low, low + self.num_clock_lits + self.num_diff_lits):
			if self[i] == None:
				encs.append(None)
			else:
				if len(self[i]) == 3: # Clock literal
					ci, const, op = self[i]
					if primed:
						ci += self.varcount
					enc = yi.vars[ci]
				else: # Difference literal
					cia, cib, const, op = self[i]
					if primed:
						cia += self.varcount
						cib += self.varcount
					enc = yi.vars[cia].mk_sub([yi.vars[cib]])
				cenc = yi.context.mk_num(const)
				if as_clause:
					if op == _GT:
						enc = enc.mk_gt(cenc)
					elif op == _GEQ:
						enc = enc.mk_ge(cenc)
					elif op == _LT:
						enc = enc.mk_lt(cenc)
					else:
						assert op == _LEQ
						enc = enc.mk_le(cenc)
				else:
					if op == _GT:
						enc = enc.mk_le(cenc)
					elif op == _GEQ:
						enc = enc.mk_lt(cenc)
					elif op == _LT:
						enc = enc.mk_ge(cenc)
					else:
						assert op == _LEQ
						enc = enc.mk_gt(cenc)
				encs.append(enc)
		low += self.num_clock_lits + self.num_diff_lits
		assert low == len(self)
		return encs
	
	def subsumes(self, other): #################################################
		'Syntactic sumbsumtion checking. For each literal in self checks, ' \
		'whether the same (or a weaker) literal is in other. Note that this ' \
		'is a stronger property than actual subsumption. '\
		'E.g. x >= 2 | y >= 2 | x - y >= 0 | y - x >= 1 subsumes x >= 2 | x - y >= 0 | y - x >= 1. '\
		'Situations like that could be avoided by using tight (term?) difference '\
		'bound matrices, but the unsat core extraction should in most cases already '\
		'avoid them at the cost of one initiation check.\n' \
		'\n' \
		'NOTE: Does not tolerate None entries'
		assert self._correct_order(), str(self)
		assert isinstance(other, Clause)
		assert all(x != None for x in self)
		if self.num_bool_lits > other.num_bool_lits or \
			self.num_range_lits > other.num_range_lits or \
			self.num_clock_lits > other.num_clock_lits or \
			self.num_diff_lits > other.num_diff_lits:
				return False
		
		# Boolean literals
		low = 0
		olow = 0
		oi = olow - 1
		for i in xrange(low, low + self.num_bool_lits):
			# Find variable in other
			while oi < olow + other.num_bool_lits - 1:
				oi += 1
				assert isinstance(other[oi], (int, long))
				assert isinstance(self[i], (int, long))
				if other[oi] == self[i]:
					break
				elif abs(other[oi]) >= abs(self[i]):
					return False
			else:
				return False
		low += self.num_bool_lits
		olow += other.num_bool_lits
		
		# Range literals
		oi = olow - 1
		for i in xrange(low, low + self.num_range_lits):
			# Find variable in other
			while oi < olow + other.num_range_lits - 1:
				oi += 1
				assert len(other[oi]) == len(self[i])
				if other[oi] == self[i]:
					break
				elif other[oi][0] >= self[i][0]: # Different constant or variable not in other
					return False
			else:
				return False
		low += self.num_range_lits
		olow += other.num_range_lits
		
		# Clock literals
		oi = olow - 1
		for i in xrange(low, low + self.num_clock_lits):
			# Find variable in other
			while oi < olow + other.num_clock_lits - 1:
				oi += 1
				assert len(other[oi]) == len(self[i])
				if other[oi][0] == self[i][0] and (self[i][2] >= 0) == (other[oi][2] >= 0):
					assert (self[i][2] >= 0) == (other[oi][2] >= 0)
					if self[i][2] >= 0: # > or >=
						# Constant in other higher or constants same but this non-strict and other strict
						if other[oi][1] > self[i][1] or (other[oi][1] == self[i][1] and (not self[i][2] and other[oi][2])):
							return False
						else:
							break
					else: # < or <=
						# Constant in other lower or constants same but this non-strict and other strict
						if other[oi][1] < self[i][1] or (other[oi][1] == self[i][1] and (not (self[i][2] == _LT) and (other[oi][2] == _LT))):
							return False
						else:
							break
				elif other[oi][0] > self[i][0] or (other[oi][0] == self[i][0] and (self[i][2] >= 0) != (other[oi][2] >= 0)):
					return False
			else:
				return False
		low += self.num_clock_lits
		olow += other.num_clock_lits
		
		# Difference literals
		oi = olow - 1
		for i in xrange(low, low + self.num_diff_lits):
			# Find variable in other
			while oi < olow + other.num_diff_lits - 1:
				oi += 1
				assert len(other[oi]) == len(self[i])
				if other[oi][0] == self[i][0] and other[oi][1] == self[i][1]:
					# Constant in other higher or constants same but this non-strict and other strict
					if other[oi][2] > self[i][2] or (other[oi][2] == self[i][2] and (not self[i][3] and other[oi][3])):
						return False
					else:
						break
				elif other[oi][0] > self[i][0] or (other[oi][0] == self[i][0] and other[oi][1] > self[i][1]):
					return False
			else:
				return False
		
		low += self.num_diff_lits
		olow += other.num_diff_lits
		assert low == len(self)
		assert olow == len(other)
		
		return True
	
	def drop_nones(self):
		nbl = self.num_bool_lits
		nrl = self.num_range_lits
		ncl = self.num_clock_lits
		ndl = self.num_diff_lits
		target = 0
		for i in xrange(len(self)):
			if self[i] == None:
				if i < self.num_bool_lits:
					nbl -= 1
				elif i < self.num_bool_lits + self.num_range_lits:
					nrl -= 1
				elif i < self.num_bool_lits + self.num_range_lits + self.num_clock_lits:
					ncl -= 1
				else:
					assert i < self.num_bool_lits + self.num_range_lits + self.num_clock_lits + self.num_diff_lits
					ndl -= 1
			else:
				self[target] = self[i]
				if self.may_drop != None:
					self.may_drop[target] = self.may_drop[i]
				target += 1
		self.num_bool_lits = nbl
		self.num_range_lits = nrl
		self.num_clock_lits = ncl
		self.num_diff_lits = ndl
		self[target:] = []
	
	def drop_lits_satisfied_by(self, s):
		'Drops literals satisfied by the state s. '\
		'Tolerates (and generates) None literals'
		assert self._correct_order(), str(self)
		assert isinstance(s, State)
		
		# Boolean literals
		low = 0
		for i in xrange(low, low + self.num_bool_lits):
			if self[i] != None:
				if s[abs(self[i]) - 1] ^ (self[i] < 0):
					self[i] = None
		low += self.num_bool_lits
		
		# Range literals -- *** unsupported ***
		for i in xrange(low, low + self.num_range_lits):
			if self[i] != None:
				if s[self[i][0]] != self[i][1]:
					self[i] = None
		low += self.num_range_lits
		
		# Clock literals
		for i in xrange(low, low + self.num_clock_lits):
			if self[i] != None:
				clk, const, op = self[i]
				if _OPS[op](s[clk], const):
					self[i] = None
		low += self.num_clock_lits
		
		# Difference literals
		for i in xrange(low, low + self.num_diff_lits):
			if self[i] != None:
				clka, clkb, const, strict = self[i]
				diff = s[clka] - s[clkb]
				if diff > const or (diff == const and not strict):
					self[i] = None
		low += self.num_diff_lits
		assert low == len(self)
	
	def recheck_initiation_after_drop(self, index):
		'Returns True if either dropping that literal makes self non-trivially initial or the literal is not a clock literal.'
		assert False, 'Currently not used'
		assert 0 <= index <= len(self)
		assert self[index] != None
		
		high = self.num_bool_lits + self.num_range_lits
		if index < high:
			return True # Always re-check for non-clock literals
		
		high += self.num_clock_lits
		if index < high:
			return False # Never re-check for clock literals
		
		assert index < high + self.num_diff_lits
		if self[index][2] < 0 or (self[index][2]== 0 and not self[index][3]):
			# The dropped literal makes this clause trivially initial
			lit = self[index]
			self[index] = None
			ret = self.trivially_initial() # Check, whether still trivially initial after dropping literal
			self[index] = lit
			if not ret:
				return True
		return False
	
	def trivially_initial(self):
		'Returns True if there is a literal like x - y > -4'
		assert False, 'Currently not used'
		low = self.num_bool_lits + self.num_range_lits + self.num.clock_lits
		for i in xrange(low, low + self.num_diff_lits):
			if self[i] != None:
				if self[i][2] < 0 or (self[i][2]== 0 and not self[i][3]):
					return True
		return False

################################################################################
class State(list):                                                             #
	'Assumed to be immutable'                                                  #
	def __init__(self, model, primed, cs):
		assert isinstance(model, list)
		assert isinstance(primed, (bool, int, long))
		
		if isinstance(primed, bool):
			low = cs.varcount if primed else 0
		else:
			assert isinstance(primed, (int, long))
			low = primed
			
		vid = low
		while vid - low < cs.varcount:
			if len(self) < cs.clockcount and cs.INT_FRAC_SPLIT:
				if len(model) <= vid + 1 or model[vid] == None or model[vid + 1] == None:
					self.append(None)
				else:
					self.append(model[vid] + model[vid + 1])
				vid += 1
			else:
				if vid < len(model):
					self.append(model[vid])
				else:
					self.append(None)
			vid += 1
		self.vnames = cs.yi.vnames
		self.vtype_ids = cs.yi.vtype_ids
		self.clockcount = cs.clockcount
		self.clockmax = cs.clockmax
		self.vtypes = cs.yi.vtypes
		self.constants = cs.constants
	
	def __str__(self):
		return self.string()
	
	def elapse(self, amount):
		'Returns new state resulting from letting time elapse by specified amount'
		ret = copy.copy(self)
		for i in xrange(self.clockcount):
			if ret[i] != None:
				ret[i] += amount
		return ret
	
	def string(self, pretty=True):
		if self:
			strn = []
			order = []
			for i in xrange(len(self)):
				order.append((self.vnames[i], i))
			order.sort()
			for _, i in order:
				if self[i] == None:
					strn.append('')
				else:
					if isinstance(self.vtypes[i], expressions.Enumeration):
						val = self.constants[int(self[i])]
					else:
						val = str(self[i])
					if config.short_states:
						strn.append(str(val))
					else:
						strn.append('%s=%s' % (self.vnames[i], val))
			jner = '\t'
			if pretty and len(self) >= MULTILINE_STRING_THRESHOLD:
				return '\n'.join(map(lambda x : jner.join(x), chunks(strn, MULTILINE_STRING_ITEMS_PER_LINE)))
			else:
				return jner.join(x for x in strn if x)
		else:
			return '<empty state>'
	
	def literals(self):
		# Boolean literals
		clause = Clause(len(self), self.vnames, self.vtypes, self.constants)
		
		for vid in xrange(self.clockcount, len(self)):
			if self[vid] == None:
				pass
			elif self.vtype_ids[vid] == TYPE_BOOLEAN:
				if self[vid]:
					clause.append(-1-vid)
				else:
					clause.append(1+vid)
			elif self.vtype_ids[vid] == TYPE_RANGE:
				pass #below
			else:
				print self.vtype_ids, vid, self.vtype_ids[vid], TYPE_BOOLEAN, TYPE_RANGE
				raise Exception('Not (yet) supported')
		
		clause.num_bool_lits = len(clause)
		
		# Range literals
		for vid in xrange(self.clockcount, len(self)):
			if self[vid] == None:
				pass
			elif self.vtype_ids[vid] == TYPE_RANGE:
				clause.append((vid, self[vid]))
		
		clause.num_range_lits = len(clause) - clause.num_bool_lits
		# Clock literals
		bounded = []
		if config.basic_regions:
			for cid in xrange(0, self.clockcount):
				assert len(bounded) == cid
			
				v = self[cid]
				assert v >= 0
				mx = self.clockmax[cid]
				if v > mx:
					bounded.append(False)
					clause.append((cid, mx, _LEQ))
				else:
					bounded.append(True)
					# Integer different
					vi = int(v)
					#In principle, we should do:
					#clause.append((cid, vi, _LT))
					#clause.append((cid, vi + 1, _GEQ))
					#but we will not add literals if a weaker literal is added later
					# Fractional = 0 different
					if  v % 1 == 0:
						clause.append((cid, vi, _LT))
#						clause.append((cid, vi + 1, _GEQ))
						
						clause.append((cid, vi, _GT))
					else:
						clause.append((cid, vi, _LEQ))
						
#						clause.append((cid, vi, _LT))
						clause.append((cid, vi + 1, _GEQ))
		else:
			bound_const = []
			for cid in xrange(0, self.clockcount):
				assert len(bounded) == cid
			
				v = self[cid]
				mx = self.clockmax[cid]
				if v > mx:
					bounded.append(False)
					bound_const.append(None)
				else:
					bounded.append(True)
					if v % 1 == 0:
						v = int(v)
						clause.append((cid, v,     True ))
					else:
						v = int(v) + 1
						clause.append((cid, v, False))
					bound_const.append(v)
		clause.num_clock_lits = len(clause) - clause.num_range_lits - clause.num_bool_lits
		
		# Difference literals
		if config.basic_regions:
			newlits = []
			for cida in xrange(0, self.clockcount):
				if bounded[cida]:
					va = self[cida]
					vai = int(va)
					vaf = va % 1
					assert vai + vaf == va
					for cidb in xrange(cida + 1, self.clockcount):
						if bounded[cidb]:
							vb = self[cidb]
							assert vb >= 0, vb
							vbi = int(vb)
							vbf = vb % 1
							assert vbi + vbf == vb, (vbi, vbf,  vb)
							if vaf < vbf:
								# a - vai >= b - vbi
								# a - b >= vai - vbi
								newlits.append((cida, cidb, vai - vbi, False))
							elif vaf == vbf:
								# a - vai != b - vbi
								# a - vai < b - vbi or a - vai > b - vbi
								# a - b < vai - vbi or a - b > vai - vbi
								# b - a > vbi - vai or a - b > vai - vbi
								newlits.append((cidb, cida, vbi - vai, True))
								newlits.append((cida, cidb, vai - vbi, True))
							else: #vaf > vbf
								# a - vai <= b - vbi
								# vbi - vai <= b - a
								newlits.append((cidb, cida, vbi - vai, False))
			newlits.sort(cmp = lambda a, b : cmp(a[0], b[0]) if a[0] != b[0] else cmp(a[1], b[1]))
			clause += newlits
		else:
			for cida in xrange(0, self.clockcount):
				if bounded[cida]:
					va = self[cida]
					for cidb in xrange(0, self.clockcount):
						if cida != cidb:
							if bounded[cidb]:
								vb = self[cidb]
								diff = va - vb
								const = int(diff - (diff % 1)) #NOTE: can be negative; so int(diff) does not work
							else:
								diff = bound_const[cida] - self.clockmax[cidb]
								assert diff % 1 == 0
								const = int(diff)
							if not bounded[cidb]:
								clause.append((cida, cidb, const,     False))
							elif diff % 1 == 0:
								clause.append((cida, cidb, const,     True ))
							else:
								clause.append((cida, cidb, const + 1, False))
							
		clause.num_diff_lits = len(clause) - clause.num_clock_lits - clause.num_range_lits - clause.num_bool_lits
		
		return clause
	
	def short_str(self):
		ret = []
		for v in self:
			if isinstance(v, bool):
				ret.append("1" if v else "0")
			else:
				ret.append("." + str(v))
		return "".join(ret)
	
	def encode_exact(self, yi, primed=False):
		ret = []
		for (k, v) in enumerate(self):
			if primed:
				k += len(self)
			if v == None:
				continue
			elif self.vtype_ids[k] == TYPE_BOOLEAN or self.vtype_ids[k] == TYPE_RANGE:
				assert (self.vtype_ids[k] != TYPE_BOOLEAN) or (yi.literals[k][False][v].varid == (k if v else -1))
				enc = yi.literals[k][False][v]
			elif self.vtype_ids[k] == TYPE_CLOCK:
				var = yi.vars[k]
				if isinstance(v, (int, long)):
					enc = var.mk_eq(yi.context.mk_num(self[k]))
				else:
					assert isinstance(v, fractions.Fraction)
					enc = yi.context.mk_num(self[k].denominator).mk_mul([var]).mk_eq(yi.context.mk_num(self[k].numerator))
			else:
				assert False
			ret.append(enc)
		return ret
	
	def encode_region_next(self, yi):
		ret = []
		# Boolean + Range
		for vi in xrange(self.clockcount, len(self)):
			assert self.vtype_ids[vi] == TYPE_BOOLEAN or self.vtype_ids[vi] == TYPE_RANGE
			v = self[vi]
			if v != None:
				var = vi + len(self)
				enc = yi.literals[var][False][v]
				assert (self.vtype_ids[vi] != TYPE_BOOLEAN) or (enc.varid == (var if v else -1))
				ret.append(enc)
		
		# Clocks -- integral
		bounded = [True,] * self.clockcount
		for ci in xrange(self.clockcount):
			var = yi.vars[ci + len(self)]
			if self[ci] != None:
				if self[ci] > self.clockmax[ci]:
					bounded[ci] = False
					ret.append(var.mk_gt(yi.context.mk_num(self.clockmax[ci])))
				elif self[ci] % 1 == 0:
					ret.append(var.mk_eq(yi.context.mk_num(int(self[ci]))))
				else:
					integ = self[ci] - (self[ci] % 1)
					assert integ % 1 == 0
					integ = int(integ)
					ret.append(var.mk_gt(yi.context.mk_num(integ)))
					ret.append(var.mk_lt(yi.context.mk_num(integ + 1)))
		
		# Clocks -- fractional
		for ci in xrange(self.clockcount):
			if self[ci] != None and bounded[ci]:
				intei = self[ci] - (self[ci] % 1)
				assert intei % 1 == 0
				intei = int(intei)
				fraci = self[ci] - intei
				evi = yi.vars[ci + len(self)]
				efraci = evi.mk_sub([yi.context.mk_num(intei)])
				for cj in xrange(ci + 1, self.clockcount):
					if self[cj] != None and bounded[cj]:
						intej = self[cj] - (self[cj] % 1)
						assert intej % 1 == 0
						intej = int(intej)
						fracj = self[cj] - intej
						evj = yi.vars[cj + len(self)]
						efracj = evj.mk_sub([yi.context.mk_num(intej)])
						if fraci > fracj:
							ret.append(efraci.mk_gt(efracj))
						elif fraci == fracj:
							ret.append(efraci.mk_eq(efracj))
						else:
							assert fraci < fracj
							ret.append(efraci.mk_lt(efracj))
		
		return ret
	
	def same_region(self, other, basic_regions):
		assert isinstance(other, State)
		assert len(self) == len(other)
		assert self.vnames == other.vnames
		assert self.vtype_ids == other.vtype_ids
		assert self.clockcount == other.clockcount
		assert self.clockmax == other.clockmax
		assert len(self) == len(other)
		assert self.vtypes == other.vtypes
		assert self.constants == other.constants
		assert isinstance(basic_regions, bool)
		
		# No clocks
		if self.clockcount == 0:
			return self == other
		
		# Non-clock variables same?
		for i in xrange(self.clockcount, len(self)): # Ordinary variables
			if self[i] != other[i]:
				return False
		
		if basic_regions:
			# Integral parts same ?
			for i in xrange(self.clockcount):
				if self[i] > self.clockmax[i]:
					if not other[i] > self.clockmax[i]:
						return False
				elif other[i] > self.clockmax[i]:
					return False
				elif int(self[i]) != int(other[i]):
					return False
		
			# Fractional ordering same ?
			sfracs = [(self[i] % 1, i) for i in xrange(self.clockcount)]
			ofracs = [(other[i] % 1, i) for i in xrange(self.clockcount)]
			skey = lambda x : x[0]
			sfracs.sort(key = skey)
			ofracs.sort(key = skey)
		
			assert sfracs
			assert ofracs
		
			for i in xrange(self.clockcount): # Different order
				if sfracs[i][1] != ofracs[i][1]:
					return False
		
			if (sfracs[0][0] == 0) != (ofracs[0][0] == 0): # Lowest zero for one but not the other
				return False
		
			for i in xrange(self.clockcount - 1): # Equality / lower than signs in different locations
				if (sfracs[i][0] == sfracs[i+1][0]) != (ofracs[i][0] == ofracs[i+1][0]):
					return False
		else:
			for c in xrange(self.clockcount):
				ci = self[c]
				cj = other[c]
				ci_i = int(ci)
#				ci_f = ci % 1
				cj_i = int(cj)
				cj_f = cj % 1
				cmaxj = cj > self.clockmax[c]
#				print c, " ", ci, ci_i, " ", cj, cj_i, cj_f, " ", cmaxj
				if not cmaxj:
					#2:
					if ci_i >= cj_i + 1:
						return False
					#3:
					if 	ci > cj_i:
						return False
				for d in xrange(self.clockcount):
					if c != d:
						di = self[d]
						dj = other[d]
						di_i = int(di)
#						di_f = di % 1
						dj_i = int(dj)
						dj_f = dj % 1
						dmaxj = dj > self.clockmax[d]
						if c < d: #once
							#4:
							if not cmaxj and not dmaxj:
								if cj_f < dj_f:
									if ci - cj_i >= di - dj_i or ci - cj_i <= di - dj_i - 1:
										return False
								elif cj_f > dj_f:
									if ci - cj_i <= di - dj_i or ci - cj_i >= di - dj_i + 1:
										return False
								else:
									assert cj_f == dj_f
									if ci - cj_i < di - dj_i or ci - cj_i > di - dj_i:
										return False
						#5: twice
						if not cmaxj and dmaxj:
							if cj_f > 0:
								if ci - cj_i >= di - self.clockmax[d] + 1:
									return False
							else:
								assert cj_f == 0
								if ci - cj_i > di - self.clockmax[d]:
									return False
		
#		print self, other
		
		return True

################################################################################
class CounterExample(list):                                                    #
	def __init__(self, s0 = None, s1 = None):                                  #
		assert s0 == None or isinstance(s0, State)
		assert s1 == None or isinstance(s1, State)
		if s0 != None:
			self.append((0, s0))
		if s1 != None:
			self.append((1, s1))
	
	def make_feasible(self, cs):
		'In presence of time, counter-examples are not real traces of the system '\
		'but a sequence of states such that there is a real counter-example '\
		'visiting the same regions. This method turns the counter-example into '\
		'an actual trace of the system. Returns time deltas'
		assert cs.yi.poplevel() == 0
		
		if cs.clockcount:
			deltas = []
			# Initial states
			cs.to_clauses(0) # vvvv A
			for ci in xrange(cs.clockcount):
				vi = cs.yi.vars[ci]
				cs.yi.assertion(vi.mk_eq(cs.yi.context.mk_num(0)))
			if not cs.yi.check():
				raise Exception('Failed to extract counter-example')
			self[0:0] = [(None, State(cs.yi.get_model(), False, cs))]
			cs.to_clauses(None) # ^^^^ A
		
			# Successive states
			cs.yi.push() # vvvv B
			cs.yi.assertion(cs.act_trans)
			deltaind = cs.yi.vnames.index(brind.DELTAVAR_NAME)
			j = 1
			while j < len(self) - 1:
				index, state = self[j]
				nindex, nstate = self[j+1]
				cs.yi.push() # vvvv C
			
				encs  =  state.encode_exact(cs.yi)
				encs += nstate.encode_region_next(cs.yi)
				for e in encs:
					cs.yi.assertion(e)
				if not cs.yi.check():
					strns = self.strings()
					print '\n'.join(strns[:j+1])
					print '---'
					print '\n'.join(strns[j+1:])
					raise Exception('Failed to extract counter-example')
			
				m = cs.yi.get_model()
				delta = m[deltaind]
				deltas.append(delta)
				assert delta >= 0
				ns = State(m, True, cs)
				if delta == 0:
					self[j+1] = (nindex, ns)
				else:
					self[j+1:j+2] = [(None, State([(val if k >= cs.clockcount else val - delta) for (k, val) in enumerate(ns)], False, cs)),
										(nindex, ns)]
					j += 1
				cs.yi.pop() # ^^^^ C
			
				j += 1
			cs.yi.pop() # ^^^^ B
			return deltas
	
	def strings(self, line_prefix = "", short_states=False):
		ret = []
		for index, s in self:
			statestr = s.short_str() if short_states else str(s)
			if '\n' in statestr:
				if index != None:
					header = 'State %d ' % index
				else:
					header = ''
				ret.append('%s%s\n%s\n' % (header, '-' * (80 - len(header)), statestr))
			else:
				ret.append('%s%s\t%s' % (line_prefix, 'State %d:' % index if index != None else '        ', statestr))
		return ret
		
	def string(self, line_prefix = "", short_states=False):
		strns = self.strings()
		if strns:
			return '\n'.join(strns)
		else:
			return '<empty counter-example>'
		
	def __str__(self):
		return self.string()

if __name__ == '__main__':
	from fractions import Fraction
	import expressions
	class X:
		pass
	cs = X()
	cs.yi = X()
	cs.yi.vnames = ['a','b','c','d','e']
	cs.clockcount = 0
	cs.clockmax = []
	cs.diffmax = []
	cs.varcount = len(cs.yi.vnames)
	cs.yi.vtype_ids = [TYPE_BOOLEAN,] * cs.varcount
	cs.yi.vtypes = [expressions.BOOLEAN] * cs.varcount
	cs.constants = []
	cs.INT_FRAC_SPLIT = False
	s = State([True,False,True,False], False, cs)
	print s
	
	c1 = s.literals()
	print c1
	print
	
	cmax = [3, 3, 4]
	cdiffmax = [[None, None, 1   ],
	            [None, None, 4   ],
	            [1,    4,    None]]
	
	cs = X()
	cs.yi = X()
	cs.yi.vnames = ['c1', 'c2', 'c3', 'a', 'b']
	cs.yi.vtype_ids = [TYPE_CLOCK, TYPE_CLOCK, TYPE_CLOCK, TYPE_BOOLEAN, TYPE_BOOLEAN]
	cs.yi.vtypes = [expressions.REAL, expressions.REAL, expressions.REAL, expressions.BOOLEAN, expressions.BOOLEAN]
	cs.clockcount = 3
	cs.clockmax = cmax
	cs.diffmax = cdiffmax
	cs.varcount = len(cs.yi.vnames)
	cs.constants = []
	cs.INT_FRAC_SPLIT = False
	
	def _dbg_lit(s, expct):
		print s
		print repr(s.literals())
		print expct
		print s.literals()
		print
	print "max:", ", ".join(map(str, cmax))
	print
	s1 = State([Fraction(9, 4), Fraction(4, 3), Fraction(5, 1), True, False, Fraction(9, 4), Fraction(4, 3), Fraction(4, 1), True, False], False, cs)
	_dbg_lit(s1, '!a | b | c1 >= 3 | c2 >= 2 | c1 >= c2 + 1 | c1 >= c3 - 1 | c2 >= c1 | c2 >= c3 - 2')
	s2 = State([Fraction(8, 4), Fraction(4, 3), Fraction(5, 1), True, False, Fraction(9, 4), Fraction(4, 3), Fraction(4, 1), True, False], False, cs)
	_dbg_lit(s2, '!a | b | c1 > 2 | c2 >= 2 | c1 >= c2 + 1 | c1 >= c3 - 2 | c2 >= c1 | c2 >= c3 - 2')
	s3 = State([Fraction(9, 4), Fraction(4, 3), Fraction(1, 1), True, False, Fraction(9, 4), Fraction(4, 3), Fraction(4, 1), True, False], False, cs)
	_dbg_lit(s3, '!a | b | c1 >= 3 | c2 >= 2 | c3 > 1 | c1 >= c2 + 1 | c1 >= c3 + 2 | c2 >= c1 | c2 >= c3 + 1 | c3 >= c1 - 1 | c3 >= c2')
	s4 = State([Fraction(900, 4), Fraction(7, 3), Fraction(4, 3), True, False, Fraction(9, 4), Fraction(4, 3), Fraction(4, 1), True, False], False, cs)
	_dbg_lit(s4, '!a | b | c2 >= 3 | c3 >= 2 | c2 >= c1 | c2 > c3 + 1 | c3 >= c1 - 1 | c3 > c2 - 1')
	
	#p1.x=5/2	p2.x=2
	ct = X()
	ct.yi = X()
	ct.yi.vnames = ['p1.x', 'p2.x']
	ct.yi.vtype_ids = [TYPE_CLOCK, TYPE_CLOCK]
	ct.yi.vtypes = [expressions.REAL, expressions.REAL]
	ct.clockcount = 2
	ct.clockmax = [2, 2]
	ct.diffmax = [[None] * 2] * 2
	ct.varcount = len(ct.yi.vnames)
	t1 = State([Fraction(5, 2), 2], False, ct)
	print t1
	print t1.literals()
	print 'p2.x > 2 | p2.x >= p1.x'
	t1 = State([Fraction(5, 2), Fraction(3, 2)], False, ct)
	print t1
	print t1.literals()
	print 'p2.x >= 2 | p2.x >= p1.x'
	
	print '-' * 80
	cl = s4.literals()
	import byices, expressions
	
	yi = byices.Yices('y.txt')
	for i in xrange(len(cs.yi.vnames)):
		yi.add_var(cs.yi.vnames[i], expressions.BOOLEAN if cs.yi.vtype_ids[i] == TYPE_BOOLEAN else expressions.REAL)
	
	print 'Encoding', '!', '(', cl, ')', 'to y.txt...'
	encs = []
	cl.encode_lits(yi, False, False, encs)
	enc = encs[0].mk_and(encs[1:])
	yi.assertion(enc)
	print yi.check()
	print yi.get_model()
	
	print 'Encoding', cl, 'to y.txt...'
	encs = []
	cl.encode_lits(yi, True, False, encs)
	enc = encs[0].mk_or(encs[1:])
	yi.assertion(enc)
	print yi.check()
	
	print '-' * 80
	c2 = s4.literals()
	s5 = State([3.1, 3, 2, False, False, Fraction(9, 4), Fraction(4, 3), Fraction(4, 1), True, False], False, cs)
	print 'Dropping literals satisfied by', s5, 'from', c2
	c2.drop_lits_satisfied_by(s5)
	print 'Should be', 'b | c2 - c1 >= 0 | c2 - c3 > 1 | c3 - c1 >= -1 | c3 - c2 > -1'
	print 'Is       ', c2
	print
	print 'Repr:', repr(c2)
	print 'Dropping None elements'
	c2.drop_nones()
	print 'Repr:', repr(c2)
	print 'Clause:  ', c2
	
	print '-' * 80
	c1 = s1.literals()
	c2 = s2.literals()
	c3 = s3.literals()
	c4 = s4.literals()
	c5 = s5.literals()
	cls = [c1, c2, c3, c4, c5]
	print '\n'.join(map(str, cls))
	print
	expected = [[True,  False, True , False, False], ### WARNING: PROBABLY WRONG
	            [True,  True,  True , False, False],
	            [False, False, True,  False, False],
	            [False, False, False, True,  False],
	            [False, False, False, False, True ]]
	for i in xrange(len(cls)):
		for j in xrange(len(cls)):
			res = cls[i].subsumes(cls[j])
			print i, j, res, expected[i][j]
			assert res == expected[i][j] 
	
	print '-' * 80
	c6 = Clause(cs.varcount, cs.yi.vnames)
	c6.append((0, 2, True))
	c6.num_clock_lits = 1
	c6.append((0, 1, 2, True))
	c6.num_diff_lits = 1
	
	c7 = copy.copy(c6)
	c7[0] = (0, 2, False)
	
	c8 = copy.copy(c6)
	c8[1] = (0, 1, 2, False)
	
	c9 = copy.copy(c6)
	c9[0] = (0, 2, False)
	c9[1] = (0, 1, 2, False)
	
	cls = [c6, c7, c8, c9]
	print '\n'.join(map(str, cls))
	print
	expected = [[True,  False, False, False],
	            [True , True,  False, False],
	            [True , False, True,  False],
	            [True , True , True , True ]]
	for i in xrange(len(cls)):
		for j in xrange(len(cls)):
			res = cls[i].subsumes(cls[j])
			print i, j, res, expected[i][j]
			assert res == expected[i][j] 
	
	print '-' * 80

