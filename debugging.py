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





print
print
strn = '*** Using debugging module ***'
print ' ' * ((80 - len(strn)) / 2), strn
print
print

import inspect, atexit, os, sys, pdb


###### PROFILING 
calls_observed = {}

	
def trace(frame, event, arg):
    print "%s, %s:%d" % (event, frame.f_code.co_filename, frame.f_lineno)
    return trace

def observe(depth):
	if not calls_observed:
		sys.settrace(trace)
		atexit.register(save_observations)
	stk = inspect.stack()[1:1+depth]
	stk = [(os.path.split(x[1])[-1], x[2], x[3]) for x in stk]
	stk += [None,] * (depth - len(stk))
	stk = tuple(stk)
	calls_observed[stk] = calls_observed.get(stk, 0) + 1

def save_observations():
	if calls_observed:
		print
		print
		print 'PARTIAL PROFILE'
		for k in sorted(calls_observed, lambda x, y: cmp(tuple((xe[0], xe[2]) for xe in x), tuple((ye[0], ye[2]) for ye in y))):
			print hash(tuple(x[2] for x in k))
			print '%s\n%d' % ('\t'.join(reversed(map(lambda x : '%s:%d' % (x[2], x[1]), k))), calls_observed[k])
			print

###### Recursion detection
REC_WHITELIST = [
# These should be fine as they are not called with high depth during parsing
('expressions.py', '__new__'),
('expressions.py', '_to_ast_argument_list'),
('expressions.py', '_to_ast_operand'),
# These should result from decorated functions calling other decorated functions:
('preproc.py', 'actual_call'),
# These are used in two contexts: debugging (in which slowness is ok) and to print the properties (which in their original form should not be too large)
('expressions.py', 'string'),
('expressions.py', 'element_str')
]

def _rec_trace(frame, event, arg):
	if event != 'call':
		return
	stk = []
	cur = frame
	dns = []
	while cur != None:
		code = cur.f_code
		fn = code.co_filename
		dn, sfn = os.path.split(fn)
		name = code.co_name
		stk.append((sfn, code.co_firstlineno, name))
		dns.append(dn)
		cur = cur.f_back
	if os.path.abspath(dns[0]) == os.path.abspath(os.getcwd()): # only own code
		if (not (stk[0][0], stk[0][2]) in REC_WHITELIST) and stk[0] in stk[1:]:
			print '\n'.join('%s %d: %s' % x for x in reversed(stk))
			print
	return _rec_trace

def recursion_detection():
	sys.settrace(_rec_trace)

###### STDOUT debugging

notify_strns = []

class TW(object):
	def __init__(self, org):
		self.org = org
	def write(self, what):
		if any(x in what for x in notify_strns):
			raise Exception("here")
		self.org.write(what)
	def flush(self):
		self.org.flush()

def notify_stdout(strn):
	if not notify_strns:
		sys.stdout = TW(sys.stdout)
	notify_strns.append(strn)

###### Hit cnt bp

_dbg_hits = 0
def hit_bp(arg=None):
	global _dbg_hits
	_dbg_hits += 1
	print "Hit debug point", _dbg_hits
	if _dbg_hits == arg:
		pdb.set_trace()

###### Decorator

def PrintRet(func):
	def rf(*args):
		ret = func(*args)
		print 'return', ret
		return ret
	return rf


if __name__ == '__main__':
	def a():
		observe(2)
	
	def b():
		a()
		a()
	
	a()
	a()
	b()
	b()
	b()

