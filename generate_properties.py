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






import sys, itertools, random
import expressions, nusmv_modules, nusmv_yacc, preproc

if __name__ == '__main__':
	args = sys.argv[1:]
	if not len(args) in [2, 3]:
		print 'Usage <file> <max-literals> [<max-number-of-properties>]'
		sys.exit(1)
	
	fn = args[0]
	num = int(args[1])
	num_generated = int(args[2]) if len(args) >= 3 else None
	
	# Parse model
	inf = open(fn, 'r')
	model = nusmv_yacc.parser.parse(inf.read())
	inf.close()
	(variable_dict, unprimed_vars, definition_vars),    \
			(definitions, transition_definitions),       \
			(initials, xinitials, transitions, invariants,\
			xinvariants, urgencies, resets, prop, xprop),  \
			orgspecs, clockmax = preproc.preprocess(model, True, False, 0, True, False, get_original_def_info=True)
		
	variables = []
	clocks = []
	for v, t in variable_dict.iteritems():
		if not v.endswith(preproc.PRIME_SUFFIX):
			if t == expressions.REAL:
				clocks.append(v)
			variables.append((v, t))
	
	for n, t in preproc.g_list_of_original_definitions.iteritems():
		if not v.endswith(preproc.PRIME_SUFFIX):
			if t == expressions.REAL:
				clocks.append(n)
			variables.append((n, t))
	
	sys.stderr.write('Found %d variables\n' % len(variables))
	
	# Generate literals
	literals = []
	
	for var, typ in variables:
		if typ == expressions.BOOLEAN:
			literals.append(var)
			literals.append(expressions.AstExpression('!', var))
		elif isinstance(typ, expressions.Range):
			for val in xrange(typ.low, typ.high + 1):
				literals.append(expressions.AstExpression('=', var, str(val)))
		elif isinstance(typ, (expressions.Enumeration, expressions.IntEnumeration)):
			for val in typ.values:
				literals.append(expressions.AstExpression('=', var, str(val)))
		elif var in clocks:
			literals.append(expressions.AstExpression('=',  var, '0'))
			literals.append(expressions.AstExpression('>',  var, '0'))
			literals.append(expressions.AstExpression('<=', var, str(clockmax[var])))
			literals.append(expressions.AstExpression('>',  var, str(clockmax[var])))
		else:
			sys.stderr.write('*** Unsupported type: %s ***' % str(typ))
	
	sys.stderr.write('Generated %d literals\n' % len(literals))
	
	# Generate specifications
	combs = []
	for i in xrange(1, num + 1):
		combs += itertools.combinations(literals, i)
	
	num_props = len(combs)
	if num_generated != None:
		combs = random.sample(combs, num_generated)
	
	for comb in combs:
		print 'INVARSPEC', ' | '.join(map(str, comb))
	
	sys.stderr.write('Generated %d properties\n' % num_props)
	if num_generated != None:
		sys.stderr.write('Selected %d properties\n' % len(combs))

