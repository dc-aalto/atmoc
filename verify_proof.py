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






PROOF_FILE_VERSION = 1

import sys, fileinput, re, fractions
import nusmv_yacc, colors, preproc, expressions, byices

VIOLATED_RET_CODE = 2

yifile = "y.txt"

NUM_RE = re.compile('(?P<num>\\d+)(/(?P<den>\\d+))?')

def primed(expr):
	assert isinstance(expr, expressions.Expression)
	ret = preproc.primed(variables, defdict, constants, expr, '')
	return ret

def should_be_unsat(exprs, satisfied_if_is=True):
	expected_sat_val(False, exprs, satisfied_if_is)

def expected_sat_val(expct, exprs, satisfied_if_is):
	yi = byices.Yices(yifile)
	for c in constants:
		yi.add_constant(c)
	def vc(a, b):
		if a.endswith(preproc.PRIME_SUFFIX) and not b.endswith(preproc.PRIME_SUFFIX):
			return 1
		elif a.endswith(preproc.PRIME_SUFFIX) and not b.endswith(preproc.PRIME_SUFFIX):
			return -1
		else:
			return cmp(a, b)
			
	for n in sorted(variables, cmp=vc):
		t = variables[n]
		yi.add_var(n, t)
	for n, e in definitions:
		yi.add_def(n, yi.encode(e))
	for ex in exprs:
		yi.assertion(yi.encode(ex))
	if expct != yi.check():
		if satisfied_if_is:
			sys.stdout.write(" ")
		print " " + colors.red("violated")
		print

		for ex in exprs:
			print ex
		print
		
		if not expct:
			for (k, v) in enumerate(yi.get_model()):
				print yi.vnames[k], v
		sys.exit(VIOLATED_RET_CODE)
	if satisfied_if_is:
		print colors.green("satisfied")
	else:
		sys.stdout.write(".")
		sys.stdout.flush()

def should_be_sat(exprs, satisfied_if_is=True):
	expected_sat_val(True, exprs, satisfied_if_is)

def verify_proof(clauses):
	print "Verifying proof consisting of", len(clauses), "clauses:"
	print "  Initiation ",
	for cl in clauses:
		should_be_unsat([init, expressions.AstExpression("!", cl)], False)
	print "", colors.green("satisfied")
	
	print "  Consecution",
	cls = expressions.reduce_to_ast_commutative("&", clauses, expressions.BooleanConstant(True))
	should_be_unsat([cls, trans, invar, primed(expressions.AstExpression("!", cls))])
	
	print "  Implies property",
	should_be_unsat([cls, nprop])

def cur_expr():
	try:
		[expr] = nusmv_yacc.expression_parser.parse(lines[lind])
		return expr
	except:
		print
		print '***', 'Line %d:' % lind, lines[lind], '***'
		print
		raise

def cur_clause_set():
	global lines, lind
	cnt = int(lines[lind])
	clauses = []
	for i in xrange(cnt):
		lind += 1
		cl = cur_expr()
		clauses.append(cl)
	return clauses

def cur_expr_set_conj():
	clauses = cur_clause_set()
	return expressions.reduce_to_ast_commutative('&', clauses, expressions.BooleanConstant(True))

clause_set_cnt = 0

def verify_clause_set(clauses, at_k):
	global init, clause_set_cnt
	assert not clauses[0]
	clauses[0] = [init]
	clause_set_cnt += 1
	print "Verifying clause set %s%s (%d sets, %d clauses)" % (clause_set_cnt, " (iteration)" if at_k else "", len(clauses), sum(len(x) for x in clauses))
	# (1) I => F_0
	# Essentially, this means that each clause has to be implied by I
	print "  I => F_0 ",
	for cset in clauses:
		for cl in cset:
			should_be_unsat([init, expressions.AstExpression("!", cl)], False)
	print "", colors.green("satisfied")
	
	# (2) F_i => F_i+1
	# Does not need any verification, syntactically true
	# The only special case is F_0 => F_1, but we already verified that in (1)
	
	# (3) F_i => P
	# Essentially, we only need to verify this for I, as P is implicitly member
	# of any other F_i
	print "  F_i => P",
	should_be_unsat([init, nprop])
	
	# (4) F_i and T => F_i+1'
	print "  F_i and T => F_i+1' ",
	for i in xrange(len(clauses) - 1):
		cur = reduce(list.__add__, clauses[i:]) + [prop, invar]
		for nxt in clauses[i+1] + ([] if (i + 1 == len(clauses) - 1 and not at_k) else [prop]):
			should_be_unsat(cur + [trans, expressions.AstExpression("!", primed(nxt))], False)
	print "", colors.green("satisfied")

def cur_state():
	st = lines[lind].split("\t")
	for i in xrange(len(st)):
		[k, v] = map(str.strip, st[i].split("="))
		k = expressions.AstExpression(k)
		if v.lower() in ["true", "false"]:
			v = expressions.BooleanConstant(v.lower() == 'true')
		elif v.lower() == "none":
			st[i] = None
			continue
		elif NUM_RE.match(v):
			m = NUM_RE.match(v)
			v = expressions.Number(int(m.group('num')))
			if m.group('den') != None:
				st[i] = expressions.AstExpression('=', ('*', k, expressions.Number(int(m.group('den')))), v)
				continue
		else:
			print lind, lines[lind]
			print i, st[i]
			print v
			raise Exception("Not yet")
		st[i] = expressions.AstExpression("=", k, v)
	return expressions.reduce_to_ast_commutative("&", [x for x in st if x != None], expressions.BooleanConstant(True))

def verify_counter_example(ce):
	print "Verifying %d state counter example " % len(ce)
	print "  Initial state",
	should_be_unsat([ce[0], expressions.AstExpression("!", init)])
	
	print "  Invariant ",
	for st in ce:
		should_be_unsat([st, expressions.AstExpression("!", invar)], False)
	print "", colors.green("satisfied")
	
	print "  Transitions ",
	for i in xrange(len(ce) - 1):
		should_be_sat([ce[i], primed(ce[i+1]), trans], False)
	print "", colors.green("satisfied")
	
	print "  Property violated",
	should_be_unsat([ce[-1], prop])

variables = {}
lind = 0

if __name__ == "__main__":
	lines = [line.strip() for line in fileinput.input()]
	lind = 0
	expected = "brind proof version %d" % PROOF_FILE_VERSION
	if lines[lind] != expected:
		raise Exception("WRONG VERSION")
	
	lind += 1
	assert lines[lind].startswith("DETAIL")
	
	lind += 1
	assert lines[lind] == "++ SYSTEM ++"

	lind += 1
	assert lines[lind] == "VARIABLES"

	lind += 1
	cnt = int(lines[lind])
	for i in xrange(cnt):
		lind += 1
		if lines[lind] == "BOOLEAN":
			tp = expressions.BOOLEAN
		elif lines[lind] == 'REAL':
			tp = expressions.REAL
		elif lines[lind] == 'RANGE':
			lind += 1
			low = int(lines[lind])
			lind += 1
			high = int(lines[lind])
			tp = expressions.Range(low, high)
		elif lines[lind] == 'ENUMERATION':
			lind += 1
			valcnt = int(lines[lind])
			vals = []
			for j in xrange(valcnt):
				lind += 1
				vals.append(lines[lind])
			tp = expressions.Enumeration(vals)
		else:
			raise Exception('Unsupported type: %s' % lines[lind])
		lind += 1
		variables[lines[lind]] = tp
	
	lind += 1
	lind += 1
	assert lines[lind] == 'DEFINITIONS', (lind, lines[lind])
	lind += 1
	cnt = int(lines[lind])
	definitions = []
	defdict = {}
	for i in xrange(cnt):
		lind += 1
		name = lines[lind]
		lind += 1
		expr = cur_expr()
		definitions.append((name, expr))
		defdict[name] = expr
	lind += 1
	
	lind += 1
	assert lines[lind] == 'CONSTANTS'
	lind += 1
	num = int(lines[lind])
	constants = []
	for i in xrange(num):
		lind += 1
		constants.append(lines[lind])
	lind += 1
	
	lind += 1
	assert lines[lind] == "INIT", (lind, lines[lind])
	lind += 1
	init = cur_expr_set_conj()
	lind += 1
	assert not lines[lind]
	
	lind += 1
	assert lines[lind] == "INVAR"
	lind += 1
	invar = cur_expr_set_conj()
	lind += 1
	assert not lines[lind]
		
	init = expressions.AstExpression('&', init, invar)
	
	lind += 1
	assert lines[lind] == "TRANS"
	lind += 1
	trans = cur_expr_set_conj()
	lind += 1
	assert not lines[lind]
	
	lind += 1
	assert lines[lind] == "PROP"
	lind += 1
	prop = cur_expr()
	nprop = expressions.AstExpression('!', prop)
	
#	lind += 1
#	assert lines[lind] == "NPROP", lines[lind]
#	lind += 1
#	nprop = cur_expr()
	
	lind += 1
	assert lines[lind] == "XPROP"
	lind += 1
	xprop = cur_expr()
	xnprop = expressions.AstExpression('!', xprop)
	
#	lind += 1
#	assert lines[lind] == "XNPROP"
#	lind += 1
#	xnprop = cur_expr()
	
	lind += 1
	assert not lines[lind]

	lind += 1
	while True:
		assert lines[lind].startswith("++")
		assert lines[lind].endswith("++")
		if lines[lind] == "++ CLAUSES %d ++" % (clause_set_cnt + 1) or lines[lind] == "++ CLAUSES %d K ++" % (clause_set_cnt + 1):
			at_k_increase = lines[lind] == "++ CLAUSES %d K ++" % (clause_set_cnt + 1)
			lind += 1
			assert "CLAUSE SET COUNT"
			lind += 1
			cnt = int(lines[lind])
			csets = []
			for i in xrange(cnt):
				lind += 1
				assert lines[lind] == "SET %d" % i
				lind += 1
				csets.append(cur_clause_set())
			verify_clause_set(csets, at_k_increase)
			lind += 1
		elif lines[lind] == "++ PROOF ++":
			lind += 1
			clauses = cur_clause_set()
			verify_proof(clauses)
		elif lines[lind] == "++ COUNTER EXAMPLE ++":
			lind += 1
			cnt = int(lines[lind])
			states = []
			for i in xrange(cnt):
				lind += 1
				states.append(cur_state())
			assert len(states) == cnt
			verify_counter_example(states)
			lind += 1
		elif lines[lind] == "++ END OF PARSER FRIENDLY PART ++":
			print "Skipping statistical information"
			break
		else:
			raise Exception("Invalid format: %d: %s" % (lind, lines[lind]))
		lind += 1
		print "%2.1f %%" % (float(lind) / len(lines) * 100.0),
print "100.0 %"

