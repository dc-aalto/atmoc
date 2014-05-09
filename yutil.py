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






from expressions import *
from byices import Yices
import preproc

D1N = "delta-1"
D2N = "delta-2"


@preproc.RewriteExpr(True, False, False)
def _conv_repl(surrounding, expr, prefix, is_def, variables, deltavar):
	assert not prefix
	assert not is_def
	assert isinstance(expr, AstExpression)
	assert len(expr) == 1
	assert isinstance(expr[0], basestring)
	assert expr[0] in variables
	if variables[expr[0]] == REAL:
		return AstExpression('+', expr, deltavar)

def is_convex(variables, constants, definitions, expr, yices_file=None):
	assert isinstance(expr, Expression)
	assert isinstance(variables, dict)
	assert all(isinstance(x, basestring) for x in variables)
	assert all(isinstance(x, Type) for x in variables.itervalues())
	assert isinstance(definitions, list)
	assert all(isinstance(x[0], basestring) for x in definitions)
	assert all(isinstance(x[1], Expression) for x in definitions)
	assert isinstance(expr, Expression)
	assert yices_file == None or isinstance(yices_file, basestring)
	
	defset = set(x[0] for x in definitions)
	
	# Preprocess
	xa =                    expr
	xb = AstExpression("!", _conv_repl(variables, defset, constants, expr, '', variables, AstExpression(D1N)))
	xc =                    _conv_repl(variables, defset, constants, expr, '', variables, AstExpression(D2N))
	
	# Set up yices
	yi = Yices(yices_file)
	for (i, c) in enumerate(constants):
		r = yi.add_constant(c)
		assert r == i
	clocks = []
	for n, t in variables.iteritems():
		yi.add_var(n, t)
		if t == REAL:
			clocks.append(n)
	for n, e in definitions:
		yi.add_def(n, yi.encode(e))
	yi.add_var(D1N, REAL)
	yi.add_var(D2N, REAL)
	
	for clk in clocks:
		expr = AstExpression(">=", clk, Number(0))
		yi.assertion(yi.encode(expr))
	
	yi.assertion(yi.encode(AstExpression(">", D1N, Number(0))))
	yi.assertion(yi.encode(AstExpression(">", D2N, D1N)))
	yi.assertion(yi.encode(xa))
	yi.assertion(yi.encode(xb))
	yi.assertion(yi.encode(xc))
	
	ret = not yi.check()
	
	return (ret, None if ret else yi.get_model())

if __name__ == "__main__":
	### DOES NOT WORK ANYMORE ###
	a = Variable("a", REAL)
	b = Variable("b", BOOLEAN)
	c = Variable("c", BOOLEAN)
	expr = AstExpression("&", b, ("|", (">", a, "4"), ("<", a, "5")))
	print expr, is_convex(expr, [a], "tmp/y1.txt")
		
	expr = AstExpression("&", b, ("|", (">", a, "4"), ("<", a, "2")))
	print expr, is_convex(expr, [a], "tmp/y2.txt")
	
	expr = AstExpression("<->", b, c)
	print expr, is_convex(expr, [], "tmp/y3.txt")

