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






import sys, os

import ply.lex as lex

import expressions

class ParsingException(Exception):
	def __init__(self, whathappened, value, valuetype, lineno, lexpos, data):	
		PRINT_AROUND = 3
		prevnlpos = data.rfind("\n", 0, lexpos)
		col = lexpos - prevnlpos
	
		lines = data.split("\n")
		msg = "%s in line %d in column %d at %s %s:\n" % (whathappened, lineno, col, valuetype, repr(value))
		line = max(lineno - 1, 0)
		if line - PRINT_AROUND > 0:
			msg += "...\n"
		before = lines[max(0, line - PRINT_AROUND) : line]
		if before:
			for l in before:
				msg += l + "\n"
		msg += lines[line]
		marker = []
		for i in xrange(col - 1):
			assert i < len(lines[line])
			if lines[line][i] == '\t':
				marker.append('\t')
			else:
				marker.append(' ')
		marker = ''.join(marker) + ('^' * len(str(value)))
		msg += "\n" + marker
		after = lines[line + 1 : line + 1 + PRINT_AROUND]
		if after:
			for l in after:
				msg += "\n" + l
		if line + PRINT_AROUND < len(lines):
			msg += "\n..."
		Exception.__init__(self, msg)

IDENTIFIER_FIRST = r'A-Za-z_'
IDENTIFIER_CONSECUTIVE = r'-.0-9$#' + IDENTIFIER_FIRST
IDENTIFIER = r'[%s][%s]*' % (IDENTIFIER_FIRST, IDENTIFIER_CONSECUTIVE)

DIGIT = r'[0-9]'

RESERVED = ["MODULE", "DEFINE", "MDEFINE", "CONSTANTS", "VAR", "IVAR", "FROZENVAR",
"INIT", "TRANS", "INVAR", "SPEC", "CTLSPEC", "LTLSPEC", "PSLSPEC", "COMPUTE",
"NAME", "INVARSPEC", "FAIRNESS", "JUSTICE", "COMPASSION", "ISA", "ASSIGN",
"CONSTRAINT", "SIMPWFF", "CTLWFF", "LTLWFF", "PSLWFF", "COMPWFF", "IN", "MIN",
"MAX", "MIRROR", "PRED", "PREDICATES", "process", "array", "of", "boolean",
"integer", "real", "word", "word1", "bool", "signed", "unsigned", "extend",
"resize", "sizeof", "uwconst", "swconst", "EX", "AX", "EF", "AF", "EG", "AG", "E", "F", "O", "G",
"H", "X", "Y", "Z", "A", "U", "S", "V", "T", "BU", "EBF", "ABF", "EBG", "ABG", "case", "esac", "mod", "next",
"init", "union", "in", "xor", "xnor", "self", "TRUE", "FALSE", "count",
"toint", #Added toint
"URGENT"#TIME
]


TWO_CHARACTER_OPERANDS = [
("..", "op_dotdot"),
("->", "op_imply"),
("<->", "op_equiv"),
("!=", "op_neq"),
("<=", "op_leq"),
(">=", "op_geq"),
(">>", "op_rshift"),
("<<", "op_lshift"),
("::", "op_coloncolon"),
(":=", "op_assign")
]


tokens = [
#General
"word_constant",
"integer_number",
"identifier",
'boolean_constant',
#"COMMENT",
] + RESERVED + [c[1] for c in TWO_CHARACTER_OPERANDS]


#Dictionaries
RESERVED_DICT = {}
for r in RESERVED:
	RESERVED_DICT[r] = r
RESERVED_DICT['TRUE']  = 'boolean_constant'
RESERVED_DICT['FALSE'] = 'boolean_constant'

def t_COMMENT(t):
	r'--.*\n'
	t.lexer.lineno += 1

TWO_CHARACTER_OPERANDS_DICT = {}
for (k, v) in TWO_CHARACTER_OPERANDS:
	TWO_CHARACTER_OPERANDS_DICT[k] = v


#tokens


def t_word_constant(t):
	r'0[us]?[0-9]+[bBoOdDhH](_*[0-9A-Fa-f]+_*)+'
	return t

@lex.TOKEN(r'-?%s%s*' % (DIGIT, DIGIT))
def t_integer_number(t):
	t.value = expressions.Number(int(t.value))
	return t


def t_error(t):
	raise ParsingException("Invalid character(s)", t.value[0], "character", t.lineno, t.lexpos, t.lexer.lexdata)

@lex.TOKEN(IDENTIFIER)
def t_identifier(t):
	t.type = RESERVED_DICT.get(t.value, "identifier")
	return t

@lex.TOKEN("|".join(x[0].replace(".", "\\.") for x in TWO_CHARACTER_OPERANDS))
def t_two_character_op(t):
	t.type = TWO_CHARACTER_OPERANDS_DICT[t.value]
	return t
	
literals = "[]();{},:=+-*/.!?&><|"
t_ignore = " \t"

def t_newline(t):
    r'\n+'
    t.lexer.lineno += len(t.value)

def _getfile():
	return __file__

_parsedir = os.path.join(os.path.split(_getfile())[0], "parserfiles")


import os
lexer = lex.lex(optimize=1)


if __name__ == "__main__":
	inf = open(sys.argv[1], "r")
	text = inf.read()
	inf.close()
	
	lexer.input(text)
	
	# Tokenize
	for tok in lexer:
	    print tok



