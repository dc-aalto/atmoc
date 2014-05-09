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






#Productions that are not in the manual are prefixed with my_
#Productions related to time are prefixed with time_

import sys, os

from nusmv_lex import tokens, _getfile, ParsingException, _parsedir
import ply.yacc as yacc

from expressions import *
from nusmv_modules import *

start = "program"

def list_helper(p, element_pos = 2, extra_tokens=0):
	if len(p) == 2 + extra_tokens:
		p[0] = [p[1]]
	else:
		p[1].append(p[element_pos])
		p[0] = p[1]

def p_program(p):
	"""program : module_list
	           | my_unused"""
	assert p.slice[1].type == "module_list", repr(p.slice[1])
	p[0] = Program(p[1])

def p_module_list(p):
	'''module_list : module
	               | module_list module'''
	list_helper(p)

def p_module(p):
	'''module : MODULE identifier
	          | MODULE identifier '(' module_parameters ')'
	          | MODULE identifier '(' module_parameters ')' module_body
	          | MODULE identifier module_body'''
	name = p[2]
	if len(p) >= 5:
		params = p[4]
	else:
		params = []
	if len(p) >=  7:
		body = p[6]
	elif len(p) >= 4 and p.slice[3].type == "module_body":
		body = p[3]
	else:
		body = []
	p[0] = Module(name, params, body)

def p_module_parameters(p):
	'''module_parameters : identifier
                         | module_parameters ',' identifier'''
	list_helper(p, 3)

def p_module_body(p):
	'''module_body : module_element
		           | module_body module_element'''
	list_helper(p)

def p_module_element (p):
	'''module_element  : var_declaration
	                   | ivar_declaration
	                   | frozenvar_declaration
	                   | define_declaration
	                   | constants_declaration
	                   | assign_constraint
	                   | trans_constraint
	                   | init_constraint
	                   | invar_constraint
	                   | fairness_constraint
	                   | ctl_specification
	                   | rtctl_specification
	                   | invar_specification
	                   | ltl_specification
	                   | compute_specification
	                   | isa_declaration
	                   | urgent_constraint'''#TIME
	p[0] = p[1]

def p_var_declaration(p):
	'''var_declaration : VAR var_list
	                   | VAR
	   ivar_declaration : IVAR simple_var_list
	                    | IVAR
	   frozenvar_declaration : FROZENVAR simple_var_list
	                         | FROZENVAR''' #Empty var blocks are incorrect but tolerated by NuSMV (2.5)
	if len(p) == 3:
		p[0] = Variables(p[1], p[2])
	else:
		p[0] = Variables(p[1], [])

def p_var_list(p):
	"""var_list        : identifier ':' type_specifier ';'
                       | var_list identifier ':' type_specifier ';'
       simple_var_list : identifier ':' simple_type_specifier ';'
	                   | simple_var_list identifier ':' simple_type_specifier ';'"""
	if len(p) == 5:
		offset = 0
	else:
		assert len(p) == 6
		offset = 1
	item = (p[1 + offset], p[3 + offset])
	if offset:
		p[1].append(item)
		p[0] = p[1]
	else:
		p[0] = [item]

def p_type_specifier(p):
	"""type_specifier : simple_type_specifier
	                  | module_type_specifier"""
	p[0] = p[1]

def p_module_type_specifier(p):
	"""module_type_specifier : identifier
	                         | identifier '(' ')'
	                         | identifier '(' parameter_list ')'
	                         | process identifier 
	                         | process identifier '(' ')'
	                         | process identifier '(' parameter_list ')'"""
	if p.slice[1].type == "identifier":
		offset = 0
		process = False
	else:
		assert p.slice[1].type == "process"
		offset = 1
		process = True
	
	module = p[1 + offset]
	
	if len(p) - offset == 5:
		parameters = p[3 + offset]
	else:
		parameters = []
	
	p[0] = ModuleType(module, parameters, process)


def p_parameter_list(p):
	"""parameter_list : next_expr
	                  | parameter_list ',' next_expr"""
	list_helper(p, 3)

def p_simple_type_specifier(p):
	"""simple_type_specifier : boolean
                             | word '[' integer_number ']'
                             | unsigned word '[' integer_number ']'
                             | signed word '[' integer_number ']'
                             | '{' enumeration_type_body '}'
                             | integer_number op_dotdot integer_number
                             | array integer_number op_dotdot integer_number of simple_type_specifier"""
	if p[1] == "boolean":
		p[0] = Boolean()
	elif p[1] == "word":
		p[0] = Word(None, int(p[3]))
	elif p[1] in ["signed", "unsigned"]:
		p[0] = Word(p[1] == "signed", int(p[4]))
	elif p.slice[2].type == "enumeration_type_body":
		if all(isinstance(x, basestring) for x in p[2]):
			p[0] = Enumeration(p[2])
		elif all(isinstance(x, Number) for x in p[2]):
			p[0] = IntEnumeration(p[2])
		else:
			raise ParsingException('Parsing error: Mixed int / constant enumeration: {%s}' % ', '.join(map(str, p[2])), p.value, "token (type %s)" % p.type, p.lineno, p.lexpos, p.lexer.lexdata)
	elif p[1] == "array":
		p[0] = Array(int(p[2]), int(p[4]), p[6])
	else:
		assert p[2] == ".."
		p[0] = Range(p[1].value, p[3].value)


def p_enumeration_type_body(p):
	"""enumeration_type_body : enumeration_type_value
                             | enumeration_type_body ',' enumeration_type_value"""
	list_helper(p, 3)

def p_enumeration_type_value(p):
	'''enumeration_type_value : symbolic_constant
	                          | integer_number'''
	p[0] = p[1]

def p_assignments(p):
	"""define_declaration : DEFINE define_body
	                      | DEFINE
	   assign_constraint  : ASSIGN assign_list
	                      | ASSIGN""" #Empty assignment or define blocks are technically not correct but supported by NuSMV
	if len(p) == 3:
		lst = p[2]
	else:
		lst = []
	assert all(((el.modifier in ['init', 'next']) == (p[1] == 'ASSIGN')) for el in lst)
	assert all((el.modifier in [None, 'init', 'next']) for el in lst)
	p[0] = AssignmentList(p[1], lst)

def p_define_body(p):
	"""define_body : identifier op_assign simple_expr ';'
                   | define_body identifier op_assign simple_expr ';'"""
	if len(p) == 5:
		p[0] = [Assignment(p[1], p[3])]
	else:
		p[1].append(Assignment(p[2], p[4]))
		p[0] = p[1]

def p_assign_list(p):
	"""assign_list : assign ';'
                   | assign_list assign ';'"""
	list_helper(p, 2, 1)

def p_assign(p):
	'''assign : init '(' complex_identifier ')' op_assign simple_expr
              | next '(' complex_identifier ')' op_assign next_expr'''
#	"""assign : complex_identifier op_assign simple_expr
#              | init '(' complex_identifier ')' op_assign simple_expr
#              | next '(' complex_identifier ')' op_assign next_expr"""
	if len(p) == 4:
		p[0] = Assignment(p[1], p[3])
	else:
		p[0] = Assignment(p[3], p[6], p[1])
		

def p_constants_declaration(p):
	"""constants_declaration : CONSTANTS constants_body ';'"""
	p[0] = Constants(p[2])

def p_constraint(p):
	"""init_constraint     : INIT simple_expr
	                       | INIT simple_expr ';'
	   invar_constraint    : INVAR simple_expr
	                       | INVAR simple_expr ';'
	   trans_constraint    : TRANS next_expr
	                       | TRANS next_expr ';'
	   fairness_constraint : FAIRNESS simple_expr
	                       | FAIRNESS simple_expr ';'
	                       | JUSTICE simple_expr
	                       | JUSTICE simple_expr ';'
	                       | COMPASSION '(' simple_expr ',' simple_expr ')'
	                       | COMPASSION '(' simple_expr ',' simple_expr ')' ';'
	   urgent_constraint   : URGENT simple_expr
	                       | URGENT simple_expr ';'"""#TIME
	if(p[1] == "COMPASSION"):
		p[0] = CompassionConstraint(p[3], p[5])
	else:
		typ = p[1]
		if typ == "FAIRNESS":
			typ = "JUSTICE"
		p[0] = Constraint(typ, p[2])

def p_specification(p):
	"""invar_specification    : INVARSPEC next_expr
	                          | INVARSPEC next_expr ';'
	                          | INVARSPEC NAME my_name op_assign next_expr
	                          | INVARSPEC NAME my_name op_assign next_expr ';'
	   ltl_specification      : LTLSPEC ltl_expr
	                          | LTLSPEC ltl_expr ';'
	                          | LTLSPEC NAME my_name op_assign ltl_expr
	                          | LTLSPEC NAME my_name op_assign ltl_expr ';'
	   ctl_specification      : CTLSPEC ctl_expr
	                          | CTLSPEC ctl_expr ';'
	                          | SPEC ctl_expr
	                          | SPEC ctl_expr ';'
	                          | CTLSPEC NAME my_name op_assign ctl_expr
	                          | CTLSPEC NAME my_name op_assign ctl_expr ';'
	                          | SPEC NAME my_name op_assign ctl_expr
	                          | SPEC NAME my_name op_assign ctl_expr ';'
	   rtctl_specification    : CTLSPEC rtctl_expr
	                          | CTLSPEC rtctl_expr ';'
	                          | SPEC rtctl_expr
	                          | SPEC rtctl_expr ';'
	                          | CTLSPEC NAME my_name op_assign rtctl_expr
	                          | CTLSPEC NAME my_name op_assign rtctl_expr ';'
	                          | SPEC NAME my_name op_assign rtctl_expr
	                          | SPEC NAME my_name op_assign rtctl_expr ';'
	   compute_specification  : COMPUTE compute_expr
	                          | COMPUTE compute_expr ';'
	                          | COMPUTE NAME my_name op_assign compute_expr
	                          | COMPUTE NAME my_name op_assign compute_expr ';'
	                          | COMPUTE"""
	typ = p[1]
	if typ == "SPEC":
		typ = "CTLSPEC"
	if len(p) < 5:
		p[0] = Specification(typ, None, p[2])
	else:
		p[0] = Specification(typ, p[3], p[5])

def p_isa_declaration(p):
	"""isa_declaration : ISA identifier"""
	p[0] = IsaDeclaration(p[2])

def p_compute_expr(p):
	"""compute_expr : MIN '[' rtctl_expr ',' rtctl_expr ']'
	                | MIN '[' rtctl_expr ',' ctl_expr ']'
	                | MIN '[' ctl_expr ',' rtctl_expr ']'
	                | MIN '[' ctl_expr ',' ctl_expr ']'
	                | MAX '[' rtctl_expr ',' rtctl_expr ']'
	                | MAX '[' rtctl_expr ',' ctl_expr ']'
	                | MAX '[' ctl_expr ',' rtctl_expr ']'
	                | MAX '[' ctl_expr ',' ctl_expr ']'"""
	p[0] = AstExpression(p[1], p[3], p[5])

def p_rtctl_expr(p):
	"""rtctl_expr : EBF range rtctl_expr
	              | EBF range ctl_expr
	              | ABF range rtctl_expr
	              | ABF range ctl_expr
	              | EBG range rtctl_expr
	              | EBG range ctl_expr
	              | ABG range rtctl_expr
	              | ABG range ctl_expr
	              | A '[' rtctl_expr BU range rtctl_expr ']'
	              | A '[' rtctl_expr BU range ctl_expr ']'
	              | A '[' ctl_expr BU range rtctl_expr ']'
	              | A '[' ctl_expr BU range ctl_expr ']'
	              | E '[' rtctl_expr BU range rtctl_expr ']'
	              | E '[' rtctl_expr BU range ctl_expr ']'
	              | E '[' ctl_expr BU range rtctl_expr ']'
	              | E '[' ctl_expr BU range ctl_expr ']'"""
	#Altered: has to have at least one RTCTL operator
	if p.slice[1].type == "ctl_expr":
		p[0] = p[1]
	elif len(p) == 4:
		p[0] = AstExpression(p[1], p[2], p[3])
	else:
		p[0] = AstExpression(p[1] + p[4], p[5], p[3], p[6])


def p_ltl_expr(p):
	"""ltl_expr : basic_expr
	            | my_ltl_expr"""
	p[0] = p[1]

def p_my_ltl_expr(p):
	"""my_ltl_expr : '(' my_ltl_expr ')'
	               | '!' my_ltl_expr
	               | my_ltl_expr '&'  my_ltl_expr
	               | my_ltl_expr '&'  basic_expr
	               | basic_expr  '&'  my_ltl_expr
	               | my_ltl_expr '|'  my_ltl_expr
	               | my_ltl_expr '|'  basic_expr
	               | basic_expr  '|'  my_ltl_expr
	               | my_ltl_expr xor  my_ltl_expr
	               | my_ltl_expr xor  basic_expr
	               | basic_expr  xor  my_ltl_expr
	               | my_ltl_expr xnor my_ltl_expr
	               | my_ltl_expr xnor basic_expr
	               | basic_expr  xnor my_ltl_expr
	               | my_ltl_expr op_imply my_ltl_expr
	               | my_ltl_expr op_imply basic_expr
	               | basic_expr  op_imply my_ltl_expr
	               | my_ltl_expr op_equiv my_ltl_expr
	               | my_ltl_expr op_equiv basic_expr
	               | basic_expr  op_equiv my_ltl_expr
	               | X my_ltl_expr
	               | X basic_expr
	               | G my_ltl_expr
	               | G basic_expr
	               | F my_ltl_expr
	               | F basic_expr
	               | my_ltl_expr U my_ltl_expr
	               | my_ltl_expr U basic_expr
	               | basic_expr  U my_ltl_expr
	               | basic_expr  U basic_expr
	               | my_ltl_expr V my_ltl_expr
	               | my_ltl_expr V basic_expr
	               | basic_expr  V my_ltl_expr
	               | basic_expr  V basic_expr
	               | Y my_ltl_expr
	               | Y basic_expr
	               | Z my_ltl_expr
	               | Z basic_expr
	               | H my_ltl_expr
	               | H basic_expr
	               | O my_ltl_expr
	               | O basic_expr
	               | my_ltl_expr S my_ltl_expr
	               | my_ltl_expr S basic_expr
	               | basic_expr  S my_ltl_expr
	               | basic_expr  S basic_expr
	               | my_ltl_expr T my_ltl_expr
	               | my_ltl_expr T basic_expr
	               | basic_expr  T my_ltl_expr
	               | basic_expr  T basic_expr"""
	if p[1] in ["X", "G", "F", "Y", "Z", "H", "O"]:
		p[0] = AstExpression(p[1], p[2])
	elif p[2] in ["U", "V", "S", "T"]:
		p[0] = AstExpression(p[2], p[1], p[3])
	else:
		p_basic_expr(p)

def p_ctl_expr(p):
	#Altered: my_ltl_expr contains at least one LTL operator
	"""ctl_expr : basic_expr
	            | my_ctl_expr"""
	p[0] = p[1]

def p_my_ctl_expr(p):
	"""my_ctl_expr : '(' my_ctl_expr ')'
	               | '!' my_ctl_expr
	               | my_ctl_expr '&' my_ctl_expr
	               | my_ctl_expr '&' basic_expr
	               | basic_expr  '&' my_ctl_expr
	               | my_ctl_expr '|' my_ctl_expr
	               | my_ctl_expr '|' basic_expr
	               | basic_expr  '|' my_ctl_expr
	               | my_ctl_expr xor  my_ctl_expr
	               | my_ctl_expr xor  basic_expr
	               | basic_expr  xor  my_ctl_expr
	               | my_ctl_expr xnor my_ctl_expr
	               | my_ctl_expr xnor basic_expr
	               | basic_expr  xnor my_ctl_expr
	               | my_ctl_expr op_imply my_ctl_expr
	               | my_ctl_expr op_imply basic_expr
	               | basic_expr  op_imply my_ctl_expr
	               | my_ctl_expr op_equiv my_ctl_expr
	               | my_ctl_expr op_equiv basic_expr
	               | basic_expr  op_equiv my_ctl_expr
	               | EG my_ctl_expr
	               | EG basic_expr
	               | EX my_ctl_expr
	               | EX basic_expr
	               | EF my_ctl_expr
	               | EF basic_expr
	               | AG my_ctl_expr
	               | AG basic_expr
	               | AX my_ctl_expr
	               | AX basic_expr
	               | AF my_ctl_expr
	               | AF basic_expr
	               | E '[' my_ctl_expr U my_ctl_expr ']'
	               | E '[' my_ctl_expr U basic_expr  ']'
	               | E '[' basic_expr  U my_ctl_expr ']'
	               | E '[' basic_expr  U basic_expr  ']'
	               | A '[' my_ctl_expr U my_ctl_expr ']'
	               | A '[' my_ctl_expr U basic_expr  ']'
	               | A '[' basic_expr  U my_ctl_expr ']'
	               | A '[' basic_expr  U basic_expr  ']'"""
	if p[1] in ["EX", "AX", "EF", "AF", "EG", "AG"]:
		p[0] = AstExpression(p[1], p[2])
	elif len(p) == 7 and p[4] == "U":
		p[0] = AstExpression(p[1] + p[4], p[3], p[5])
	else:
		p_basic_expr(p)

def p_my_name(p):
	"""my_name : identifier"""
	p[0] = p[1]

def p_constants_body(p):
	"""constants_body : identifier
                      | constants_body ',' identifier"""
	list_helper(p, 3)


def p_next_expr(p):
	"""next_expr : basic_expr"""
	p[0] = p[1]

def p_basic_expr_list(p):
	"""basic_expr_list : basic_expr
	                   | basic_expr_list ',' basic_expr"""
	list_helper(p, 3)


def p_set_body_expr(p):
	'''set_body_expr : basic_expr
	                 | set_body_expr ',' basic_expr'''
	list_helper(p, 3)

def p_case_expr(p):
	"case_expr : case case_body esac"
	p[0] = CaseExpression(p[2])

def p_case_body(p):
	"""case_body : basic_expr ':' basic_expr ';'
	             | case_body basic_expr ':' basic_expr ';'"""
	if len(p) == 5:
		p[0] = [(p[1], p[3])]
	else:
		p[1].append((p[2], p[4]))
		p[0] = p[1]


def p_basic_next_expr(p):
	"""basic_next_expr : next '(' basic_expr ')'"""
	p[0] = AstExpression(p[1], p[3])

def p_complex_identifier(p):
	"""complex_identifier : identifier
                          | complex_identifier '.' identifier
                          | complex_identifier '[' simple_expr ']'
                          | self"""
	if len(p) == 2:
		p[0] = p[1]
	elif len(p) == 4:
		p[0] = p[1] + p[2] + p[3]
	else:
		p[0] = p[1] + p[2] + p[3] + p[4]

def p_simple_expr(p):
	"""simple_expr : basic_expr"""
	p[0] = p[1]

def p_basic_expr(p):
	'''basic_expr : boolean_constant
	              | integer_constant
	              | word_constant
	              | range_constant
	              | identifier
	              | '(' basic_expr ')'
	              | '!' basic_expr
	              | basic_expr '&' basic_expr
	              | basic_expr '|' basic_expr
	              | basic_expr xor basic_expr
	              | basic_expr xnor basic_expr
	              | basic_expr op_imply basic_expr
	              | basic_expr op_equiv basic_expr
	              | basic_expr '=' basic_expr
	              | basic_expr op_neq basic_expr
	              | basic_expr '<' basic_expr
	              | basic_expr '>' basic_expr
	              | basic_expr op_leq basic_expr
	              | basic_expr op_geq basic_expr
	              | '-' basic_expr %prec my_uminus
	              | basic_expr '+' basic_expr
	              | basic_expr '-' basic_expr
	              | basic_expr '*' basic_expr
	              | basic_expr '/' basic_expr
	              | basic_expr mod basic_expr
	              | toint '(' basic_expr ')'
	              | count '(' basic_expr_list ')'
	              | basic_expr '?' basic_expr ':' basic_expr %prec my_qmop
	              | case_expr
	              | basic_next_expr'''
# Deactivated :
#	              | word1 '(' basic_expr ')'
#	              | bool '(' basic_expr ')'
#	              | '{' set_body_expr '}'
#	              | basic_expr op_rshift basic_expr
#	              | basic_expr op_lshift basic_expr
#	              | basic_expr '[' my_index ']'
#	              | basic_expr '[' basic_expr ':' basic_expr ']'
#	              | basic_expr op_coloncolon basic_expr
#	              | swconst '(' basic_expr ',' basic_expr ')'
#	              | uwconst '(' basic_expr ',' basic_expr ')'
#	              | signed '(' basic_expr ')'
#	              | unsigned '(' basic_expr ')'
#	              | sizeof '(' basic_expr ')'
#	              | extend '(' basic_expr ',' basic_expr ')'
#	              | resize '(' basic_expr ',' basic_expr ')'
#	              | basic_expr union basic_expr
#	              | basic_expr in basic_expr
	if p.slice[1].type in ["basic_next_expr", "case_expr"]:
		#Simple stuff
		p[0] = p[1]
	elif p.slice[1].type == 'boolean_constant':
		p[0] = BooleanConstant(p[1] == 'TRUE')
	elif p.slice[1].type == "integer_constant":
		p[0] = p[1]
	elif p.slice[1].type in ["identifier", "word_constant"]:
		#Constant
		p[0] = AstExpression(p[1])
	elif p.slice[1].type == "range_constant":
		p[0] = p[1]
	elif p[1] == "(":
		#Parenthesis
		p[0] = p[2]
	elif p[1] in ["!", "-"]:
		#Unary operators
		p[0] = AstExpression(p[1], p[2])
	elif p[2] in ["&", "|", "xor", "xnor", "->", "<->", "=", "!=", "<", ">", "<=", ">=", "+", "-", "*", "/", "mod", ">>", "<<", "::", "union", "in"]:
		#Binary operators
		p[0] = AstExpression(p[2], p[1], p[3])
	elif p[2] == "?":
		#Ternary operators
		p[0] = AstExpression("?:", p[1], p[3], p[5])
	elif p[2] == "(":
		#Function style
		if p[1] == "count":
			p[0] = AstExpression([p[1]] + p[3])
		elif len(p) >= 6:
			p[0] = AstExpression(p[1], p[3], p[5])
		else:
			p[0] = AstExpression(p[1], p[3])
	elif p[1] == '{':
		#Set Expression
		p[0] = AstExpression(["{}"] + p[2])
	else:
		assert p[2] == "["
		if len(p) == 5:
			p[0] = AstExpression("[]", p[1], p[3])
		else:
			p[0] = AstExpression("[:]", p[1], p[3], p[5])

def p_range_constant(p):
	"""range_constant : integer_number op_dotdot integer_number
	   range : integer_number op_dotdot integer_number"""
	p[0] = AstExpression(p[2], AstExpression(p[1]), AstExpression(p[3]))

def p_my_index(p):
	"""my_index : integer_number"""
	p[0] = AstExpression(p[1])

def p_redirection(p):
	"""integer_constant : integer_number
	   symbolic_constant : identifier"""
	p[0] = p[1]

#def p_boolean_const(p):
#	'''boolean_const : FALSE
#	                 | TRUE'''
#	p[0] = p[1]


def p_my_unused(p):
	"""my_unused : integer
	             | real
	             | SIMPWFF
	             | MDEFINE
	             | LTLWFF
	             | PRED
	             | CTLWFF
	             | COMPWFF
	             | PSLWFF
	             | MIRROR
	             | CONSTRAINT
	             | PREDICATES
	             | IN
	             | PSLSPEC""" #currently not in use
	raise SyntaxError("Unused reserved identifier: " + p.value)

def p_error(p):
	if p != None:
		raise ParsingException("Parsing error", p.value, "token (type %s)" % p.type, p.lineno, p.lexpos, p.lexer.lexdata)
	else:
		raise ParsingException("Parsing error", "", "file end", -1, -1, "")

precedence = [
("right", "op_imply"),
("left", "op_equiv"),
("left", "my_qmop"),
("left", "|", "xor", "xnor"),
("left", "&"),
("left", "=", "op_neq", "<", ">", "op_leq", "op_geq"),
("left", "U", "V", "S", "T"),
("left", "AX", "AG", "AF", "EX", "EG", "EF", "X", "G", "F", "Y", "Z", "H", "O"),
("left", "in"),
("left", "union"),
("left", "op_lshift", "op_rshift"),
("left", "+", "-"),
("left", "*", "/", "mod"),
("left", "my_uminus"),
("left", "op_coloncolon"),
("left", "!"),
("left", "]")
]



__parsefile = "nusmv-parsetab"
if not _parsedir in sys.path:
	sys.path.append(_parsedir)

parser = yacc.yacc(outputdir=_parsedir, debugfile=os.path.join(_parsedir, "parser.out"), debug=(1 if __name__ == "__main__" else 0), optimize=1)
start = "basic_expr_list"
expression_parser = yacc.yacc(outputdir=_parsedir, debugfile=os.path.join(_parsedir, "parser.out"), debug=(1 if __name__ == "__main__" else 0), tabmodule="expr", optimize=1)

if __name__ == "__main__":
	inf = open(sys.argv[1], "r")	
	text = inf.read()
	inf.close()
	
	args = sys.argv[1:]
	
	try:
		result = parser.parse(text, )
		if "--flatten" in args:
			print "-- Flattening..."
			result.flatten(["clock"])
		if "--inline" in args or "--vinline" in args:
			varinline = "--vinline" in args
			print "-- Inlining..."
			if varinline:
				print "-- (Using variables)"
			for k in result.modules:
				result.modules[k].inline_definitions(varinline)
		if "--enum" in args:
			print "-- Getting rid of enums..."
			result.enums_to_ranges()
		
		if "--assign" in args:
			print "-- Removing ASSIGNs"
			result.remove_assigns()
		
		if "--names" in args:
			print result.string(True)
		else:
			print result
	except ParsingException, e:
		print "Parsing failed:"
		print "\n".join(e.args)
		sys.exit(1)

