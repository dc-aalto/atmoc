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





import sys

def bold(s):
	return "\033[1m%s\033[0m" % str(s)

def gray(s):
	return '\033[30;1m%s\033[0m' % s

STARTRED = '\033[31;1m'
def red(s):
	return '%s%s%s' % (STARTRED, s, END)

STARTGREEN = '\033[32;1m'
def green(s):
	return '%s%s%s' % (STARTGREEN, s, END)
	
def yellow(s):
	return '\033[33;1m%s\033[0m' % s

def blue(s):
	return '\033[34;1m%s\033[0m' % s

def violet(s):
	return '\033[35;1m%s\033[0m' % s

def bright_blue(s):
	return '\033[36;1m%s\033[0m' % s

def white(s):
	return '\033[37;1m%s\033[0m' % s

def graybg(s):
	return '\033[40;1m%s\033[0m' % s

STARTREDBG = '\033[41;1m'
END = '\033[0m'
def redbg(s):
	return '%s%s%s' % (STARTREDBG, s, END)
	
def greenbg(s):
	return '\033[42;1m%s\033[0m' % s
	
def yellowbg(s):
	return '\033[43;1m%s\033[0m' % s

def bluebg(s):
	return '\033[44;1m%s\033[0m' % s

def violetbg(s):
	return '\033[45;1m%s\033[0m' % s

def bright_bluebg(s):
	return '\033[46;1m%s\033[0m' % s

def whitebg(s):
	return '\033[47;1m%s\033[0m' % s

def plain(s):
	"Removes all colors etc."
	while s.find("\033[") >= 0:
		pos = s.find("\033[")
		pos2 = s.find("m", pos)
		if pos2 >= 0:
			s = s[:pos] + s[pos2+1:]
	return s

def print_table(table, ignore_empty_columns=True, separator=" ", strm = sys.stdout):
	"Takes a list of list of table rows (which themselves are lists) and prints them in a way so that every entry in a column has the same width."
	assert isinstance(table, list)
	assert all(isinstance(x, list) for x in table)
	assert table
	assert any(x for x in table)
	
	width = [max(len(plain(row[i])) if len(row) > i else 0 for row in table) for i in xrange(max(len(row) for row in table))] #column widths
	if ignore_empty_columns:
		printed_columns = [i for i in xrange(len(width)) if width[i]]
	else:
		printed_columns = range(len(table))
	assert printed_columns
		
	for row in table:
		if row:
			actually_printed = [i for i in printed_columns if (i < len(row))]
			if actually_printed:
#				print width, len(width), printed_columns, map(plain, row)
				for i in actually_printed[:-1]:
					strm.write(row[i])
					strm.write(" " * (width[i] - len(plain(row[i]))))
					strm.write(separator)
				strm.write(row[actually_printed[-1]])
		strm.write("\n")

