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





from distutils.core import setup, Extension

module1 = Extension('yicesfull', sources = ['yicesfull.c'],
			library_dirs = ['.'], libraries = ['yices'],
			include_dirs=['.']
		)

setup (name = 'Yices C API wrapper',
       version = '0.1',
       description = 'Wrapper for the yices api',
       ext_modules = [module1],
       )

