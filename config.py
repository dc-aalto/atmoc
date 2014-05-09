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





VERSION = "1.0"

import sys, time, getopt, random, os
import yicesfull, stats

##### Constants

VERBOSITY_NONE    = 0 # Level at which no verbose output is generated
VERBOSITY_DEFAULT = 0 # Default verbosity
VERBOSITY_MAX     = 5 # Max verbosity level
VERBOSITY_ANY     = 1 # Level starting from which any verbose output is generated

verbosity         = VERBOSITY_DEFAULT # Global verbosity level

DEFAULT_MAX_LIT_DROP_FAILURES = 3
DEFAULT_RESTART_RATION = 1000.0
DEFAULT_PROOF_DETAIL = 'final'

PROOF_DETAIL_FINAL  = 0
PROOF_DETAIL_K      = 1
PROOF_DETAIL_CLAUSE = 2

VALID_PROOF_DETAILS = {
	'final'  : PROOF_DETAIL_FINAL,
	'k'      : PROOF_DETAIL_K,
	'clause' : PROOF_DETAIL_CLAUSE
}

RETVAL_USAGE = 2

##### Argument parsing - helpers

def __goodbye(errmsg=None, retval=RETVAL_USAGE, mention_minus_h=True):
	if errmsg != None:
		sys.stderr.write(errmsg)
		sys.stderr.write('\n')
	if mention_minus_h:
		sys.stderr.write('Use -h for more information.\n')
	sys.exit(retval)

def __help():
	print  'Usage: %s [<options>] <input-file>\n' % os.path.split(sys.argv[0])[-1] +\
'''
Version %s
Options:
   -h or --help   : Show this screen and exit
   -v             : Show version and exit
   --lp           : List properties but do not check anything
   --cp           : Count properties and exit
   -n <num>       : Only check property number <num> (0-based in flattened file,
                    use --lp to find  out ids.
   -s             : Show statistical information.
   --yt           : Measure time spent by yices seperately
   --tr <file>    : Print statistical information in the form of a table row
                    (seperated by tabs) into a file
   --th <file>    : Write a table header for statistical information tables into
                    a file and exit. NO VERIFICATION PERFORMED!
   --non-trace-ce : Does not turn a found counter-example into an actual trace
                    of the system. I.e. counter-examples are sequences of states
                    such that there is a counter-example trace of the systems
                    that visits the same regions.
   --nochecks     : Assume convexity without checking; Skip type checks
   --def-vars:      New variables are created for definitions used in more
                    than on location. These variables are, however, not used in
                    clauses.
   --seed <num>:     Sets the random seed

Specific to IC3 algorithm:
   -d <num>       : Maximum number of unsuccesful literal drops. Default: %d
   -r <float>     : Restart ration. When the number of pushes is greater than
                    this ratio times the number ordinary variables, a fresh
                    yices is used. Default value: %f
   --non-lazy:      Actively exclude any bad state ever found, even if clauses
                    added since the states discovery have already excluded the
                    state.
   --proof <file>:  Write the final proof of the property into a file for
                    properties holding, or the system + counter example for a
                    property not holding
   --proof-detail <det>: Controls the detail given in the proof file. <det> can
                    be one of the following:
                      final:  Only the final proof / counter example is given
                      k:      The intermediate clauses are dumped every time k
                              is increased.
                      clause: Every time a clause is added, the intermediate
                              clauses are dumped.
                    The default setting is "%s". Needs to have a proof file
                    specified.
    --no-optimization-checks: Do not use optimization checks.
    --basic-regions: Use basic region definition

Temporal induction:
    --ind:           Use temporal induction
    --all-diseq:     Add disequality constraints for all pairs of states.
    --basic-regions: Use basic region definition

Bounded model checking
    -b <n>:         Incremental bounded model checking up to bound n

Further options, mostly intended for debugging:
   --short        : Print short states information
   -verbosity <v> : Sets the verbosity, values can range from %d (no verbose
                    output) to %d (full verbosity)
   -y <file>      : Dump Yices input to <file>''' % (VERSION, DEFAULT_MAX_LIT_DROP_FAILURES,
   		DEFAULT_RESTART_RATION, DEFAULT_PROOF_DETAIL, VERBOSITY_NONE, VERBOSITY_MAX)
	sys.exit(0)

##### Actual argument parsing
check_property = 0 #Currently only one property supported
yicesfile = None
nochecks = None
list_properties = False
short_states = False
check_alot = True
show_stats = False
avoid_drops = True
max_drop_lit_failures = DEFAULT_MAX_LIT_DROP_FAILURES
restart_ratio = DEFAULT_RESTART_RATION
def_vars = False
defs_in_clauses = False
expected_type = None
seed = long(time.time() * 256)
proof_file = None
proof_detail = VALID_PROOF_DETAILS[DEFAULT_PROOF_DETAIL]
non_trace_counter_example = False
table_row_file = None
verbosity = VERBOSITY_DEFAULT
filename = None
measure_yices_time = False
actvar_impl = False
interactive = False
simple_propagation = False
count_properties = False
type_check = True
bmc_bound = None
use_k_ind = False
all_diseq = False
basic_regions = False

def parse_command_line():
	global check_property, yicesfile, nochecks, list_properties, short_states, \
		check_alot, show_stats, avoid_drops, max_drop_lit_failures, filename,  \
		restart_ratio, def_vars, defs_in_clauses, verbosity, expected_type,    \
		seed, proof_file, proof_detail, table_row_file, measure_yices_time,    \
		non_trace_counter_example, actvar_impl, interactive, all_diseq,        \
		simple_propagation, count_properties, bmc_bound, use_k_ind,            \
		basic_regions
	
	# Command line args
	try:
		options, args = getopt.gnu_getopt(sys.argv[1:], 'hy:n:sd:r:ib:v',
				['lp', 'help', 'nochecks', 'verbosity=', 'basic-regions',
				 'no-optimization-checks', 'short', 'non-lazy',
				 'def-vars', 'def-clauses', 'seed=', 'proof-detail=',
				 'proof=', 'def-expr', 'tr=', 'th=', 'non-trace-ce', 'yt',
				 'act-impl', 'simple-propagation', 'cp', 'ind', 'all-diseq'])
	except getopt.GetoptError, e:
		__goodbye('Error: %s' % e.msg)
	
	for arg, val in options:
		try:
			if arg == '-h' or arg == '--help':
				__help()
			elif arg == '-v':
				print VERSION
				sys.exit(0)
			elif arg == '--basic-regions':
				basic_regions = True
			elif arg == '--all-diseq':
				all_diseq = True
			elif arg == '--non-trace-ce':
				non_trace_counter_example = True
			elif arg == '--seed':
				expected_type = 'integer'
				val = int(val)
				random.seed(val)
				yicesfull.seed(random.randint(0, 2**31-1))
				seed = val
			elif arg == '--def-clauses':
				def_vars = True
				defs_in_clauses = True
			elif arg == '-r':
				expected_type = 'float'
				val = float(val)
				if val <= 0:
					__goodbye('-r expects a positive fractional value')
				restart_ratio = val
			elif arg == '--proof':
				proof_file = val
			elif arg == '--proof-detail':
				if not val in VALID_PROOF_DETAILS:
					__goodbye('--proof-detail needs to be one of the following: %s' % ', '.join(VALID_PROOF_DETAILS))
				proof_detail = VALID_PROOF_DETAILS[val]
			elif arg == '-d':
				expected_type = 'integer'
				max_drop_lit_failures = int(val)
			elif arg == '--def-vars':
				def_vars = True
			elif arg == '-s':
				show_stats = True
			elif arg == '--tr':
				table_row_file = val
			elif arg == '--th':
				of = open(val, 'w')
				of.write('\t'.join(stats.table_header()))
				of.write('\n')
				of.close()
				sys.exit(0)
			elif arg == '-y':
				yicesfile = val
			elif arg == '--nochecks':
				nochecks = True
				type_check = False
			elif arg == '--lp':
				list_properties = True
			elif arg == '--cp':
				count_properties = True
			elif arg == '-n':
				expected_type = 'integer'
				check_property = int(val)
			elif arg == '--act-impl':
				actvar_impl = True
			elif arg == '-i':
				interactive = True
			elif arg == '--simple-propagation':
				simple_propagation = True
			elif arg == '--verbosity':
				verbosity = int(val)
				if verbosity > VERBOSITY_MAX:
					print '*** WARNING: The specified verbosity is higher then the maximum value of %d, which is used instead. ***\n'\
											% VERBOSITY_MAX
				if verbosity < VERBOSITY_NONE:
					print '*** WARNING: The specified verbosity is lower then the minimum value of %d, which is used instead. ***\n'\
											% VERBOSITY_NONE
			elif arg == '--short':
				short_states = True
			elif arg == '--no-optimization-checks':
				check_alot = False
			elif arg == '--non-lazy':
				avoid_drops = False
			elif arg == '--yt':
				measure_yices_time = True
				yicesfull.enable_time_measuring(True)
			elif arg == '-b':
				expected_type = 'positive int'
				bmc_bound = int(val)
				if bmc_bound <= 0:
					raise ValueError('negative')
			elif arg == '--ind':
				use_k_ind = True
			else:
				assert False, (arg, val)
		except ValueError:
			__goodbye('Invalid argument for %s -- expected %s' % (arg, expected_type))
	
	for a, b in [('def_vars', 'interactive'),
				('defs_in_clauses', 'interactive')]:
		if eval(a) and eval(b):
			__goodbye('Conflicting flags')
		
	if verbosity >= VERBOSITY_ANY:
		show_stats = True
	
	if not len(args) == 1:
		__goodbye('Invalid argument number')
		
	filename = args[0]

