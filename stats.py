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





import config
import yicesfull

TABLE_HEADER = ['Filename',
			'Property checked',
			'Property holds',
			'Counter-example length',
			'Started',
			'Yices version',
			'Seed',
			'k',
			'# Clauses',
			'Proof size',
			'Dropped clauses',
			'Equality drops',
			'Subsumption drops',
			'Queries',
			'Optimization queries',
			'Initiation queries',
			'Consecution queries',
			'Assertions',
			'Pushes',
			'Pops',
			'Contexts',
			'Restart ratio',
			'Yices CPU time',
			'Total CPU time']

import datetime, os
import yicesfull

IND_FILENAME = 0
IND_K = 4
IND_PROOF_SIZE = 6
IND_YICPU = 16
IND_CPU = 17
LLENGTH = 18

NASTR = 'N/A'

CHECK_TYPE_OPTIMIZATION = 0
CHECK_TYPE_INITIATION   = 1
CHECK_TYPE_CONSECUTION  = 2
NUM_CHECK_TYPES = 3

class BrindStats(object):
	def __init__(self):
		self.start = datetime.datetime.now()
		
		self.cs = None
		
		self.yqueries = 0
		self.yassertions = 0
		self.yqueries = 0
		self.yqueries_by_type = [0] * NUM_CHECK_TYPES
		self.ypushes = 0
		self.ypops = 0
		self.ycontexts = 0
		self.holds = None
		self.ce_length = None
		self.k = None
	
	def get_ce_length_string(self):
		if self.ce_length == None:
			return NASTR
		else:
			return str(self.ce_length)
	
	def set_cs(self, cs):
		assert self.cs == None
		self.cs = cs
	
	def get_k_str(self):
		if self.k == None:
			return NASTR
		else:
			return str(self.k)
	
	def get_ccount_str(self):
		if self.cs != None and hasattr(self.cs, 'clauses') and self.cs.clauses != None:
			return str(sum(len(x) for x in self.cs.clauses))
		else:
			return NASTR
	
	def get_proof_size_str(self):
		if self.cs != None and hasattr(self.cs, 'clauses') and self.cs.clauses != None:
			for i in xrange(1, len(self.cs.clauses) - 1):
				if not self.cs.clauses[i]:
					break
			else:
				return NASTR
			return str(sum(len(x) for x in self.cs.clauses[i+1:]))
		else:
			return NASTR
	
	def get_drop_str(self):
		if self.cs != None and hasattr(self.cs, 'cnt_rediscovered'):
			return str(self.cs.cnt_rediscovered + self.cs.cnt_subsumption_drop)
		else:
			return NASTR
	
	def get_eq_drop_str(self):
		if self.cs != None and hasattr(self.cs, 'cnt_rediscovered'):
			return str(self.cs.cnt_rediscovered)
		else:
			return NASTR
	
	def get_subsumption_drop_str(self):
		if self.cs != None and hasattr(self.cs, 'cnt_subsumption_drop'):
			return str(self.cs.cnt_subsumption_drop)
		else:
			return NASTR
	
	def get_restart_ratio_str(self):
		return str(config.restart_ratio)
	
	def get_holds_strn(self):
		if self.holds == None:
			return NASTR
		elif self.holds:
			return 'yes'
		else:
			return 'no'
	
	def get_ytime_str(self, including_seconds = False):
		if config.measure_yices_time:
			return '%sf%s' % (yicesfull.duration(), ' s' if including_seconds else '')
		else:
			return NASTR
	
	def __str__(self):
		user, syst, chuser, chsyst, elapsed = os.times()
		return '''Filename:        %s
Property checked: %d
Proptery holds:   %s
Started at:       %s
k:                %s
Clause count:     %s
Proof size:       %s (ignore if counter example found)
Clauses dropped:  %s (equality: %s, real subsumption: %s)
Yices stats:
  Version:    %s
  Queries:    %d
    Optimization queries: %d
    Initiation queries:   %d
    Consecution queries:  %d
    Other queries:        %d
  Assertions: %d
  Pushes:     %d - %d = %d
  Time:       %s
  Contexts:   %d (restart ratio: %s)
Additional information:
  Seed    : %d
  CPU time: %f s''' % (config.filename,
  			config.check_property,
  			self.get_holds_strn(),
			str(self.start),
  			self.get_k_str(), #
  			self.get_ccount_str(),
  			self.get_proof_size_str(),
  			self.get_drop_str(), self.get_eq_drop_str(), self.get_subsumption_drop_str(),
  			yicesfull.get_version(),
			self.yqueries,
  			self.yqueries_by_type[CHECK_TYPE_OPTIMIZATION],
  			self.yqueries_by_type[CHECK_TYPE_INITIATION],
  			self.yqueries_by_type[CHECK_TYPE_CONSECUTION],
			self.yqueries - self.yqueries_by_type[CHECK_TYPE_OPTIMIZATION]\
			              - self.yqueries_by_type[CHECK_TYPE_INITIATION]\
			              - self.yqueries_by_type[CHECK_TYPE_CONSECUTION],
			self.yassertions,
			self.ypushes, self.ypops, self.ypushes - self.ypops,
			self.get_ytime_str(),
			self.ycontexts, self.get_restart_ratio_str(),
			config.seed,
  			user + syst + chuser + chsyst)
  	
  	def table_row(self):
		user, syst, chuser, chsyst, elapsed = os.times()
  		return [config.filename,
  				str(config.check_property),
  				self.get_holds_strn(),
  				self.get_ce_length_string(),
				str(self.start),
	  			yicesfull.get_version(),
				str(config.seed),
	  			self.get_k_str(), #
	  			self.get_ccount_str(),
	  			self.get_proof_size_str(),
	  			self.get_drop_str(),
	  			self.get_eq_drop_str(),
	  			self.get_subsumption_drop_str(),
	  			str(self.yqueries),
	  			str(self.yqueries_by_type[CHECK_TYPE_OPTIMIZATION]),
	  			str(self.yqueries_by_type[CHECK_TYPE_INITIATION]),
	  			str(self.yqueries_by_type[CHECK_TYPE_CONSECUTION]),
				str(self.yassertions),
				str(self.ypushes),
				str(self.ypops),
				str(self.ycontexts),
				self.get_restart_ratio_str(),
				self.get_ytime_str(),
	  			str(user + syst + chuser + chsyst)]
	
	def write_tr(self, fn):
		if config.table_row_file != None:
			of = open(fn, 'w')
			of.write('\t'.join(self.table_row()))
			of.write('\n')
			of.close()

def table_header():
	return TABLE_HEADER

