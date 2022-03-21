#!/usr/bin/env python
#-*- coding:utf-8 -*-
##
## forqes.py
##
##  Created on: Apr 02, 2015
##      Author: Alexey S. Ignatiev
##      E-mail: aign@sat.inesc-id.pt
##

#
#==============================================================================
from __future__ import print_function
from asyncproc import AsyncProc
import atexit
import os
import socket
import subprocess


#
#==============================================================================
class ForqesException(Exception):
    pass


#
#==============================================================================
class Forqes():
    """
        Forqes wrapper class.
    """

    def __init__(self, tool, fpos, fneg, primes, noneg, weighted, verb):
        """
            Forqes wrapper constructor.
        """

        self.tool = tool
        self.verb = verb
        self.path = os.path.join(os.path.dirname(os.path.realpath(__file__)), self.tool)

        if not os.path.isfile(self.path):
            raise ForqesException('Forqes binary not found at {0}'.format(self.path))

        try:
            # a bit of a hack to check whether we can really run it
            DEVNULL = open(os.devnull, 'wb')
            subprocess.Popen([self.path], stdout=DEVNULL, stderr=DEVNULL)
        except:
            raise ForqesException('Forqes binary {0} is not executable.\n'
                                  'It may be compiled for a different platform.'.format(self.path))

        self.pfname = 'p.{0}.{1}@{2}.cnf'.format(os.path.basename(fpos)[:-4],
                                            os.getpid(), socket.gethostname())

        self.args = [self.path, '-n', fneg, '--primes', self.pfname, '-vv',
                        '-w', fpos]
        if not weighted:
            self.args.remove('-w')
        if noneg:
            self.args.remove('-n')
            self.args.remove(fneg)

        print('\nc2 exact minimization')
        print('c2 building primes formula')

        # reading the number of original variables
        for line in open(fpos, 'r'):
            if line[:13] == 'c n orig vars':
                self.nofv = int(line[13:].strip())
                break
            elif line[:6] == 'p cnf ':
                self.nofv = int(line[6:].split()[0].strip())
                break

        # saving primes to a file
        try:
            with open(self.pfname, 'w') as fp:
                print('p cnf', self.nofv, len(primes), file=fp)
                fp.writelines(primes)
        except IOError as e:
            sys.stderr.write('\033[31;1mERROR:\033[m Unable to write file {0}.\n'.format(self.pfname))
            sys.stderr.write('\033[33m' + str(e) + '\033[m\n')
            sys.exit(1)

        atexit.register(self._at_exit)

    def _at_exit(self):
        """
            Removes temporary file.
        """

        if os.path.exists(self.pfname):
            os.remove(self.pfname)

    def run(self):
        """
            Calls approximate minimizer.
        """

        print('c2 running', self.tool)

        subproc = AsyncProc()
        subproc.call(self.args)

        self.mincnf = None
        for line in subproc.get_line(0.1):
            if line:
                if line[0] == 'o':
                    print(line.strip())

                if self.verb:
                    if line[:6] == 'c MDS:':
                        print('c2 ({0}) mds:'.format(self.tool), line[6:].strip())
                    if line[:9] == 'c constr:':
                        print('c2 ({0}) curr cost:'.format(self.tool), line[9:].strip())
                    if line[0] == 'v':
                        self.mincnf = [int(l) - 1 for l in line[2:].strip().split()[:-1]]
                    if line[:13] == 'c disj MDSes:':
                        print('c2 ({0}) disj mdses:'.format(self.tool), line[13:].strip())
                    if line[:13] == 'c unit MDSes:':
                        print('c2 ({0}) unit mdses:'.format(self.tool), line[13:].strip())

        return self.mincnf, self.nofv
