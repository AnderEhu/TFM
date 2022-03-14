#!/usr/bin/env python
#-*- coding:utf-8 -*-
##
## approx.py
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
from subprocess import CalledProcessError, Popen, check_output


#
#==============================================================================
class ApproxMin():
    """
        Basic class for approximate minimization.
    """

    def __init__(self, fpos, fneg, primes, verb):
        """
            Basic constructor.
        """

        self.tool = None
        self.path = None
        self.verb = verb

        print('\nc2 approx minimization')
        print('c2 building gmus formula')

        # reading the negated CNF formula and the number of original variables
        self.nofv = 0
        cnf_neg = []
        for line in open(fneg, 'r'):
            if line and line[0] != 'p' and line[0] != 'c':
                cl = [int(l) for l in line.split()[:-1]]
                self.nofv = max([abs(l) for l in cl] + [self.nofv])

                cnf_neg.append(cl)
            elif line[:13] == 'c n orig vars':
                self.nofv_orig = int(line[13:].strip())

        # creating a group-oriented MUS file
        self.gfname = 'p.{0}.{1}@{2}.gcnf'.format(os.path.basename(fpos)[:-4],
                                                os.getpid(), socket.gethostname())

        try:
            with open(self.gfname, 'w') as fp:
                print('p gcnf', self.nofv, len(cnf_neg) + len(primes), len(primes), file=fp)

                for cl in cnf_neg:
                    print('{0}', ' '.join([str(l) for l in cl]), '0', file=fp)

                for i, cl in enumerate(primes):
                    print('{{{0}}}'.format(i + 1), cl, end=' ', file=fp)
        except IOError as e:
            sys.stderr.write('\033[31;1mERROR:\033[m Unable to write file {0}.\n'.format(self.gfname))
            sys.stderr.write('\033[33m' + str(e) + '\033[m\n')
            sys.exit(1)

        atexit.register(self._at_exit)

    def _at_exit(self):
        """
            Removes temporary file.
        """

        if os.path.exists(self.gfname):
            os.remove(self.gfname)

    def run(self):
        """
            Calls approximate minimizer.
        """

        print('c2 running', self.tool)

        subproc = AsyncProc()
        subproc.call(self.args)

        for line in subproc.get_line(0.1):
            if line and line[0] == 'v':
                self.mincnf = [int(l) - 1 for l in line[2:].strip().split()[:-1]]

        print('o', len(self.mincnf))
        return self.mincnf, self.nofv_orig


#
#==============================================================================
class HHLMUCException(Exception):
    pass


#
#==============================================================================
class HHLMUC(ApproxMin, object):
    """
        Class for minimization with hhlmuc.
    """

    def __init__(self, tool, fpos, fneg, primes, verb):
        super(HHLMUC, self).__init__(fpos, fneg, primes, verb)

        self.tool = tool
        self.path = os.path.join(os.path.dirname(os.path.realpath(__file__)), self.tool)
        self.args = [self.path, self.gfname]

        if not os.path.isfile(self.path):
            raise HHLMUCException('Hhlmuc binary not found at {0}'.format(self.path))

        try:
            # a bit of a hack to check whether we can really run it
            DEVNULL = open(os.devnull, 'wb')
            Popen([self.path], stdout=DEVNULL, stderr=DEVNULL)
        except:
            raise HHLMUCException('Hhlmuc binary {0} is not executable.\n'
                                  'It may be compiled for a different platform.'.format(self.path))


#
#==============================================================================
class MUSerException(Exception):
    pass


#
#==============================================================================
class MUSer2(ApproxMin, object):
    """
        Class for minimization with muser2.
    """

    def __init__(self, tool, fpos, fneg, primes, verb):
        super(MUSer2, self).__init__(fpos, fneg, primes, verb)

        self.tool = tool
        self.path = os.path.join(os.path.dirname(os.path.realpath(__file__)), self.tool)

        if not os.path.isfile(self.path):
            raise MUSerException('MUSer2 binary not found at {0}'.format(self.path))

        try:
            # a bit of a hack to check whether we can really run it
            DEVNULL = open(os.devnull, 'wb')
            Popen([self.path], stdout=DEVNULL, stderr=DEVNULL)
        except:
            raise MUSerException('MUSer2 binary {0} is not executable.\n'
                                  'It may be compiled for a different platform.'.format(self.path))

        self.args = [self.path, '-comp', '-grp', '-v', '0', self.gfname]
        if not self._needs_comp_mode():
            self.args.remove('-comp')

    def _needs_comp_mode(self):
        """
            Checks if muser2 needs the '-comp' option.
        """

        try:
            output_ = check_output([self.path, '-h'])
        except CalledProcessError as err:
            output_ = err.output

        for line in output_.split('\n'):
            line = line.lstrip()
            if line[:5] == '-comp':
                return True
            elif line[:7] == '-nocomp':
                return False

        return False
