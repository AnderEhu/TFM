#!/usr/bin/env python
#-*- coding:utf-8 -*-
##
## primer.py
##
##  Created on: Apr 02, 2015
##      Author: Alexey S. Ignatiev
##      E-mail: aign@sat.inesc-id.pt
##

#
#==============================================================================
from __future__ import print_function
from asyncproc import AsyncProc
import os
import subprocess


#
#==============================================================================
class PrimerException(Exception):
    pass


#
#==============================================================================
class Primer():
    """
        Primer wrapper class.
    """

    def __init__(self, algo, fpos, fneg, verb, mindnf=False):
        """
            Primer constructor.
        """

        self.tool = 'primer-{0}'.format(algo)
        self.path = os.path.join(os.path.dirname(os.path.realpath(__file__)), self.tool)
        self.verb = verb
        self.primes = []
        self.mindnf = mindnf

        if algo in ('a', 'b'):
            self.args = [self.path, '-no-ip_all', '-print_all', fpos, fneg]
            if self.mindnf:
                self.args[1] = '-ip_all'
        else:  # pe2
            self.args = [self.path, '-print_all', fpos]

        if not os.path.isfile(self.path):
            raise PrimerException('Primer binary not found at {0}'.format(self.path))

        try:
            # a bit of a hack to check whether we can really run it
            DEVNULL = open(os.devnull, 'wb')
            subprocess.Popen([self.path], stdout=DEVNULL, stderr=DEVNULL)
        except:
            raise PrimerException('Primer binary {0} is not executable.\n'
                                  'It may be compiled for a different platform.'.format(self.path))

        print('c1 computing primes')

    def run(self):
        """
            Calls primer binary.
        """
        print('c1 running {0}'.format(self.tool))

        subproc = AsyncProc()
        subproc.call(self.args)
        i = 0
        if self.mindnf:  # outside the loop in a hope of saving time
            for line in subproc.get_line(0.1):
                if line and line[:17] == 'Prime Implicant: ':
                    prime = '{0} 0'.format(line[17:].strip())

                    if self.verb:
                        print('c1 ({0}) pn: {1}'.format(self.tool, prime))
                    print("Hello! A prime was found!")
                    i += 1
                    if (i > 1700):
                        print(i)
                    self.primes.append(' '.join([str(-int(l)) for l in prime.split()]) + '\n')
        else:
            for line in subproc.get_line(0.1):
                if line and line[:17] == 'Prime Implicate: ':
                    prime = '{0} 0'.format(line[17:].strip())
                    self.primes.append(prime + '\n')

                    if self.verb:
                        print('c1 ({0}) pe: {1}'.format(self.tool, prime))

        print('c1', 'primes found:', len(self.primes))
        return self.primes
