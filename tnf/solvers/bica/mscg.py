#!/usr/bin/env python
#-*- coding:utf-8 -*-
##
## mscg.py
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
import itertools
import os
import socket
import subprocess
from six.moves import range
import sys


#
#==============================================================================
class MSCGException(Exception):
    pass


#
#==============================================================================
class MSCG():
    """
        MSCG wrapper class.
    """

    def __init__(self, fpos, primes, minterm_cover, weighted, verb):
        """
            MSCG wrapper constructor.
        """

        self.tool = 'mscg'
        self.verb = verb
        self.soft = []
        self.path = os.path.join(os.path.dirname(os.path.realpath(__file__)), self.tool)

        orig = []
        prim = []
        hard = []
        wght = []

        print('\nc2 exact minimization')
        if not minterm_cover:
            sys.stderr.write('\033[33;1mWARNING:\033[m Minterm covering is not'
                              ' chosen.\n')
            sys.stderr.write('\033[33m Reporting an upper bound.\033[m\n')

        # parsing the original CNF formula
        self.nofv_orig = 0
        for line in open(fpos, 'r'):
            if line and line[0] != 'p' and line[0] != 'c':
                cl = tuple([int(l) for l in line.split()[:-1]])
                self.nofv_orig = max([abs(l) for l in cl] + [self.nofv_orig])

                orig.append(set(cl))

        if minterm_cover:
            mint = set()
            allv = set(range(1, self.nofv_orig + 1))
            for i, cl in enumerate(orig):
                rest = list(allv - set([abs(l) for l in cl]))

                print('\rc2 generating minterms: {0:6.2f}%'.format(float(i) / (len(orig) - 1) * 100), end=' ')
                for ext in itertools.product([-1, 1], repeat=len(rest)):
                    mint.add(tuple(cl) + tuple(map(lambda pair : pair[0] * pair[1], zip(ext, rest))))

            orig = [set(cl_m) for cl_m in mint]
            print('')

        # parsing the primes and Tseitin-encoding them
        t = 1
        full_len = len(primes) + len(orig)
        for line in primes:
            line = line.strip()
            if line:
                cl = [int(l) for l in line.split()[:-1]]
                prim.append(set(tuple(cl)))

                self.soft.append(-t)
                wght.append(len(cl) if weighted else 1)
                t += 1
                print('\rc2 building maxsat formula: {0:6.2f}%'.format(float(t) / (full_len - 1) * 100), end=' ')

        nofv = t

        for i, cl in enumerate(orig):
            cl_h = []
            for t, p in zip(self.soft, prim):
                if p.issubset(cl):
                    cl_h.append(-t)
            print('\rc2 building maxsat formula: {0:6.2f}%'.format(float(i + len(self.soft)) / (full_len - 1) * 100), end=' ')
            hard.append(tuple(cl_h))

        hard = set(tuple(hard))
        hard = list(hard)

        print('')

        # saving MaxSAT formula to a file
        self.mfname = 'm.{0}.{1}@{2}.wcnf'.format(os.path.basename(fpos)[:-4],
                                                os.getpid(), socket.gethostname())

        self.args = [self.path, '-a', 'olliti', '--calc-bounds', '--complete-bmo',
                '--trim', '5', '-vv', self.mfname]
        try:
            with open(self.mfname, 'w') as fp:
                topw = sum(wght) + 1
                print('p wcnf', nofv - 1, len(hard) + len(self.soft), topw, file=fp)

                for cl in hard:
                    print(topw, ' '.join([str(l) for l in cl]), '0', file=fp)

                for tl, w in zip(self.soft, wght):
                    print(w, tl, '0', file=fp)
        except IOError as e:
            sys.stderr.write('\033[31;1mERROR:\033[m Unable to write file {0}.\n'.format(self.mfname))
            sys.stderr.write('\033[33m' + str(e) + '\033[m\n')
            sys.exit(1)

        atexit.register(self._at_exit)

    def _at_exit(self):
        """
            Removes temporary file.
        """

        if os.path.exists(self.mfname):
            os.remove(self.mfname)

    def run(self):
        """
            Calls approximate minimizer.
        """

        print('c2 running', self.tool)

        subproc = AsyncProc()
        subproc.call(self.args)

        for line in subproc.get_line(0.1):
            if line:
                if line[0] == 'o':
                    print(line.strip())
                elif line[0] == 'v':
                    model = [int(l) for l in line[2:].strip().split()]

                if self.verb:
                    if line[:23] == 'c (msu-olliti) n cores:':
                        print('c2 (mscg) curr cost:', line.split(';')[0][23:].strip())
                    elif line[0] == 's':
                        print('c2 (mscg)', line.strip())

                    elif line[:28] == 'c (msu-olliti) bounds found:':
                        print('c2 (mscg) bounds found:', line[29:].strip())

        # determining what soft clauses are falsified by the model
        self.mincnf = []
        for i, l in enumerate(self.soft):
            if model[abs(l) - 1] > 0:
                self.mincnf.append(i)

        return self.mincnf, self.nofv_orig
