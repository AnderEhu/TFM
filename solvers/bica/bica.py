#!/usr/bin/env python
#-*- coding:utf-8 -*-
##
## bica.py
##
##  Created on: Feb 11, 2015
##      Author: Alexey S. Ignatiev
##      E-mail: aign@sat.inesc-id.pt
##

#
#==============================================================================
from __future__ import print_function
import approx
import atexit
from forqes import Forqes, ForqesException
import getopt
from mscg import MSCG, MSCGException
import os
from primer import Primer, PrimerException
import resource
import signal
import socket
import sys


#
#==============================================================================
def at_exit(temp_files, times):
    """
        Removing temporary files and showing CPU time at exit.
    """

    for fn in temp_files:
        if os.path.exists(fn):
            os.remove(fn)

    if times[2]:  # only if the main time is set at the end
        print('')
        if times[0]:
            print('c3 phase1 time: {0:.4f}'.format(times[0]))
        if times[1]:
            print('c3 phase2 time: {0:.4f}'.format(times[1]))

        print('c3 script time: {0:.4f}'.format(times[2]))


#
#==============================================================================
def setup_execution(temp_files, times):
    """
        Registers signal and atexit handlers.
    """

    # register interrupt handler
    def handler(signum, frame):
        sys.stderr.write('c interrupted\n')
        sys.exit(0)
        # at_exit will fire here

    signal.signal(signal.SIGTERM, handler)  # external termination
    signal.signal(signal.SIGINT, handler)   # ctrl-c keyboard interrupt

    # register at_exit to remove
    # temporary files when program exits
    atexit.register(at_exit, temp_files, times)


#
#==============================================================================
def create_negation(pfname, temp_files):
    """
        Encodes the negation of the input CNF formula.
    """

    nofv = 0
    cnf_pos = []

    comment_pos = -1  # there is no line 'c n orig vars' in the file
    for i, line in enumerate(open(pfname, 'r')):
        if line[0] != 'p' and line[0] != 'c':
            cl = [int(l) for l in line.split()[:-1]]
            nofv = max([abs(l) for l in cl] + [nofv])

            cnf_pos.append(cl)
        elif line[:13] == 'c n orig vars':
            nofv_orig = int(line[13:].strip())
            comment_pos = i

    fname = '{0}.{1}@{2}'.format(os.path.basename(fns[0])[:-4], os.getpid(),
                                    socket.gethostname())

    if comment_pos == -1 or nofv != nofv_orig:
        pos = '{0}-p.cnf'.format(fname)
        temp_files.append(pos)
        try:
            with open(pos, 'w') as fp:
                print('c n orig vars', nofv, file=fp)
                print('p cnf', nofv, len(cnf_pos), file=fp)
                for cl in cnf_pos:
                    print(' '.join([str(l) for l in cl]), '0', file=fp)
        except IOError as e:
            sys.stderr.write('\033[31;1mERROR:\033[m Unable to write file {0}.\n'.format(pos))
            sys.stderr.write('\033[33m' + str(e) + '\033[m\n')
            sys.exit(1)
    else:
        pos = pfname

    neg = '{0}-n.cnf'.format(fname)
    temp_files.append(neg)

    try:
        with open(neg, 'w') as fp:
            print('c n orig vars', nofv, file=fp)

            cl_fin = []
            cnf_neg = []
            for cl in cnf_pos:
                if len(cl) > 1:
                    nofv += 1
                    cnf_neg.append(cl + [-nofv])

                    for l in cl:
                        cnf_neg.append([-l, nofv])

                    cl_fin.append(-nofv)
                else:
                    cl_fin.append(-cl[0])
            cnf_neg.append(cl_fin)

            print('p cnf', nofv, len(cnf_neg), file=fp)
            for cl in cnf_neg:
                print(' '.join([str(l) for l in cl]), '0', file=fp)
    except IOError as e:
        sys.stderr.write('\033[31;1mERROR:\033[m Unable to write file {0}.\n'.format(neg))
        sys.stderr.write('\033[33m' + str(e) + '\033[m\n')
        sys.exit(1)

    return pos, neg


#
#==============================================================================
def create_minimizer(minimizer, fns, primes, mterms, noneg, weighted, verbose):
    """
        Creates minimizer depending on the command-line options.
    """

    if len(minimizer) >= 6 and minimizer[:6] == "forqes":
        try:
            miner = Forqes(minimizer, fns[0], fns[1], primes, noneg, weighted,
                            verbose)
        except ForqesException as e:
            sys.stderr.write('\033[31;1mERROR:\033[m Unable to use forqes for '
                             'formula minimization.\n')
            sys.stderr.write('\033[33m' + str(e) + '\033[m\n')
            sys.exit(1)
    elif minimizer in ('mscg', 'maxsat', 'mxsat'):
        try:
            miner = MSCG(fns[0], primes, mterms, weighted, verbose)
        except MSCGException as e:
            sys.stderr.write('\033[31;1mERROR:\033[m Unable to use mscg for '
                             'formula minimization.\n')
            sys.stderr.write('\033[33m' + str(e) + '\033[m\n')
            sys.exit(1)
    elif minimizer == 'hhlmuc':
        try:
            miner = approx.HHLMUC(minimizer, fns[0], fns[1], primes, verbose)
        except approx.HHLMUCException as e:
            sys.stderr.write('\033[31;1mERROR:\033[m Unable to use hhlmuc for '
                             'formula minimization.\n')
            sys.stderr.write('\033[33m' + str(e) + '\033[m\n')
            sys.exit(1)
    elif minimizer == 'muser2':
        try:
            miner = approx.MUSer2(minimizer, fns[0], fns[1], primes, verbose)
        except approx.MUSerException as e:
            sys.stderr.write('\033[31;1mERROR:\033[m Unable to use hhlmuc for '
                             'formula minimization.\n')
            sys.stderr.write('\033[33m' + str(e) + '\033[m\n')
            sys.exit(1)

    return miner


#
#==============================================================================
def parse_options():
    """
        Parses command-line options:
    """

    try:
        opts, args = getopt.getopt(sys.argv[1:],
                                   'dhm:np:tvw',
                                   ['mindnf',
                                    'help',
                                    'minimizer=',
                                    'no-neg',
                                    'primer=',
                                    'minterms',
                                    'verbose',
                                    'weighted'])
    except getopt.GetoptError as err:
        sys.stderr.write(str(err).capitalize())
        usage()
        sys.exit(1)

    primer = 'b'
    mindnf = False
    minimizer = 'forqes'
    minterms = False
    noneg = False
    verbose = 0
    weighted = False

    for opt, arg in opts:
        if opt in ('-d', '--mindnf'):
            mindnf = True
        elif opt in ('-h', '--help'):
            usage()
            sys.exit(0)
        elif opt in ('-m', '--minimizer'):
            minimizer = str(arg)
        elif opt in ('-n', '--no-neg'):
            noneg = True
        elif opt in ('-p', '--primer'):
            primer = str(arg)
        elif opt in ('-t', '--minterms'):
            minterms = True
        elif opt in ('-v', '--verbose'):
            verbose += 1
        elif opt in ('-w', '--weighted'):
            weighted = True
        else:
            assert False, 'Unhandled option: {0} {1}'.format(opt, arg)

    return primer, minimizer, mindnf, minterms, noneg, weighted, verbose, args


#
#==============================================================================
def usage():
    """
        Prints usage message.
    """

    print('Usage: ' + os.path.basename(sys.argv[0]) + ' [options] pos-file [neg-file]')
    print('Options:')
    print('        -h, --help')
    print('        -d, --mindnf                Compute a minimum DNF (instead of CNF)')
    print('        -m, --minimizer=<string>    Minimizer to use')
    print('                                    Available values: forqes, hhlmuc, mscg, muser2 (default = forqes)')
    print('                                                      [mscg is for clausal minimization only]')
    print('        -n, --no-neg                Do not use the negated formula when minimizing')
    print('        -p, --primer=<string>       Prime enumeration algorithm')
    print('                                    Available values: a, b, pe2 (default = b)')
    print('                                                      [pe2 is for clausal minimization only]')
    print('        -t, --minterms              Generate minterms before minimizing cover [for mscg only]')
    print('        -w, --weighted              Use weighted formulation (only for exact minimization)')
    print('        -v, --verbose               Be verbose')


#
#==============================================================================
def show_info():
    """
        Prints info message.
    """

    print('c0 Bica Boolean formula minimizer')
    print('c0 author(s):      Alexey Ignatiev    [email:aign@sat.inesc-id.pt]')
    print('c0 contributor(s): Joao Marques-Silva [email:jpms@ucd.ie]')
    print('c0                 Alessandro Previti [email:alessandro.previti@ucdconnect.ie]')
    print('')


#
#==============================================================================
if __name__ == '__main__':
    algo, minimizer, mindnf, mterms, noneg, weighted, verbose, fns = parse_options()
    # sys.stdout = os.fdopen(sys.stdout.fileno(), 'w', 0)

    temp_files = []
    times = [0, 0, 0]
    setup_execution(temp_files, times)

    # testing if input files exist
    for f in fns:
        f = f.strip()
        if not os.path.isfile(f):
            sys.stderr.write('\033[31;1mERROR:\033[m Unable to read file {0}.\n'.format(f))
            sys.stderr.write('\033[33m File may not exist or have wrong permissions.\033[m\n')
            sys.exit(1)

    # a mindnf representation cannot be computed with pe2 or mscg
    if mindnf and (algo == 'pe2' or noneg or minimizer == 'mscg'):
        sys.stderr.write('\033[31;1mERROR:\033[m Unable to compute a minimum'
                         ' DNF representation.\n')
        if len(fns) == 1 or noneg:
            sys.stderr.write('\033[33m Negated formula is also needed.\033[m\n')
        elif algo == 'pe2':
            sys.stderr.write('\033[33m The pe2 algorithm cannot be used.\033[m\n')
        elif minimizer == 'mscg':
            sys.stderr.write('\033[33m The mscg minimizer cannot be used.\033[m\n')

        sys.exit(1)

    # a mindnf representation may be incorrect if only one input file is given
    if mindnf and len(fns) == 1:
        sys.stderr.write('\033[33;1mWARNING:\033[m Maybe unable to compute a '
                         'correct minimum DNF representation.\n')
        sys.stderr.write('\033[33m Negated formula should be also specified.\033[m\n')

    # creating negated formula if needed
    if len(fns) == 1:
        if not (noneg or algo == 'pe2'):
            fns = list(create_negation(fns[0], temp_files))
        else:
            noneg = True
            fns.append('/dev/null')

    # showing head
    show_info()

    # running primer
    try:
        primer = Primer(algo, fns[0], fns[1], verbose, mindnf)
        primes = primer.run()
        times[0] = resource.getrusage(resource.RUSAGE_CHILDREN).ru_utime
    except PrimerException as e:
        sys.stderr.write('\033[31;1mERROR:\033[m Unable to use primer-{0} for '
                         'computing primes.\n'.format(algo))
        sys.stderr.write('\033[33m' + str(e) + '\033[m\n')
        sys.exit(1)

    if mindnf:
        fns[0], fns[1] = fns[1], fns[0]

    # running minimizer
    miner = create_minimizer(minimizer, fns, primes, mterms, noneg, weighted,
            verbose)
    mincnf, nofv = miner.run()
    times[1] = resource.getrusage(resource.RUSAGE_CHILDREN).ru_utime - times[0]

    if verbose > 1:
        # printing solution
        if mindnf:
            print('c2{0} min clausal form:'.format('' if minimizer in ('forqes', 'mscg') else ' approx'))
            print('p dnf', nofv, len(mincnf))
            for clid in mincnf:
                print(' '.join([str(-int(l)) for l in primes[clid].split()]))
        else:
            print('c2{0} min clausal form:'.format('' if minimizer in ('forqes', 'mscg') else ' approx'))
            print('p cnf', nofv, len(mincnf))
            for clid in mincnf:
                sys.stdout.write(primes[clid])

    times[2] = resource.getrusage(resource.RUSAGE_SELF).ru_utime
