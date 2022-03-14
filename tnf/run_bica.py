#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Sat Jun 26 13:34:12 2021

Author: Noel Arteche

"""
from tools import execute_command, BICA, MiniSAT
from time import time
from circuit import Circuit
from os import remove

def prime_cover_via_BICA(formula,
                         do_delete=True,         # delete the temporary files
                         do_write=False,         # write the output to the file obtained_primes.txt
                         do_print_primes=False,  # print the found prime cover
                         do_print_times=False,   # print the running times
                         do_print_summary=False, # print a summary of the run
                         for_testing=False):     # return more info

    """
    This procedure takes as input a Boolean formula and returns a list of sets,
    representing a DNF equivalent to the original formula, of minimal size.
    This is exactly a cover of the formula by prime implicants.

    It calls the tool Bica to do this.

    The input formula can be either an existential Boolean circuit, built by using
    the class Circuit, or a list of lists. For example,

        ['&', 'True', ['&', ['->', ['&', ['-', 'p'], ['&', ['X', 'p'], ['&', ['X', ['X', 'p'] ...

    The flags allow to display information and delete temporary files.

    """

    t0 = time()

    # Create a circuit object with the benchmark to be used.
    # (check first whether it is already a circuit, or whether you need
    # to convert it from a list format given as input).
    C = Circuit()
    if isinstance(formula, Circuit):
        C = formula
    else:
        C.list_to_circ(formula)

    # Create a DIMACS file tuned for BICA with the positive formula.
    C.write_in_DIMACS("pos.cnf", add_BICA_line=True)

    # Create a DIMACS file tuned for BICA with the NEGATIVE formula.
    C.negate_output()
    C.write_in_DIMACS("neg.cnf", add_BICA_line=True)

    t1 = time() - t0

    # Check whether the formulas are tautologies or contradictions; else, call Bica.
    essential_primes = []
    primes_found = 0
    t2 = 0.0

    t_sat = time()
    if MiniSAT("pos.cnf") == "UNSAT":      # is a contradiction; return []
        essential_primes = []
        t_sat = time() - t_sat
    elif MiniSAT("neg.cnf") == "UNSAT":    # is a tautology; return [{}]
        essential_primes = [set()]
        primes_found = 1
        t_sat = time() - t_sat
    else:                       # is a contingency; call BICA
        t_sat = time() - t_sat

        # Call Bica
        t0 = time()
        essential_primes, primes_found = BICA("pos.cnf", "neg.cnf", C)
        t2 = time() - t0

    # Print relevant information, if desired:

    if do_print_primes:
        print()
        print("============================= PRIMES ============================")
        print(essential_primes)
        print("_________________________________________________________________")

    if do_print_summary:
        print()
        print("============================ RESULTS ============================")
        print("BICA found {} essential prime implicants.".format(len(essential_primes)))
        print("Originally, {} primes had been found.".format(primes_found))
        if int(primes_found) != 0:
            print("Percentage of relevant primes: {} %".format(len(essential_primes)/int(primes_found) * 100))

        if essential_primes == [set()]:
            print("The formula is a TAUTOLOGY.")
        elif essential_primes == []:
            print("The formula is a CONTRADICTION.")

    if do_print_times:
        print()
        print("=============================  TIMES  ============================")
        print("TOTAL TIME:                              {} s".format(t1 + t2 + t_sat))
        print("Time for preprocessing formula for BICA: {} s".format(t1))
        print("Time spent by MiniSAT on checking taut.: {} s".format(t_sat))
        print("Time spent by BICA on solving and post.: {} s".format(t2))
        #print("Time spent on post-processing output:    {} s".format(t3))
        print("Percentage of time spent on BICA:        {} %".format(100 * t2/(t1 + t2 + t_sat)))
        print("__________________________________________________________________")

    if do_write:
        f = open("obtained_primes.txt", "w")
        f.write(str(essential_primes))
        f.close()

    # Delete the temporary files used, if desired.
    if do_delete:
        remove("pos.cnf")
        remove("neg.cnf")

    if for_testing:
        return essential_primes, t1 + t2 + t_sat, primes_found
    else:
        return essential_primes


#####################################################
###                   Examples                    ###
#####################################################

""" prime_cover_via_BICA(['->', 'c', ["G[0,3]", ['-', 'c']]], do_delete=True,        # delete the temporary files
                                                                 do_write=False,        # write the output to a file
                                                                 do_print_primes=True,  # print the found prime cover
                                                                 do_print_times=True,   # print the running times
                                                                 do_print_summary=True, # print a summary of the run
                                                                 for_testing=False)     # return more info """
 
# prime_cover_via_BICA(benchmarks.ander_1(),
#                                                                         do_delete=True,
#                                                                         do_write=False,
#                                                                         do_print_primes=True,
#                                                                         do_print_times=True,
#                                                                         do_print_summary=True)

# prime_cover_via_BICA(['|', ['X', ['X', ['-', 'p']]],['X', ['X', 'p']]],
#                                                                         do_delete=True,
#                                                                         do_write=False,
#                                                                         do_print_primes=True,
#                                                                         do_print_times=True,
#                                                                         do_print_summary=True)

# prime_cover_via_BICA(['&', ['X', ['X', ['-', 'p']]],['X', ['X', 'p']]],
#                                                                         do_delete=True,
#                                                                         do_write=False,
#                                                                         do_print_primes=True,
#                                                                         do_print_times=True,
#                                                                         do_print_summary=True)