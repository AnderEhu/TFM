#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Wed May 12 19:21:33 2021

@author: alephnoell
"""
from os import popen, remove

#################################################
### ================= Tools ================= ###
#################################################

def ander_to_str(formula):
    """
        Ander's to_str function, used to convert atomic formulas
        to strings when translating from the list of lists format
        to a circuit.
    """
    if isinstance(formula, str):
        return formula
    elif len(formula) == 2:
        if formula[0] == "-":
            return  formula[0] + ander_to_str(formula[1])
        else:
            sub_str = ander_to_str(formula[1])
            if sub_str.startswith('-') and formula[0] == 'X':
                return '-' + formula[0] + "(" + sub_str[1:] +")"
            else:
                return formula[0] + "(" + sub_str +")"
    else:
        leftFormula = ander_to_str(formula[1])
        rightFormula = ander_to_str(formula[2])
        return "(" + leftFormula + ")" + formula[0] + "(" + rightFormula + ")"


def execute_command(command):
    """
        Executes the Linux command given in the input string
        and returns the string with the output.
    """
    call = popen(command)
    output = call.read()
    call.close()
    return output

def call_solver(file_name, solver="depqbf"):
    """
        Calls a QBF solver (either depQBF or QuAbS) to solve the formula
        given the file whose name is provided.
    """
    if solver == "quabs":
        call_output = execute_command("./solvers/quabs/build/quabs" + " --partial-assignment " + file_name)
        #print("the call output is: {}".format(call_output))
        if call_output == "" or "dumped" in call_output:
            print("Error in QUABS!")
            return []
        split = call_output.split("r ")
        sat = split[1][:-1]
        if sat == "UNSAT":
            return []
        else:
            return [int(v) for v in split[0][2:-3].split(" ")]
    elif solver == "depqbf":
        call_output = execute_command("./solvers/quabs/build/qcir2qdimacs " + file_name + 
                                      " | depqbf --qdo")
        split = call_output.split("V ")
        split = split[1:]
        cert = [int(ass[:-2])for ass in split]
        return cert
    else:
        print("Other solvers not yet supported.")

def MiniSAT(file_name):
    res = execute_command("minisat " + file_name)
    if "UNSAT" in res:
        return "UNSAT"
    elif "SAT" in res:
        return "SAT"
    else:
        print("MiniSAT could not determine satisfiability. Printing trace:")
        print(res)
    
def BICA(pos_name, neg_name, C):
    """
        Calls the formula minimization tools BICA on the files with names pos_name
        and neg_name.
    """
    bica_output = execute_command("python3 ./solvers/bica/bica.py -d -vv {} {}".format(pos_name, neg_name))

    bica = open("bica_file.txt", "w")
    bica.write(bica_output)
    bica.close()
    bica = open("bica_file.txt", "r")
    essential_primes = []
    n_primes = 0
    primes_found = 0
    for i, line in enumerate(bica):
        if line.startswith("c1 primes found: "):
            primes_found = line.split(' ')[-1][:-1]
        if n_primes > 0:
            prime = line.split(" ")
            prime = prime[:-1]
            prime = [int(l) for l in prime]
            pi = []
            for l in prime:
                if l > 0:
                    pi.append(C.inverse_names[l])
                else:
                    pi.append("-" + C.inverse_names[abs(l)])
            essential_primes.append(set(pi))
            n_primes -= 1
        if line.startswith("p"):
            info = line.split(" ") # p dnf vars primes
            n_primes = int(info[3][:-1])    
    bica.close()
    remove("bica_file.txt")
    return essential_primes, primes_found     