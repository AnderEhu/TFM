from tools import ander_to_str, execute_command
from os import remove

#################################################
### ================ Circuit ================ ###
#################################################

class Circuit:
    """
    A class used to represent a quantified Boolean circuit.

    
    Attributes
    ----------
    counter : int
        counter to give new variable names
    names : dict[str -> int]
        dictionary mapping names (strings) to numeric names (ints)
    inverse_names: dict[int -> str]
        dictionary mapping numeric names (ints) to names (strings)
    variables : list[str]
        list of strings containing the names of the variables
    quantifiers : list[str]
        lint of strings with the quantifier commands in QCIR,
        ready to add to the file
    gates : dict[int -> list[str, list[int]]]
        dictionary mapping gate numbers to a pair containing the
        operator (str) and the operands (list of ints)
    output : str
        name of the output gate
    written : str
        circuit written in QCIR
    assignments : list[list[int]]
        list of lists containing variable assignments that must not be used

    """

    def __init__(self):
        self.counter = 0            # e.g. :
        self.names = dict()         #   names = {"g3" : 35, ...}
        self.inverse_names = dict() #   inverse_names = {35 : "g3", ...}
        self.variables = list()     #   variables = ["x", "y", ...]
        self.quantifiers = list()   #   quantifiers = ["exists(34, 23, 35)", ...]
        self.gates = dict()         #   gates = {34 : ["and", [1, 2, 3]], ...}
        self.output = ""            #   output = "f34"
        self.written = ""
        self.assignments = []       #   assignments = [ [1, -2], [-2, 3], ... ]

    def id(self, name):
        """
            Assigns a numeric id to a new variable and returns it,
            or returns the numeric id of name if it was already adde before.
        """
        if name in self.names:
            return self.names[name]
        else:
            self.counter += 1
            self.names[name] = self.counter
            self.inverse_names[self.counter] = name
            return self.counter

    def add_variable(self, varName):
        """
            Adds a variable to the circuit, given its name as a string.
        """
        self.id(varName)
        if varName not in self.variables:
            self.variables.append(varName)

    def add_quantifier(self, quant, vars):
        """
            Adds the quantifier block labelled with quant to the variables in the list vars.
        """
        numVars = [self.id(name) for name in vars]
        varsStr = str(numVars)
        self.quantifiers.append(quant + "(" +  varsStr[1:len(varsStr)-1]  + ")")

    def add_gate(self, gateName, operator, operands):
        """
            Adds a gate with output name gateName (str), operator ('and', 'or', 'xor', 'if', 'iff', 'ite'),
            and with a list of operands, given as a nmae of strings e.g. ["-x", "y"].
        """
        numOperands = []
        for name in operands:
            if name[0] == "-":
                numOperands.append(-self.id(name[1:]))
            else:
                numOperands.append(self.id(name))

        if operator in ['or', 'and', 'xor']:
            self.gates[self.id(gateName)] = [operator, numOperands]
        elif operator == 'ite':
            self.gates[self.id(gateName + "_ite_1")] = ["and", numOperands[0:2]]
            self.gates[self.id(gateName + "_ite_2")] = ["and", [-numOperands[0], numOperands[2]]]
            self.gates[self.id(gateName)] = ["or", [self.id(gateName + "_ite_1"), self.id(gateName + "_ite_2")]] 
        elif operator == 'if':
            self.gates[self.id(gateName)] = ["or", [-numOperands[0], numOperands[1]]]
        elif operator == 'iff':
            self.gates[self.id(gateName + "_iff_left")] = ["or", [-numOperands[0], numOperands[1]]]
            self.gates[self.id(gateName + "_iff_right")] = ["or", [-numOperands[1], numOperands[0]]]
            self.gates[self.id(gateName)] = ["and", [self.id(gateName + "_iff_left"), self.id(gateName + "_iff_right")]]

    def set_output(self, output_gate):
        """
            Set the gate with name output_gate as output.
        """
        self.id(output_gate)
        self.output = output_gate

    def negate_output(self, update_written=True):
        if self.output[0] == "-":
            self.output = self.output[1:]
        else:
            self.output = "-" + self.output

        if update_written:
            self.generate_written()

    def generate_written(self):
        """
            Generates the string containing the QCIR version of the circuit.
        """
        qcir = "#QCIR-G14\n"
        #for variable in self.variables:
        #    qcir += "#{} = {}\n".format(variable, self.id(variable))
        for block in self.quantifiers:
            qcir += block + "\n"
        if self.output.startswith('-'):
            qcir += "output(-{})\n".format(self.id(self.output[1:]))
        else:
            qcir += "output({})\n".format(self.id(self.output))
        for gate in self.gates:
            body = str(self.gates[gate][1])
            qcir += str(gate) + " = " + self.gates[gate][0] + "(" + body[1:len(body)-1] + ")" + "\n"
        qcir = qcir[:len(qcir)-1]
        self.written = qcir
        return qcir

    def get_written(self, update_written=False):
        """
            Returns the written version of the circuit if it exists;
            else, it produces it and then returns it.
        """
        if self.written == "" or update_written:
            self.generate_written()

        return self.written

    def generate_file(self, file_name, from_scratch=False):
        """
            Writes the QCIR output into the file with name file_name.
        """
        f = open(file_name, "w")
        if from_scratch:
            self.generate_written()
        f.write(self.get_written())
        f.close()

    def update_primes_circuit(self, assignment):
        C = self
        self.assignments.append(assignment) # added to the list of assignments
        old_out = self.names["out"]
        if self.id("assignments") in self.gates:
            assignments_gate = self.gates[self.id("assignments")]
            self.gates[self.id("assignments")] = ["and", [int(v) for v in assignment]] # add new assignment gate
            assignments_gate[1].append(-self.id("assignments")) # add new assignments
            self.gates[self.id("out")] = [assignments_gate[0], assignments_gate[1]]
            self.names["assignments"] += 1
            self.names["out"] += 1
            C.add_gate("out","and", ["f", "assignments", "prime"])
        else:
            self.gates[self.id("out")  ] = ["and", [int(v) for v in assignment]]
            self.gates[self.id("out")+1] = ["and", [-self.id("out")]]
            self.names["assignments"] = self.id("out")+1
            self.names["out"] += 2
            C.add_gate("out", "and", ["f", "assignments", "prime"])

        # TODO: Directly update the written version
        
    def get_assignments(self):
        return self.assignments

    def process_list(self, formula_as_list):
        """
            Backend recursive procedure that, given a formula in Ander's list format,
            converts it to a circuit and writes it into self.
        """
        C = self
        f = formula_as_list
        gate_name = ""

        # Check if it's already a string:
        if isinstance(formula_as_list, str):
            return formula_as_list

        # Check if it's atomic (p, Xp, X^n p...) --- maybe the case for letters is covered earlier! It also includes F[x, y] and G[a, b]
        if f[0] not in ['&', '|', '-', '->']:
            gate_name = ander_to_str(f)
            if gate_name not in C.variables:
                return "ERROR: variables not defined!"
        # Check whether it's negation
        elif f[0] == '-':
            gate_name = "-" + C.process_list(f[1])
        else:
            operator = f[0]
            if operator == '&':
                operator = 'and'
            elif operator == '|':
                operator = 'or'
            elif operator == '->':
                operator = 'if'
                if (isinstance(f[1], str) and f[1] == 'True'):
                    f = f[2]
                    gate_name = C.process_list(f)
                    return gate_name
                elif (f[1][0] == 'True'):
                    print("The weird case!")
                    f[1] = f[1][1:]
                    gate_name = C.process_list(f)
                    return gate_name

            operands = []
            for i in range(1, len(f)):
                op = C.process_list(f[i])
                if op != 'True' and op != 'False':
                    operands.append(op)

            gate_name = ander_to_str(f)
            C.add_gate(gate_name, operator, operands)

        return gate_name

    def add_variables_from_formula_as_list(self, formula_as_list):
        """
            When converting a formula as list to a circuit, this is used
            to do a first read to check what variables are in the formula.

            In the process, it pulls negations to the front in the case of temporal
            formulas that are booleanized, that's why it returns the (modified) list.
        """
        C = self

        # Check if it's already a string:
        if isinstance(formula_as_list, str):
            if formula_as_list == 'True' or formula_as_list == 'False':
                return formula_as_list
            C.add_variable(formula_as_list)
            return formula_as_list

        # Check if it's atomic (p, Xp, X^n p...) --- maybe the case for letters is covered earlier!
        if formula_as_list[0] not in ['&', '|', '-', '->']:
            complex_name = ander_to_str(formula_as_list) # to_str checks for a negation and pulls it
            if complex_name.startswith('-'):
                C.add_variable(complex_name[1:])
                return ['-', complex_name[1:]]
            else:
                C.add_variable(complex_name)
                return complex_name
                
        else:
            for i in range(1, len(formula_as_list)):
                formula_as_list[i] = C.add_variables_from_formula_as_list(formula_as_list[i])
            return formula_as_list


    def list_to_circ(self, formula_as_list):
        """
            Frontend recursive procedure that, given a formula in Ander's list format,
            converts it to a circuit and writes it into self.
        """
        C = self

        # Add the variables to the circuit and pull temporal negations to the front.
        formula_with_corrected_negations = C.add_variables_from_formula_as_list(formula_as_list)
        if 'True' in C.variables:
            print("ERROR: the constant True got in the list!")
            return
        elif 'False' in C.variables:
            print("ERROR: the constant False got in the list!")

        # Process the list recursively.
        output = C.process_list(formula_with_corrected_negations)

        # Add dummy existential quantifiers.
        C.add_quantifier("exists", C.variables)

        # Set the output
        C.set_output(output)

    def read_from_DIMACS(self, dimacs_file_name):
        """
            Reads a propositional formula (existential) from a DIMACS
            file and writes it into self.
        """
        dimacs = open(dimacs_file_name)
        C = self
        n_variables = 0
        n_clauses = 0
        all_clauses = []

        # Parse de DIMACS file.
        for i, line in enumerate(dimacs):
            if line.startswith('c'): # omit comments
                continue
            elif line.startswith('p'): # read the number of variables and add them to C
                if n_variables > 0:
                    print("ERROR: wrong QCIR format.")
                    return
                n_variables = int(line.split(' ')[2])
                n_clauses = line.split(' ')[3][:-2]
                for v in range(1, n_variables + 1):
                    C.add_variable(str(v))
                C.add_quantifier("exists", C.variables)
            else: # add a clause
                clause = line.split(' ')[:-1]
                C.add_gate(str(n_variables + i), "or", clause)
                all_clauses.append(str(n_variables + i))

        C.add_gate("final", "and", all_clauses)
        C.set_output("final")

        dimacs.close()

    def write_in_QDIMACS(self, qdimacs_file_name):
        """
            Outputs a QDIMACS file with the formula, after conversion to PCNF.
        """
        f = open("temp.qcir", "w")
        f.write(self.generate_written())
        f.close()
        execute_command("./solvers/quabs/build/qcir2qdimacs " + "temp.qcir"   + " > {}".format(qdimacs_file_name))
        remove("temp.qcir")

    def write_in_DIMACS(self, dimacs_file_name, add_BICA_line=False):
        """
            Outputs a DIMACS file with the formula, after conversion to PCNF and
            deleting the quantifiers.
        """
        self.write_in_QDIMACS("temp_dimacs.qdimacs")
        f = open("temp_dimacs.qdimacs", "r")
        g = open(dimacs_file_name, "w")

        if add_BICA_line:
            g.write("c n orig vars {}\n".format(len(self.variables)))

        # Remove the existential quantifiers for QDIMACS to get a DIMACS
        tseitin_vars = 0
        #removed_clauses = 0
        clauses = 0
        for i, line in enumerate(f):
            if line.startswith('p'):
                g.write(line)
                tseitin_vars = int(line.split(' ')[-2])
                clauses = line.split(' ')[-1]
                clauses = clauses[:-1]
                clauses = int(clauses)
            elif not line.startswith('e') and not line.startswith('a'):
                g.write(line)

        f.close()
        g.close()

        remove("temp_dimacs.qdimacs")

def prime_implicants_circuit_DP(F):
    """
        Given a propositional formula written as a circuit F,
        it produces the Imp ^ AltPrime formula for F. 
    """
    C = Circuit()
    # Add variables
    original_vars = F.variables
    x_vars = [str(i) for i in range(1, len(original_vars) + 1)] # the variables of the formula
    u_vars = ['u_' + v for v in x_vars]
    s_vars = ['s_' + v for v in x_vars]
    b_vars = ['b_{}_{}'.format(i, j) for i in x_vars for j in x_vars]
    u_prime_vars = ['u_prime_' + v for v in x_vars]
    y_vars = ['y_' + v for v in x_vars]
    z_vars = ['z_' + v for v in x_vars]
    x_vars = ['x_' + i for i in x_vars]
    for var_set in [u_vars, x_vars, s_vars, u_prime_vars, y_vars, z_vars]:
        for v in var_set:
            C.add_variable(v)

    # Add quantifiers
    C.add_quantifier("exists", u_vars)
    C.add_quantifier("exists", x_vars)
    C.add_quantifier("forall", s_vars)
    C.add_quantifier("exists", b_vars)

    # Add gates for the new variables
    for i in range(1, len(x_vars)+1):
        C.add_gate("v{}".format(str(i)), "ite", ["u_{}".format(str(i)), "s_{}".format(str(i)), "x_{}".format(str(i))])
        for j in range(1, len(x_vars)+1):
            if i == j:
                C.add_gate("w_{}_{}".format(str(i), str(j)), "or", ["b_{}_{}".format(str(i), str(j))])
            else:
                C.add_gate("w_{}_{}".format(str(i), str(j)), "ite", ["u_{}".format(str(j)), "b_{}_{}".format(str(i), str(j)), "x_{}".format(str(j))])
                
    # Somehow I add the gates of the formula three times and call the outputs 'f', 'g' and 'h':
    renaming_f = dict()
    renaming_g = dict()
    for i in range(1, len(x_vars)+1):
            renaming_g[i] = dict()
        
    for i in range(1, len(x_vars)+1):
        renaming_f[F.id(F.variables[i-1])] = "v{}".format(str(i))
        for j in range(1, len(x_vars)+1):
            renaming_g[i][F.id(F.variables[j-1])] = "w_{}_{}".format(str(i), str(j))

    i = 0
    for gate_name in F.names:
        if gate_name not in F.variables and gate_name != F.output:
            i += 1
            renaming_f[F.id(gate_name)] = "f{}".format(str(i))
            for j in range(1, len(x_vars)+1):
                renaming_g[j][F.id(gate_name)] = "g_{}_{}".format(str(j), str(i))


    renaming_f[F.id(F.output)] = "f"
    for i in range(1, len(x_vars)+1):
        renaming_g[i][F.id(F.output)] = "g_" + str(i)

    for gate_num in F.gates:
        gate = F.gates[gate_num]
        op_signs = dict()
        for op in gate[1]:
            op_signs[op] = "-" if op < 0 else ""
        C.add_gate(renaming_f[gate_num], gate[0], [op_signs[op] + renaming_f[abs(op)] for op in gate[1]])
        for i in range(1, len(x_vars)+1):
            C.add_gate(renaming_g[i][gate_num], gate[0], [op_signs[op] + renaming_g[i][abs(op)] for op in gate[1]])
    
    # Priming
    for i in range(1, len(x_vars)+1):
        C.add_gate("prime{}".format(str(i)), "if", ["-u_{}".format(str(i)), "-g_{}".format(str(i))])
    C.add_gate("prime", "and", ["prime{}".format(str(i)) for i in range(1, len(x_vars)+1)])

    C.add_gate("out", "and", ["f", "prime"])
    C.set_output("out")
    
    return C

def prime_implicants_circuit(F):
    """
        Given a propositional formula written as a circuit F,
        it produces the Imp ^ Prime formula for F. 
    """
    C = Circuit()
    # Add variables
    original_vars = F.variables
    x_vars = [str(i) for i in range(1, len(original_vars) + 1)] # the variables of the formula
    u_vars = ['u_' + v for v in x_vars]
    s_vars = ['s_' + v for v in x_vars]
    u_prime_vars = ['u_prime_' + v for v in x_vars]
    y_vars = ['y_' + v for v in x_vars]
    z_vars = ['z_' + v for v in x_vars]
    x_vars = ['x_' + i for i in x_vars]
    for var_set in [u_vars, x_vars, s_vars, u_prime_vars, y_vars, z_vars]:
        for v in var_set:
            C.add_variable(v)

    # Add quantifiers
    C.add_quantifier("exists", u_vars)
    C.add_quantifier("exists", x_vars)
    C.add_quantifier("forall", s_vars)
    C.add_quantifier("forall", u_prime_vars)
    C.add_quantifier("exists", y_vars)
    C.add_quantifier("exists", z_vars)

    # Add gates for the new variables
    for i in range(1, len(x_vars)+1):
        C.add_gate("v{}".format(str(i)), "ite", ["u_{}".format(str(i)), "s_{}".format(str(i)), "x_{}".format(str(i))])
        C.add_gate("w{}".format(str(i)), "ite", ["u_prime_{}".format(str(i)), "y_{}".format(str(i)), "x_{}".format(str(i))])
        C.add_gate("w_prime{}".format(str(i)), "ite", ["u_prime_{}".format(str(i)), "z_{}".format(str(i)), "x_{}".format(str(i))])

    # Somehow I add the gates of the formula three times and call the outputs 'f', 'g' and 'h':
    renaming_f, renaming_g, renaming_h = dict(), dict(), dict()
    for i in range(1, len(x_vars)+1):
        renaming_f[F.id(F.variables[i-1])] = "v{}".format(str(i))
        renaming_g[F.id(F.variables[i-1])] = "w{}".format(str(i))
        renaming_h[F.id(F.variables[i-1])] = "w_prime{}".format(str(i))
    i = 0
    for gate_name in F.names:
        if gate_name not in F.variables and gate_name != F.output:
            i += 1
            renaming_f[F.id(gate_name)] = "f{}".format(str(i))
            renaming_g[F.id(gate_name)] = "g{}".format(str(i))
            renaming_h[F.id(gate_name)] = "h{}".format(str(i))
    renaming_f[F.id(F.output)] = "f"
    renaming_g[F.id(F.output)] = "g"
    renaming_h[F.id(F.output)] = "h"

    for gate_num in F.gates:
        gate = F.gates[gate_num]
        op_signs = dict()
        for op in gate[1]:
            op_signs[op] = "-" if op < 0 else ""
        C.add_gate(renaming_f[gate_num], gate[0], [op_signs[op] + renaming_f[abs(op)] for op in gate[1]])
        C.add_gate(renaming_g[gate_num], gate[0], [op_signs[op] + renaming_g[abs(op)] for op in gate[1]]) 
        C.add_gate(renaming_h[gate_num], gate[0], [op_signs[op] + renaming_h[abs(op)] for op in gate[1]])    
       
    # Agreeing
    for i in range(1, len(x_vars)+1):
        C.add_gate("agree{}".format(str(i)), "if", ["u_{}".format(str(i)), "u_prime_{}".format(str(i))])
    C.add_gate("agree", "and", ["agree{}".format(str(i)) for i in range(1, len(x_vars)+1)])

    # Disagreeing
    for i in range(1, len(x_vars)+1):
        C.add_gate("disagree{}".format(str(i)), "and", ["-u_{}".format(str(i)), "u_prime_{}".format(str(i))])
    C.add_gate("disagree", "or", ["disagree{}".format(str(i)) for i in range(1, len(x_vars)+1)])

    # Validity implies not an implicant
    C.add_gate("valid", "and", ["agree", "disagree"])
    C.add_gate("implicant", "and", ["g", "-h"])
    C.add_gate("prime", "if", ["valid", "implicant"])

    C.add_gate("out", "and", ["f", "prime"])
    C.set_output("out")
    
    return C
