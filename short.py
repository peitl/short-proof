#!/usr/bin/env python3

from pysat.card import CardEnc, EncType
from pysat.formula import CNF, IDPool
from pysat.solvers import Solver, Lingeling, Glucose4, Minisat22, Cadical
from time import perf_counter, time, sleep
from datetime import datetime
from random import shuffle
from collections import defaultdict
from bisect import bisect
import pysolvers

import sys, os
import math
import argparse
import subprocess
import functools

from threading import Timer
from multiprocessing import Pool

machine_summary = ""

def info(msg : str):
    print(f"short.py INFO {datetime.now():%d.%m.%Y %H:%M:%S}: {msg}")

def bulk_info(msg_list : list[str]):
    for msg in msg_list:
        info(msg)

# convenience class to specify options for library usage
class Options:
    def __init__(self):
        self.verbosity = 0
        self.sat_solver = "cadical"
        self.cardnum = 1
        self.ldq = False
        self.cnf = ""
        self.enc = "traditional"
        self.orbit_mode = "parallel"
        self.suborbit_mode = "parallel"

class Formula:
    def __init__(self, clauses=None):
        self.clauses = []
        self.exivars = set()
        self.univars = set()
        # unideps maps u to existential variables left of u
        self.unideps = {}
        # uniblockers maps u to existential variables right of u
        self.uniblockers = {}
        if clauses != None:
            for C in clauses:
                self.add_clause(C)

    def add_vars(self, newvars, vartype):
        """
        vartype in {"a", "e"}
        """
        if vartype == "a":
            for v in newvars:
                self.univars.add(v)
                self.unideps[v] = set(self.exivars) # copy
                self.uniblockers[v] = set()
        else:
            for v in newvars:
                self.exivars.add(v)
                for u in self.univars:
                    self.uniblockers[u].add(v)

    def add_clause(self, clause, reductionless=False):

        clause_vars = set(abs(lit) for lit in clause)

        # universally reduce
        if not reductionless:
            clause = sorted(lit for lit in clause if
                    abs(lit) not in self.univars or
                    len(self.uniblockers[abs(lit)] & clause_vars) > 0)

        self.clauses.append(clause)

        # quantify free variables in the outermost block
        new_free_vars = clause_vars - self.exivars - self.univars
        if new_free_vars:
            self.exivars |= new_free_vars
            for u in self.univars:
                self.unideps[u] |= new_free_vars

def internal_single_solve(solver_name, clauses):
    solver = Solver(name=solver_name, bootstrap_with=clauses, use_timer=True)
    ans = solver.solve()
    model = solver.get_model() if ans == True else None
    return ans, model, solver.time()

class SolverWrapper:
    internal_solvers = {
            "cadical",
            "glucose4",
            "lingeling",
            "maplesat",
            "minisat22"
            }
    verbosity_args = {
            "kissat" : ["-q"],
            "cryptominisat5" : ["--verb", "0"],
            "cryptominisat" : ["--verb", "0"]
            }

    def __init__(self, solver_name, clauses, cnf, query):
        self.solver_name = solver_name
        self.clauses = clauses
        self.model = []
        self.query = query

    def interrupt(self):
        self.solver.interrupt()

    def internal_parallel_solve(self, assumptions_list):
        #print(f"Executing {len(assumptions)} process" + "es" if len(assumptions) > 1 else "")
        answers_async = [None for a in assumptions_list]
        with Pool(len(assumptions_list)) as p:
            def terminate_others(val):
                if val == True:
                    p.terminate()
            for i, assumptions in enumerate(assumptions_list):
                answers_async[i] = p.apply_async(
                        internal_single_solve,
                        (
                            self.solver_name,
                            self.clauses + [[x] for x in assumptions]
                        ),
                        callback=lambda val: terminate_others(val[0]))
            p.close()
            p.join()
        answers = [answer_async.get() for answer_async in answers_async if answer_async.ready()]
        ans = False
        time = 0.0
        model = None
        total_time = 0.0
        for pans, pmodel, ptime in answers:
            time = max(time, ptime)
            total_time += ptime
            if pans == True:
                ans = True
                model = pmodel
            if pans == None and ans == False:
                ans = None
        info(f"Solved query {self.query} with answer {ans} in {time:.2f} sec ({total_time:.2f} sec total work)")
        #print(f"* [{datetime.now():%d.%m.%Y %H:%M:%S}] Solved query {self.query} with answer {ans} in {time:.2f} sec ({total_time:.2f} sec total work)")
        return ans, model, time

    #TODO: implement time limit
    def internal_sequential_solve(self, assumptions_list):
        """
            solve with each assumption set from the list in turn,
            looking for the max value (i.e. terminate upon the first SAT answer)
        """
        solver = Solver(name=self.solver_name, bootstrap_with=self.clauses, use_timer=True)
        ans = None
        model = None
        time = 0.0
        for i, assumptions in enumerate(assumptions_list):
            #if time_limit != None:
            #    timer = Timer(time_limit, self.interrupt)
            #    timer.start()

            #    ans = solver.solve_limited(expect_interrupt=True)

            #    if ans != None:
            #        timer.cancel()
            ans = solver.solve(assumptions=assumptions)
            time += solver.time()
            if len(assumptions_list) > 1:
                print(f"solved assumption {i+1} in {solver.time():.2f} sec")
            if ans == True:
                break
        if ans == True:
            model = solver.get_model()
        solver.delete()
        if len(assumptions_list) > 1:
            info(f"Solved query {self.query} with answer {ans} in {time:.2f} sec")
        return ans, model, time

    def solve(self, time_limit = None, assumptions = None):
        if self.solver_name in self.internal_solvers:
            if assumptions == None:
                self.ans, self.model, self.time = internal_single_solve(self.solver_name, self.clauses)
                info(f"Solved query {self.query} with answer {self.ans} in {self.time:.2f} sec")
            else:
                #self.ans, self.model, self.time = self.internal_sequential_solve(assumptions)
                self.ans, self.model, self.time = self.internal_parallel_solve(assumptions)
        else:
            # write the clauses into a temporary CNF file, then
            # call  solver_name  as a subprocess,
            # capture output and read the model
            self.tmp_query_file = cnf + f".has_{self.query}_{time()}.cnf"
            write_formula(self.clauses, self.tmp_query_file)
            t_begin = perf_counter()
            output = subprocess.run([self.solver_name] + self.verbosity_args.get(self.solver_name, []) + [self.tmp_query_file], capture_output=True)
            t_end = perf_counter()
            os.remove(self.tmp_query_file)
            self.time = t_end - t_begin
            self.ans = output.returncode == 10
            if self.ans:
                outlines = output.stdout.decode().split("\n")
                for line in outlines:
                    if len(line) > 0 and line[0] == "v":
                        self.model += [int(lit) for lit in line.split() if lit != "v"]




def implies(preconditions, postconditions):
    """
    Returns a set of clauses that encode that the
    conjunction of preconditions implies the conjunction
    of postconditions
    """
    neg_preconditions = [-x for x in preconditions]
    return [neg_preconditions + [x] for x in postconditions]

def maxvar(clauses):
    return max([0] + [max(abs(lit) for lit in clause) for clause in clauses if len(clause) > 0])

def size(F):
    return sum(len(c) for c in F)

def write_formula(F, filename):
    with open(filename, "w") as f:
        print(f"p cnf {maxvar(F)} {len(F)}", file=f)
        print("".join((" ".join(map(str, clause)) + " 0\n") for clause in F), end="", file=f)


def print_formula(F):
    print(f"p cnf {maxvar(F)} {len(F)}")
    print("".join((" ".join(map(str, clause)) + " 0\n") for clause in F), end="")

def draw_formula(F, padding="  "):
    for cl in F.clauses:
        print(padding, end="")
        cl_string = [" "] * maxvar(F.clauses)
        for lit in cl:
            if lit < 0:
                cl_string[abs(lit) - 1] = "-"
            else:
                cl_string[abs(lit) - 1] = "+"
        print("".join(cl_string))

def read_formula(filename, reductionless):
    """
    Reads QDIMACS (and also DIMACS, which is a special case)
    and returns the set of clauses and data structures that
    represent the prefix.
    """
    F = Formula()
    with open(filename) as f:
        for line in f:
            line = line.strip()
            if len(line) == 0 or line[0] == "c":
                continue
            if line[0] == "p":
                continue
            if line[0] in {"a", "e"}:
                linedata = list(map(int, line.split()[1:-1]))
                F.add_vars(linedata, line[0])
            else:
                linedata = list(map(int, line.split()[:-1]))
                F.add_clause(linedata, reductionless)
    return F





def verb_query_begin(s):
    print(f"* Generating query short_{s}(F)...")
    sys.stdout.flush()

def verb_query_end(nv, nc, nl, t):
    print(f"* Done. ({t:.2f} sec)")
    print(f"* Query has {nv:6d} variables")
    print(f"*           {nc:6d} clauses")
    print(f"*           {nl:6d} literals")
    sys.stdout.flush()


def is_unsat(F):
    return not Lingeling(bootstrap_with=F.clauses).solve()

def is_minimal(F):
    """
    Checks whether the CNF f is minimally unsatisfiable
    Warning: doesn't check whether the formula is UNSAT
    """
    max_var = maxvar(F.clauses)
    clause_vars = list(range(max_var + 1, max_var + len(F.clauses) + 1))
    solver = Lingeling(bootstrap_with=[c + [-clause_vars[i]] for i, c in enumerate(F.clauses)])
    for i in range(len(F.clauses)):
        clause_vars[i] *= -1
        ans = solver.solve(assumptions=clause_vars)
        clause_vars[i] *= -1
        if not ans:
            return False
    return True

def make_predicates(vp):
    # {pos|neg}[i,v] says that the variable v occurs positively (negatively) in clause i
    def pos(i, v):
        return vp.id(f"pos[{i},{v}]")
    def neg(i, v):
        return vp.id(f"neg[{i},{v}]")
    def empty(i):
        return vp.id(f"empty[{i}]")

    # piv[i,v] says that the clause i was obtained by resolving over v
    def piv(i, v):
        return vp.id(f"piv[{i},{v}]")

    # u{pos|neg}[i,v] says, for a resolvent i, that
    # the variable v occurs in at least one premise positively (negatively)
    def upos(i, v):
        return vp.id(f"upos[{i},{v}]")
    def uneg(i, v):
        return vp.id(f"uneg[{i},{v}]")

    # ax[i,j] says that clause i in the proof is axiom j of f
    # isax[i] says that clause i in the proof is an axiom
    def ax(i, j):
        return vp.id(f"ax[{i},{j}]")
    def isax(i):
        return vp.id(f"isax[{i}]")

    # arc[i,j] says that clause j is a resolvent of clause i
    def arc(i, j):
        #print(f"arc[{i},{j}]:{vp.id(f'arc[{i},{j}]')} ", file=sys.stderr)
        return vp.id(f"arc[{i},{j}]")

    # exarc[i,j] says that the arc from i to j is "extra", i.e. not the first outgoing arc from i
    def exarc(i, j):
        return vp.id(f"exarc[{i},{j}]")

    # {pos|neg}carry[i,j,v] says that the variable v occurs {posi|nega}tively in i and
    # is carried over to j because of arc[i,j]
    def poscarry(i, j, v):
        return vp.id(f"poscarry[{i},{j},{v}]")
    def negcarry(i, j, v):
        return vp.id(f"negcarry[{i},{j},{v}]")

    # {pos|neg}drop[i,j,v] says that the variable v occurs {posi|nega}tively in i but
    # does not occur in j anymore
    def posdrop(i, j, v):
        return vp.id(f"posdrop[{i},{j},{v}]")
    def negdrop(i, j, v):
        return vp.id(f"negdrop[{i},{j},{v}]")
    return pos, neg, empty, piv, ax, isax, arc, exarc, upos, uneg, poscarry, negcarry, posdrop, negdrop

def vartable(F, s, vp):

    variables = sorted(F.exivars | F.univars)
    lits = sorted(variables + [-v for v in variables], key=lambda lit: (abs(lit), -lit))
    n = len(variables)
    m = len(F.clauses)

    vt = {}
    pol_int = [-1, 1]
    pol_str = ["-", ""]
    pol_num = 2
    names_cl_var = ["pos", "neg", "piv", "upos", "uneg"]
    names_cl_ax = ["ax"]
    names_cl = ["isax"]
    names_cl_cl = ["arc", "exarc", "sim"]
    names_cl_cl_var = ["poscarry", "negcarry"]
    names_cl_cl_lit = ["eq"]
    vt.update({pol_int[pol] * vp.id(f"{name}[{i}]"): f"{pol_str[pol]}{name}[{i}]"
        for name in names_cl for i in range(s) for pol in range(pol_num)})
    vt.update({pol_int[pol] * vp.id(f"{name}[{i},{v}]"):  f"{pol_str[pol]}{name}[{i},{v}]"
        for name in names_cl_var for i in range(s) for v in variables      for pol in range(pol_num)})
    vt.update({pol_int[pol] * vp.id(f"{name}[{i},{j}]"):  f"{pol_str[pol]}{name}[{i},{j}]"
        for name in names_cl_ax  for i in range(s) for j in range(m)      for pol in range(pol_num)})
    vt.update({pol_int[pol] * vp.id(f"{name}[{i},{j}]"):  f"{pol_str[pol]}{name}[{i},{j}]"
        for name in names_cl_cl  for i in range(s) for j in range(i+1, s) for pol in range(pol_num)})
    vt.update({pol_int[pol] * vp.id(f"{name}[{i},{j},{v}]"):  f"{pol_str[pol]}{name}[{i},{j},{v}]"
        for name in names_cl_cl_var  for i in range(s) for j in range(i+1, s)
        for v in variables for pol in range(pol_num)})
    vt.update({pol_int[pol] * vp.id(f"{name}[{i},{j},{l}]"):  f"{pol_str[pol]}{name}[{i},{j},{l}]"
        for name in names_cl_cl_lit  for i in range(s) for j in range(i+1, s)
        for l in lits for pol in range(pol_num)})
    return vt

def reconstruct(model, F, s, vp):

    variables = sorted(F.exivars | F.univars)
    m = len(F.clauses)
    pos, neg, empty, piv, ax, isax, arc, exarc, upos, uneg, poscarry, negcarry, posdrop, negdrop =\
            make_predicates(vp)

    mset = set(model)
    for i in range(s):
        axioms = []
        parents = []
        clause = []
        for v in variables:
            if pos(i, v) in mset:
                clause.append(v)
            if neg(i, v) in mset:
                clause.append(-v)
        if isax(i) in mset:
            for j in range(m):
                if ax(i, j) in mset:
                    axioms.append(j + 1)
        for y in range(i):
            if arc(y, i) in mset:
                parents.append(y + 1)
        #strcl = " ".join(map(str,clause))
        strcl = " ".join(f"{lit:>3d}" for lit in clause)
        strxioms = f'ax({", ".join(map(str,axioms))})'
        strents = f'res({", ".join(map(str,parents))})'
        print(f"{i+1:2d}: {strcl:<{4*len(variables)}} {(strxioms if axioms else strents)}")

def reconstruct_projected(model, s, vp, G):

    clause_at, clause_until, clause_after, pair_until, clause_available = make_predicates_abstract(vp)
    mset = set(model)
    r = len(G)

    for i in range(s):
        for C in range(r):
            if clause_at(C, i) in mset:
                print(str(i) + ": " + " ".join(map(str, G[C])))
        #print(f"(available:", end="")
        #for C in range(r):
        #    if clause_available(C, i) in mset:
        #        print(" " + " ".join(map(str, G[C])), end=";")
        #print(")")



def definitions(F, s, is_mu, vp):

    variables = sorted(F.exivars | F.univars)
    n = len(variables)
    m = len(F.clauses)
    fset = [set(C) for C in F.clauses]
    pos, neg, empty, piv, ax, isax, arc, exarc, upos, uneg, poscarry, negcarry, posdrop, negdrop =\
            make_predicates(vp)

    definition_clauses = []

    # definition of being an axiom
    definition_clauses += [[-isax(i)] + [ax(i, j) for j in range(i, m)] for i in range(s)] +\
               [[-ax(i, j), isax(i)] for i in range(s) for j in range(i, m)]

    # definition of carries
    definition_clauses += [c for i in range(s-1) for j in range(i+1, s) for v in variables
                    for c in [
                        [-poscarry(i, j, v),  pos(i, v)],
                        [-poscarry(i, j, v),  arc(i, j)],
                        [ poscarry(i, j, v), -pos(i, v), -arc(i, j)],
                        [-negcarry(i, j, v),  neg(i, v)],
                        [-negcarry(i, j, v),  arc(i, j)],
                        [ negcarry(i, j, v), -neg(i, v), -arc(i, j)]
                    ]
                ]

    # defines which literals are in the union of the two premises of a resolvent
    definition_clauses += [c for j in range(2, s) for i in range(j) for v in variables
                    for c in [
                        [-poscarry(i, j, v), upos(j, v)],
                        [-negcarry(i, j, v), uneg(j, v)]
                    ]
                ] +\
                [c for j in range(2, s) for v in variables
                    for c in [
                        [-upos(j, v)] + [poscarry(i, j, v) for i in range(j)],
                        [-uneg(j, v)] + [negcarry(i, j, v) for i in range(j)]
                    ]
                ]

    # definition of pivot
    definition_clauses += [c for i in range(s) for x in F.exivars
                    for c in [
                        [-piv(i, x), upos(i, x)],
                        [-piv(i, x), uneg(i, x)],
                        [-piv(i, x), -pos(i, x)],
                        [-piv(i, x), -neg(i, x)],
                        [-upos(i, x), -uneg(i, x), piv(i, x)]
                    ]
                ]

    # definition of {pos|neg}drop
    #definition_clauses += [c for i in range(s-1) for j in range(i+1, s) for v in variables
    #                for c in [
    #                    [-posdrop(i, j, v),  pos(i, v)],
    #                    [-posdrop(i, j, v), -pos(j, v)],
    #                    [ posdrop(i, j, v), -pos(i, v), pos(j, v)],
    #                    [-negdrop(i, j, v),  neg(i, v)],
    #                    [-negdrop(i, j, v), -neg(j, v)],
    #                    [ negdrop(i, j, v), -neg(i, v), neg(j, v)]
    #                ]
    #            ]

    # set literals in axioms accordingly
    # this is optimized using the fact that axiom i appear no later
    # than as line i (if at all)
    # ! axioms are assumed to be universally reduced ! (done in add_clause)
    set_axioms = []
    for j, c in enumerate(fset):
        for v in variables:
            if -v in c:
                set_axioms.extend([-ax(i, j), neg(i, v)] for i in range(j+1))
                if v in F.univars:
                    set_axioms.extend([-ax(i, j), -pos(i, v)] for i in range(j+1))
            elif v in c:
                set_axioms.extend([-ax(i, j), pos(i, v)] for i in range(j+1))
                if v in F.univars:
                    set_axioms.extend([-ax(i, j), -neg(i, v)] for i in range(j+1))
            else:
                set_axioms.extend([-ax(i, j), -neg(i, v)] for i in range(j+1))
                set_axioms.extend([-ax(i, j), -pos(i, v)] for i in range(j+1))
    definition_clauses += set_axioms

    # definition of emptiness

    definition_clauses += [[empty(i)] + [pos(i, v) for v in variables] + [neg(i, v) for v in variables] for i in range(s)] +\
            [[-empty(i), -pos(i, v)] for i in range(s) for v in variables] +\
            [[-empty(i), -neg(i, v)] for i in range(s) for v in variables]

    return definition_clauses


def essentials(F, s, is_mu, vp, ldq):

    variables = sorted(F.exivars | F.univars)
    n = len(variables)
    m = len(F.clauses)
    pos, neg, empty, piv, ax, isax, arc, exarc, upos, uneg, poscarry, negcarry, posdrop, negdrop =\
            make_predicates(vp)

    essential_clauses = []

    # the first two clauses cannot possibly be resolvents
    essential_clauses += [[isax(0)], [isax(1)]]

    # axioms have no incoming arcs
    essential_clauses += [[-isax(j), -arc(i, j)] for j in range(1, min(s, m+1)) for i in range(j)]

    #######################################################################
    # here we define the resolution constraints via upos and uneg variables
    #######################################################################

    # retention of non-pivot existential literals
    essential_clauses += [c for i in range(2, s) for x in F.exivars
                    for c in [
                        [piv(i, x), -upos(i, x), pos(i, x)],
                        [piv(i, x), -uneg(i, x), neg(i, x)]
                    ]
                ]

    # retention of blocked universals
    essential_clauses += [c for i in range(2, s) for u in F.univars for x in F.uniblockers[u]
                    for c in [
                        [-upos(i, u), pos(i, u), -pos(i, x)],
                        [-upos(i, u), pos(i, u), -neg(i, x)],
                        [-uneg(i, u), neg(i, u), -pos(i, x)],
                        [-uneg(i, u), neg(i, u), -neg(i, x)]
                    ]
                ]
    
    if is_mu:
        # we know exactly which lines are resolvents

        # resolvents have a pivot
        essential_clauses += [[piv(i, x) for x in F.exivars] for i in range(m, s)]

        # non-introduction
        essential_clauses += [c for i in range(m, s) for v in variables
                        for c in [
                            [-pos(i, v), upos(i, v)],
                            [-neg(i, v), uneg(i, v)]
                        ]
                    ]

    else:
        # resolvents have a pivot
        essential_clauses += [[isax(i)] + [piv(i, x) for x in F.exivars] for i in range(2, s)]

        # non-introduction
        essential_clauses += [c for i in range(2, s) for v in variables
                        for c in [
                            [isax(i), -pos(i, v), upos(i, v)],
                            [isax(i), -neg(i, v), uneg(i, v)]
                        ]
                    ]

    # at most one pivot
    # NOTE: this cardinality constraint uses no auxiliary variables (otherwise must be moved to the end)
    essential_clauses += [c for i in range(s)
            for c in CardEnc.atmost([piv(i, x) for x in F.exivars], encoding=EncType.pairwise).clauses]

    # no variable occurs both positively and negatively in a clause
    if not ldq:
        essential_clauses += [[-pos(i, v), -neg(i, v)] for i in range(s-1) for v in variables]
    else:
        essential_clauses += [[-pos(i, x), -neg(i, x)] for i in range(s-1) for x in F.exivars]


    # union of premises is non-tautological on universal variables
    if not ldq:
        essential_clauses += [[-upos(i, u), -uneg(i, u)] for i in range(s) for u in F.univars]
    else:
        essential_clauses += [
                [-arc(i, k), -arc(j, k), -pos(i, u), -neg(j, u)] +
                [piv(k, x) for x in F.unideps[u]]
                    for k in range(2, s)
                    for i in range(k)
                    for j in range(k) if i != j
                    for u in F.univars
                ]

    # clauses are universally reduced
    essential_clauses += [C for i in range(s) for u in F.univars for C in
            [
                [-pos(i, u)] +\
                    [pos(i, x) for x in F.uniblockers[u]] + [neg(i, x) for x in F.uniblockers[u]],
                [-neg(i, u)] +\
                    [pos(i, x) for x in F.uniblockers[u]] + [neg(i, x) for x in F.uniblockers[u]]
            ]
        ]

    # all clauses following an empty clause are also empty, derived by the same last step
    # this is for when we don't have a tight lower bound, i.e. when we're not doing incremental search
    #
    # WARNING: this has to be updated, if we want to fix a suffix of the proof, such as the last
    # resolution step. What can happen is we can have  [ ..., empty, empty, empty, x, -x, empty]
    # thus, here we need to know whether we are fixing something at the end, and adjust accordingly
    essential_clauses += [[-empty(i), empty(i+1)] for i in range(s-1)]
    essential_clauses += [[-arc(i,j), -empty(j), arc(i, j+1)] for j in range(2, s-1) for i in range(j)]

    # the last clause is empty
    essential_clauses += [[empty(s-1)]]

    return essential_clauses

def axiom_placement_clauses(F, s, is_mu, vp):

    variables = sorted(F.exivars | F.univars)
    n = len(variables)
    m = len(F.clauses)
    axioms = range(m)
    pos, neg, empty, piv, ax, isax, arc, exarc, upos, uneg, poscarry, negcarry, posdrop, negdrop =\
            make_predicates(vp)

    # axioms appear in original order, without duplicates
    # axiom j cannot possibly appear later than as clause j
    # all axioms are in the front
    # axioms have no pivot

    axiom_placement = []
    if is_mu:
        axiom_placement += [[ax(i, i)] for i in axioms] + [[-isax(i)] for i in range(m, s)]
        axiom_placement += [[-piv(i, x)] for i in axioms for x in F.exivars]
        axiom_placement += [[-upos(i, v)] for i in axioms for v in variables] +\
                           [[-uneg(i, v)] for i in axioms for v in variables]
    else:
        axiom_placement += [[-isax(i), isax(i-1)] for i in range(2, s)]
        axiom_placement += [[-ax(i, j)] for i in proof_clauses for j in range(min(i, m))]
        axiom_placement += [[-ax(i, j), -ax(i+1, jj)]
                for i in range(s-1) for j in axioms for jj in range(j+1)]
        axiom_placement += [[-isax(i), -piv(i, x)] for i in range(s-1) for x in F.exivars]
        axiom_placement += [[-isax(i), -upos(i, v)] for i in axioms for v in variables] +\
                           [[-isax(i), -uneg(i, v)] for i in axioms for v in variables]

    return axiom_placement

def redundancy(F, s, is_mu, vp, card_encoding, known_lower_bound=None, var_orbits=None):

    variables = sorted(F.exivars | F.univars)
    n = len(variables)
    m = len(F.clauses)

    redundant_clauses = []
    pos, neg, empty, piv, ax, isax, arc, exarc, upos, uneg, poscarry, negcarry, posdrop, negdrop =\
            make_predicates(vp)

    # every non-empty clause must be used. As soon as we derive the empty clause, the
    # rest is filled with its copies
    redundant_clauses += [[empty(i)] + [arc(i, j) for j in range(i+1, s)] for i in range(s-1)]

    # in the same case, we know that no subsumed clause is ever derived
    #redundant_clauses += [
    #        [posdrop(i, j, v) for v in variables] +\
    #        [negdrop(i, j, v) for v in variables]
    #        for i in range(s-1) for j in range(i+1, s)]

    # resolvents have exactly two premises
    if is_mu:
        redundant_clauses +=  [card_clause for j in range(max(m, 3), s) for card_clause in
                CardEnc.equals([arc(i, j) for i in range(j)],
                    bound=2,
                    encoding=card_encoding,
                    vpool=vp).clauses]
    else:
        redundant_clauses += [[isax(j)] + card_clause for j in range(3, s) for card_clause in
                CardEnc.equals([arc(i, j) for i in range(j)],
                    bound=2,
                    encoding=card_encoding,
                    vpool=vp).clauses]

    if is_mu:
            # definition of an extra arc
            redundant_clauses += [[-arc(i, j), -arc(i, k), exarc(i, k)]
                    for i in range(s-2)
                        for j in range(max(i+1, m), s-1)
                            for k in range(j+1, s)]
            redundant_clauses += [[-exarc(i, j), arc(i, j)]
                    for i in range(s-2)
                        for j in range(max(i+2, m+1), s)]
            redundant_clauses += [[-exarc(i, k)] + [arc(i, j) for j in range(max(i+1, m), k)]
                        for i in range(s-2)
                            for k in range(max(i+2, m+1), s)]

            # limit the number of extra arcs to s - 2m + 1
            # when we allowed the proof to be shorter than s, this bound had to be adapted: we can have more extra arcs,
            # because the copies of the empty clause each have outdegree 0
            redundant_clauses += CardEnc.atmost(
                    [exarc(i, j) for i in range(s-2) for j in range(max(i+2, m), s)] + [-empty(i) for i in range(known_lower_bound, s)],
                    bound=s-2*m+1+s-known_lower_bound,
                    encoding=card_encoding,
                    vpool=vp).clauses

    # each variable must be a pivot at least once
    # if v is the pivot in j and i is a premise, then v appears in i (pos or neg)
    #if is_mu:
    #    redundant_clauses += [[piv(i, v) for i in range(m, s)] for v in F.exivars]
    #    redundant_clauses += [[-arc(i, j), -piv(j, v), pos(i, v), neg(i, v)] for j in range(m, s) for i in range(j) for v in F.exivars]
    #    pass
    #else:
    #    redundant_clauses += [[piv(i, v) for i in range(2, s)] for v in F.exivars]
    #    pass

    # we know that there is no proof of length < known_lower_bound
    if known_lower_bound != None:
        redundant_clauses += [[-empty(known_lower_bound-2)]]

    # TODO: turned off for now, because large and not that performant
    ## for saturated formulas: require that extending "phantom" literals propagate all the way down
    ## phantom variable v added to axiom k occurs in clause i
    #def phos(i, k, v):
    #    return vp.id(f"phantom_pos[{i},{k},{v}]")
    #def pheg(i, k, v):
    #    return vp.id(f"phantom_neg[{i},{k},{v}]")
    #def phos_carry(i, j, k, v):
    #    return vp.id(f"phantom_pos_carry[{i},{j},{k},{v}]")
    #def pheg_carry(i, j, k, v):
    #    return vp.id(f"phantom_neg_carry[{i},{j},{k},{v}]")

    #Fset = [set(C) for C in F.clauses]
    #phars_pos = [(k, v) for k in range(m) for v in variables if  v not in Fset[k]]
    #phars_neg = [(k, v) for k in range(m) for v in variables if -v not in Fset[k]]

    #phantom_init = [[phos(k, k, v)] for k, v in phars_pos] + [[pheg(k, k, v)] for k, v in phars_neg]

    #phantom_propagation =\
    #        [[-pos(i, v), -phos(i, k, v)] for i in range(s) for k, v in phars_pos] +\
    #        [[-neg(i, v), -pheg(i, k, v)] for i in range(s) for k, v in phars_neg] +\
    #        [ 
    #            C for j in range(m, s) for i in range(j) for k, v in phars_pos for C in [
    #                [-phos(i, k, v), -arc(i, j), phos_carry(i, j, k, v)],
    #                [ phos(i, k, v), -phos_carry(i, j, k, v)],
    #                [ arc(i, j), -phos_carry(i, j, k, v)]
    #            ]
    #        ] + [
    #            C for j in range(m, s) for i in range(j) for k, v in phars_neg for C in [
    #                [-pheg(i, k, v), -arc(i, j), pheg_carry(i, j, k, v)],
    #                [ pheg(i, k, v), -pheg_carry(i, j, k, v)],
    #                [ arc(i, j), -pheg_carry(i, j, k, v)]
    #            ]
    #        ] + [
    #            [-phos(j, k, v)] + [phos_carry(i, j, k, v) for i in range(j)]
    #            for j in range(m, s) for k, v in phars_pos
    #        ] + [
    #            [-pheg(j, k, v)] + [pheg_carry(i, j, k, v) for i in range(j)]
    #            for j in range(m, s) for k, v in phars_neg
    #        ]

    #phantom_end = [[phos(s-1, k, v)] for k, v in phars_pos] + [[pheg(s-1, k, v)] for k, v in phars_neg]

    #redundant_clauses += phantom_init + phantom_propagation + phantom_end

    if known_lower_bound != None:
        # place bounds on the number of active clauses depending on the stage of the proof
        def active(i, j):
            return vp.id(f"active[{i},{j}]")

        def hardness_bound(j):
            #return [0, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11][bisect([1, 2, 3, 4, 6, 8, 10, 12, 14, 17], j)]
            return bisect([1, 2, 3, 4, 6, 8, 10, 12, 14, 17], j) + 1

        def_active = [
                        [-active(i, j)] + [arc(i, k) for k in range(j, s)]
                            for j in range(m, s)
                                for i in range(j)
                    ]# + [
                     #   [active(i, j), -arc(i, k)]
                     #       for j in range(m, s)
                     #           for i in range(j)
                     #               for k in range(j, s)
        if is_mu:
            init_active = [[active(i, m) for i in range(m)]]

        bound_active = []
        for j in range(m, known_lower_bound):
            #print(f"{j} : {s-j} : {hardness_bound(s-j)}")
            bound_active += CardEnc.atleast([active(i, j) for i in range(j)], bound=hardness_bound(known_lower_bound-j), vpool=vp).clauses
        redundant_clauses += def_active + init_active + bound_active

        # TODO: only do for irreducible formulas (i.e. assuming irreduciblity)
        no_axiom_cut = [[-arc(i, m), -arc(j, m), active(i, m+1), active(j, m+1)] for i in range(m) for j in range(i+1, m)]

        redundant_clauses += no_axiom_cut


    return redundant_clauses

def symmetry_breaking_v(F, s, is_mu, vp, var_orbits=None, sub_orbits=None, orbit_mode=None, suborbit_mode=None):

    pos, neg, empty, piv, ax, isax, arc, exarc, upos, uneg, poscarry, negcarry, posdrop, negdrop =\
            make_predicates(vp)
    variables = sorted(F.exivars | F.univars)
    lits = sorted(variables + [-v for v in variables], key=lambda lit: (abs(lit), -lit))
    n = len(variables)
    m = len(F.clauses)

    symbreak = []

    # lexicographic ordering of consecutive clauses

    # if the formula is mu, we know where the axioms are
    istart = m if is_mu else 2
    if is_mu:
        def isax_mu(i):
            return []
    else:
        def isax_mu(i):
            return [isax(i)]


    # we will use the fact that clauses are non-tautological
    # and model them as vectors of {0, 1, 2} indexed by variables
    # positive occurrence = 2
    # negative occurrence = 1
    #       no occurrence = 0
    #
    # NOTE that this doesn't work for long-distance Q-resolution

    # the last clause on which the lex ordering should be enforced
    last = s-1
    if var_orbits != None and orbit_mode != None:
        last = s-3
        if sub_orbits != None and suborbit_mode != None:
            last = s-4

    def leq(i, j, v):
        return vp.id(f"leq[{i},{j},{v}]")

    def leq_upto(i, j, l):
        return vp.id(f"leq_upto[{i},{j},{v}]")

    for i in range(istart, last-1):
        for j in range(i+1, last):
            for v in variables:
                #prd = pos if lits[k] > 0 else neg
                #v = abs(lits[k])
                symbreak.extend([
                    [-leq(i, j, v), -pos(i, v),  pos(j, v)],
                    [-leq(i, j, v), -neg(i, v),  neg(j, v), pos(j, v)],
                    [ leq(i, j, v), -pos(j, v)],
                    [ leq(i, j, v),  pos(i, v), -neg(j, v)],
                    [ leq(i, j, v),  pos(i, v),  neg(i, v)],
                ])

    for i in range(istart, last-1):
        for j in range(i+1, last):
            for k, v in enumerate(variables):
                if k == 0:
                    symbreak += [
                            [-leq_upto(i, j, variables[0]),  leq(i, j, variables[0])],
                            [ leq_upto(i, j, variables[0]), -leq(i, j, variables[0])]
                        ]
                else:
                    symbreak.extend([
                        [-leq_upto(i, j, v),  leq_upto(i, j, variables[k-1])],
                        [-leq_upto(i, j, v),  leq(i, j, v)],
                        [ leq_upto(i, j, v), -leq_upto(i, j, variables[k-1]), -leq(i, j, v)]
                    ])

    # simultaneous source property
    # sim[i,j] says that the if the clauses are being removed in this order,
    # at the time of removal of i (when i is a source), j is also a source
    def sim(i, j):
        return vp.id(f"sim[{i},{j}]")

    symbreak += [[ sim(i, i+1),  arc(i, i+1)] for i in range(istart, last-1)] +\
                [[-sim(i, i+1), -arc(i, i+1)] for i in range(istart, last-1)]

    # ϴ(s^2·n) clauses
    # ϴ(s^2·n) literals
    for i in range(istart, last-2):
        for j in range(i+2, last):
            symbreak += [
                    [-sim(i, j),  sim(i+1, j)],
                    [-sim(i, j), -arc(i, j)],
                    [ sim(i, j), -sim(i+1, j), arc(i, j)]
                    ]

    for i in range(istart, last-1):
        for j in range(i+1, last):
            symbreak.append(isax_mu(i) + [-sim(i, j), pos(i, variables[0]),                       -pos(j, variables[0])])
            symbreak.append(isax_mu(i) + [-sim(i, j), pos(i, variables[0]), neg(i, variables[0]), -neg(j, variables[0])])
            for k, v in enumerate(variables):
                if k < len(variables) - 1:
                    symbreak.append(isax_mu(i) + [-sim(i, j), -leq_upto(i, j, v), pos(i, variables[k+1]),                         -pos(j, variables[k+1])])
                    symbreak.append(isax_mu(i) + [-sim(i, j), -leq_upto(i, j, v), pos(i, variables[k+1]), neg(i, variables[k+1]), -neg(j, variables[k+1])])
            # a non-empty clause shouldn't subsume any successor clause
            symbreak.append([empty(i), -leq_upto(i, j, variables[-1])])

    assumptions = None
    if var_orbits != None and orbit_mode != None:

        # TODO I don't think this is entirely sound with s-1-i instead of s-i...
        for i in range(4, 6):
            symbreak += CardEnc.atmost(
                    [pos(s-i, v) for v in variables] +
                    [neg(s-i, v) for v in variables],
                    i-2, vpool=vp).clauses

        if orbit_mode == "parallel":
            assumptions = []
            for i, O in enumerate(var_orbits):
                v = O[0]
                fix_last_resolution = [
                            neg(s-2, v),
                            pos(s-3, v)
                        ] + [
                            -pos(s-2, w) for w in variables
                        ] + [
                            -neg(s-3, w) for w in variables
                        ] + [
                            -pos(s-3, w) for w in variables if v != w
                        ] + [
                            -neg(s-2, w) for w in variables if v != w
                        ] + [arc(s-2, s-1), arc(s-3, s-1), -arc(s-3, s-2)]
                if sub_orbits == None:
                    assumptions.append(fix_last_resolution)
                else:
                    if suborbit_mode == None:
                        assumptions.append(fix_last_resolution)
                    elif suborbit_mode == "parallel":
                        for SO in sub_orbits[i]:
                            w = SO[0]
                            assumptions.append(fix_last_resolution +
                                    [-pos(s-4, x) for x in variables if x not in {v, w}] +
                                    [-neg(s-4, x) for x in variables if x not in {v, w}]
                                    )
                    elif suborbit_mode == "sequential":
                        SOR = {SO[0] for SO in sub_orbits[i]} | {v}
                        assumptions.append(fix_last_resolution +
                                [-pos(s-4, x) for x in variables if x not in SOR] +
                                [-neg(s-4, x) for x in variables if x not in SOR]
                                )
        elif orbit_mode == "sequential":
            OR = {O[0] for O in var_orbits}
            #fix_last_resolution =\
            symbreak += \
                    [[-pos(s-2, x)] for x in variables               ] +\
                    [[-neg(s-2, x)] for x in variables if x not in OR] +\
                    [[-pos(s-3, x)] for x in variables if x not in OR] +\
                    [[-neg(s-3, x)] for x in variables               ] +\
                    [[arc(s-2, s-1), arc(s-3, s-1), -arc(s-3, s-2)]] +\
                    [[piv(s-1, x) for x in OR]] +\
                    [[-pos(s-3, x),  neg(s-2, x)] for x in OR] +\
                    [[ pos(s-3, x), -neg(s-2, x)] for x in OR]
            if sub_orbits != None and suborbit_mode != None: # sequential var orbit mode cannot be combined with parallel sub orbit mode (TODO check why)
                SOR = {SO[0] for i in range(len(var_orbits)) for SO in sub_orbits[i]}
                symbreak += \
                        [[-pos(s-4, x)] for x in variables if x not in SOR] +\
                        [[-neg(s-4, x)] for x in variables if x not in SOR]


                        


    # only for variable-transitive formulas, such as PHP: the last clause must always be unit,
    # and in fact we can pick the literal in that clause (by a Lemma)
    # we pick the last negative literal because it is the smallest in the lex-ordering
    # we can also constrain the clause before that

    #TODO: detect formula symmetries and orbits automatically
    #symbreak += [[pos(s-2, variables[-1]), neg(s-2, variables[-1])]] +\
    #symbreak += [[neg(s-2, variables[-1])]] +\
    #        [[-pos(s-2, v)] for v in variables[:-1]] +\
    #        [[-neg(s-2, v)] for v in variables[:-1]] +\
    #        [[pos(s-3, variables[-1]), neg(s-3, variables[-1])]] +\
    #        [[-pos(s-3, variables[-1]), -pos(s-3, v)] for v in variables[:-1]] +\
    #        [[-pos(s-3, variables[-1]), -neg(s-3, v)] for v in variables[:-1]]

    #TODO: the Lemma says that if O contains a variable from every var-orbit, then there is a variable o in O
    # such that an arbitrary literal of o can be placed as the last unit clause. We pick the negative literal
    # because that cannot clash with the symmetry breaking (really though? What if the negative clause can be
    # derived much earlier?) all variables always contain a variable from every orbit, so that's an overapprox.
    #symbreak += [[neg(s-2, v) for v in variables]]
    #symbreak += [[neg(s-2, variables[0])]]

    return symbreak, assumptions

def symmetry_breaking(F, s, is_mu, vp, var_orbits=None):

    pos, neg, empty, piv, ax, isax, arc, exarc, upos, uneg, poscarry, negcarry, posdrop, negdrop =\
            make_predicates(vp)
    variables = sorted(F.exivars | F.univars)
    lits = sorted(variables + [-v for v in variables], key=lambda lit: (abs(lit), -lit))
    n = len(variables)
    m = len(F.clauses)

    symbreak = []

    # lexicographic ordering of consecutive clauses

    # if the formula is mu, we know where the axioms are
    istart = m if is_mu else 2
    if is_mu:
        def isax_mu(i):
            return []
    else:
        def isax_mu(i):
            return [isax(i)]



    # geq[i,j,l] says that all literals up to and including position l,
    # are greater than or equal in clause j than in clause i
    def geq(i, j, l):
        return vp.id(f"geq[{i},{j},{l}]")

    def geq_upto(i, j, l):
        return vp.id(f"geq_upto[{i},{j},{l}]")

    for i in range(istart, s-1):
        for j in range(i+1, s):
            for k in range(0, len(lits)):
                prd = pos if lits[k] > 0 else neg
                v = abs(lits[k])
                symbreak.extend([
                    [-geq(i, j, lits[k]), -prd(i, v),  prd(j, v)],
                    [ geq(i, j, lits[k]), -prd(j, v)],
                    [ geq(i, j, lits[k]),  prd(i, v)],
                ])

    prd = pos if lits[0] > 0 else neg
    v = abs(lits[0])
    symbreak += [c for i in range(istart, s-1) for j in range(i+1, s) for c in [
                [-geq_upto(i, j, lits[0]),  geq(i, j, lits[0])],
                [ geq_upto(i, j, lits[0]), -geq(i, j, lits[0])]
            ]
        ]
    for i in range(istart, s-1):
        for j in range(i+1, s):
            for k in range(1, len(lits)):
                prd = pos if lits[k] > 0 else neg
                v = abs(lits[k])
                symbreak.extend([
                    [-geq_upto(i, j, lits[k]),  geq_upto(i, j,  lits[k-1])],
                    [-geq_upto(i, j, lits[k]),  geq(i, j, lits[k])],
                    [ geq_upto(i, j, lits[k]), -geq_upto(i, j,  lits[k-1]), -geq(i, j, lits[k])]
                ])

    # simultaneous source property
    # sim[i,j] says that the if the clauses are being removed in this order,
    # at the time of removal of i (when i is a source), j is also a source
    def sim(i, j):
        return vp.id(f"sim[{i},{j}]")

    symbreak += [[ sim(i, i+1),  arc(i, i+1)] for i in range(istart, s-1)] +\
                [[-sim(i, i+1), -arc(i, i+1)] for i in range(istart, s-1)]

    # ϴ(s^2·n) clauses
    # ϴ(s^2·n) literals
    for i in range(istart, s-2):
        for j in range(i+2, s):
            symbreak += [
                    [-sim(i, j),  sim(i+1, j)],
                    [-sim(i, j), -arc(i, j)],
                    [ sim(i, j), -sim(i+1, j), arc(i, j)]
                    ]

    # ϴ(s^2·n) clauses
    # ϴ(s^2·n) literals
    first_prd = pos if lits[0] > 0 else neg
    first_v = abs(lits[0])
    for i in range(istart, s-1):
        for j in range(i+1, s):
            symbreak.append(isax_mu(i) + [-sim(i, j), first_prd(i, first_v), -first_prd(j, first_v)])
            for k in range(len(lits) - 1):
                prd = pos if lits[k+1] > 0 else neg
                v = abs(lits[k+1])
                symbreak.append(isax_mu(i) + [-sim(i, j), -geq_upto(i, j, lits[k]), prd(i, v), -prd(j, v)])
            # a non-empty clause shouldn't subsume any successor clause
            symbreak.append([empty(i), -qeq_upto(i, j, lits[-1])])

    # only for variable-transitive formulas, such as PHP: last clause must always be unit, so
    # we fix the variable in that clause to be x_{n-1}, because those are the smallest clauses
    # in the lexicographic ordering

    #symbreak += [[pos(s-2, variables[-1]), neg(s-2, variables[-1])]] +\
    #        [[-pos(s-2, v)] for v in variables[:-1]] +\
    #        [[-neg(s-2, v)] for v in variables[:-1]]


    return symbreak


def get_query(F, s, is_mu, card_encoding, ldq, known_lower_bound=None, var_orbits=None, sub_orbits=None, orbit_mode=None, suborbit_mode=None):
    """
    This function takes a CNF formula F and an integer s,
    and returns clauses that encode the statement:

    Does F have a resolution refutation of length at most s?

    It also returns lists of variables that are useful in order
    to recover the found proof.

    The optional variable_orbits argument specifies the orbits of the variables 1..n
    under a group of symmetries of F. If given, get_query will additionally return
    a list of lists of assumptions that try to find a proof by fixing the last resolution
    step to a variable of each orbit in turn.
    """

    variables = sorted(F.exivars | F.univars)
    n = len(variables)
    m = len(F.clauses)

    vp = IDPool()

    # clauses in the proof are indexed starting from 0

    # some helper notation
    axioms = range(m)
    proof_clauses = range(s)

    pos, neg, empty, piv, ax, isax, arc, exarc, upos, uneg, poscarry, negcarry, posdrop, negdrop =\
            make_predicates(vp)

    definition_clauses = definitions(F, s, is_mu, vp)

    essential_clauses = essentials(F, s, is_mu, vp, ldq)

    ############### REDUNDANCY ###############

    redundant_clauses = redundancy(F, s, is_mu, vp, card_encoding, known_lower_bound=known_lower_bound)

    ############### SYMMETRY BREAKING ###############

    axiom_placement = axiom_placement_clauses(F, s, is_mu, vp)

    symbreak = None
    assumptions = None
    if ldq == False:
        symbreak, assumptions = symmetry_breaking_v(F, s, is_mu, vp, var_orbits=var_orbits, sub_orbits=sub_orbits, orbit_mode=orbit_mode, suborbit_mode=suborbit_mode)
    else:
        symbreak = symmetry_breaking(F, s, is_mu, vp, var_orbits=var_orbits)

    all_clauses =\
            definition_clauses +\
            essential_clauses +\
            axiom_placement

    max_orig_var = maxvar(all_clauses)
    
    all_clauses += redundant_clauses + symbreak

    #max_var = maxvar(all_clauses)
    #print(max_var, file=sys.stderr)
    #print(max_orig_var, file=sys.stderr)
    #vt = vartable(F, s, vp)
    #for v in range(1, max_orig_var+1):
    #    print(f"{v}: {vt[v]}", file=sys.stderr)

    cubes = []

    return all_clauses, vp, max_orig_var, assumptions#, cubes

def resolve(C, D):
    clash_set = {x for x in C if -x in D}
    if len(clash_set) == 1:
        x = clash_set.pop()
        return (C | D) - {x, -x}
    else:
        return None

def make_predicates_abstract(vp):
    def clause_at(C, i):
        return vp.id(f"clause_at({C},{i})")
    def clause_until(C, i):
        return vp.id(f"clause_until({C},{i})")
    def clause_after(C, i):
        return vp.id(f"clause_after({C},{i})")
    def pair_until(C, D, i):
        return vp.id(f"pair_until({C},{D},{i})")
    def clause_available(C, i):
        return vp.id(f"clause_available({C},{i})")
    return clause_at, clause_until, clause_after, pair_until, clause_available

def ab(a, b):
    if a <= 1 and b <= 1:
        return a + b
    else:
        return max(a, b)

def hb(H, P, C, S=None):
    if len(P[C]) == 0:
        H[C] = 1
        return 1
    if C in H:
        return H[C]
    if S == None:
        S = set()
    H[C] = min((ab(hb(H, P, p[0], S=S|{C}), hb(H, P, p[1], S=S|{C})) + 1 for p in P[C] if len(set(p) & S) == 0), default = 1)
    return H[C]

def heuristic_lb(F, G, P, empty_clause):
    r = len(G)
    m = len(F.clauses)
    H = {C : 0 for C in range(m)}
    for C in range(m, r):
        #H[C] = min((hb(H[p[0]], H[p[1]]) + 1 for p in P[C]), default=1)
        hb(H, P, C)
        print(H[C])
    print("---")
    print(H[empty_clause])
    print(sum(H.values()))


def occurrence_dict(set_seq):
    occ = defaultdict(set)
    for i, S in enumerate(set_seq):
        for e in S:
            occ[e].add(i)
    return occ

def not_subsumed(set_seq):
    """
        assumes set_seq is in increasing cardinality order and without duplicates
    """
    occ = occurrence_dict(set_seq)
    subsumed = [False] * len(set_seq)
    #for i in range(len(set_seq)):
    for i, C in enumerate(set_seq):
        if not subsumed[i]:
            subsumed_by_current = functools.reduce(set.intersection, [occ[e] for e in C])
            for j in subsumed_by_current:
                if i < j:
                    subsumed[j] = True
    return [X for i, X in enumerate(set_seq) if not subsumed[i]]

def prod(A, B):
    return not_subsumed(sorted({a | b for a in A for b in B}, key=len))

debug_size=16
t_last=None
# TODO: short-circuit queries with S larger than some S already known
def all_derivations(C, P, subsumers, m, S=None, cache={}):
    """
        return all derivations of C (as a list of sets of clauses) that do not use clauses from S
    """
    global debug_size, t_last
    if C < m:
        return [frozenset()]
    if S == None:
        S = set()
    S |= subsumers[C]
    val = cache.get(C)
    if val != None:
        for S_cached, derivations in val:
            if S_cached == S:
                return derivations
            if S_cached < S:
                return [D for D in derivations if len(D & S) == 0]
    derivations_S = not_subsumed(
            sorted(
                (x | {C} for p in P[C] if len(set(p) & S) == 0 for x in prod(
                            all_derivations(p[0], P, subsumers, m, S=S|{C}),
                            all_derivations(p[1], P, subsumers, m, S=S|{C})
                        )),
                key=len
            )
        )
    if len(derivations_S) == 0:
        derivations_S = [frozenset([C])]
    if val != None:
        cache[C] = [(cS, cD) for cS, cD in val if not (len(S) < len(cS) and S < cS)] + [(S, derivations_S)]
        #cache[C].append((S, derivations_S))
    else:
        cache[C] = [(S, derivations_S)]
    num_deriv = sum(sum(len(D) for S, D in x) for x in cache.values())
    if num_deriv >= debug_size:
        cache_length = sum(len(c) for c in cache.values())
        #cache_subsumptions = sum(1 for x in cache.values() for i, (cS, D) in enumerate(x) for j in range(i+1, len(x)) if cS <= x[j][0] or x[j][0] <= cS) 
        print(f"cache length: {num_deriv} (caches sets: {cache_length}, cache clauses: {len(cache)})", end="")
        #print(f"cache length: {num_deriv} (caches sets: {cache_length}, cache_subsumptions: {cache_subsumptions}, cache clauses: {len(cache)})", end="")
        debug_size *= 2
        t_now = perf_counter()
        if t_last != None:
            print(f" doubling time: {t_now - t_last:.2f}")
        else:
            print()
        t_last = t_now
    #print([C, S, derivations_S])
    return derivations_S

# TODO: finish the implementation of the direct algorithm
def direct_shortest_proof(F, G, P, empty_clause):
    """
        F is the formula
        G are all not-trivially-subsumed reachable resolvents
        P is {C : [D, E if res(D, E) = C]}

        finds the shortest proof of F, assuming F is minimally unsatisfiable
    """
    r = len(G)
    m = len(F.clauses)
    subsumers = {C : frozenset(D for D in range(r) if G[D] < G[C]) for C in range(r)}
    AD = all_derivations(empty_clause, P, subsumers, m)
    s = 10**6
    mD = None
    for D in AD:
        if len(D) < s:
            s = len(D)
            mD = D
    return mD
    # O is the open set of vertices whose all derivations have been found, but
    # which have not been processed yet
    #O = [C for C in range(m, r) if len(P[C]) == 0]
    #CL = {range(m)}
    ## L storest a list of derivations as sets of clauses for every clause (excluding the target and axioms)
    #L = defaultdict(list)
    #while O:
    #    C = O.pop()
        

def enumerate_resolvents(F):
    n = len(F.exivars | F.univars)
    G = [set(C) for C in F.clauses]
    P = defaultdict(list)
    m = len(G)

    for i in range(m):
        for j in range(i+1, m):
            R = resolve(G[i], G[j])
            if R == None:
                continue
            for k in range(m):
                if G[k] <= R:
                    break
            else:
                for k in range(m, len(G)):
                    if G[k] <= R:
                        break
                    if R <= G[k]:
                        G[k] = R
                        P[k] = [(i, j)]
                        break
                else:
                    G.append(R)
                    #P[len(G)-1] = [(i, j)]

    r = len(G)
    empty_clause = None

    i = m
    while i < len(G):
        for j in range(i):
            R = resolve(G[i], G[j])
            if R == None:
                continue
            # if subsumed by an axiom or a level-1 clause, we don't need R
            for k in range(r):
                if G[k] <= R:
                    break
            else:
                for k in range(r, len(G)):
                    if G[k] == R:
                        P[k].append((j, i))
                        break
                else:
                    G.append(R)
                    P[len(G)-1].append((j, i))
                    #print(f"c {len(F)}: " + " ".join(map(str, sorted(F[-1][0], key=abs))))
                    if len(R) == 0:
                        empty_clause = len(G) - 1
                    #else:
                    #    Q.append([-len(F)], weight=1)
        i += 1

    r = len(G)
    p = sum([len(p) for p in P.values()])
    b = len([(C, D) for C in range(r) for D in range(r) if G[C] < G[D]])

    print(f"--------------------------------------")
    print(f"* # reachable resolvents:      {r :6d}")
    print(f"* # parent pairs:              {p :6d}")
    print(f"* # proper subsumptions:       {b :6d}")
    print(f"--------------------------------------")

    return G, P, empty_clause


#def get_query_abstract(F, s, is_mu=True, known_lower_bound=None):
def get_query_abstract(F, G, P, empty_clause, s, is_mu=True, known_lower_bound=None):
    """
    An alternative encoding, where we first enumerate all possible reachable
    clauses and record their graph structure, and then encode the search for
    a proof on this abstract structure that forgets all about clause content.

    For now assuming no universal variables.

    A first-order summary of the encoding:
        clauses C, D, E range over [0, r-1], where r is the number of reachable clauses
        positions i, j range over [0, s-1], where s is the length of the proof we are looking for

    Encoding size:
      clauses = 2(3rs - r) + rs + (s-1)(r+p) + (s-1)b + sr(r-1)/2 + 3sp + m + 2
              = 8rs -3r + 4sp - p + sb - b + sr(r-1)/2 + m + 2
              = rs(8 + (r-1)/2) + s(4p + b) - 3r - p - b + m + 2
      vars    = 4rs + sp

    (C not empty and i != j)  =>  clause_at(C, i)  =>  not clause_at(C, j)
        variant with subsumption checking (including the possibility C=D):
            C <= D and i < j  =>  clause_at(C, i)  =>  not clause_at(D, j)
            
    clause_until(C, i)     =  clause_until(C, i-1) or clause_at(C, i)
    clause_after(C, i)     =  clause_after(C, i+1) or clause_at(C, i)
    pair_until(C, D, i)    =  clause_until(C, i) and clause_until(D, i)
    clause_available(C, i) =  OR_{D, E parents of C} pair_until(D, E, i-1)
    clause_at(C, i)        => clause_available(C, i)

    symmetry breaking:
        (we cannot pick the larger clause D when C is also available and we want to use it later)
    
    C << D  =>  clause_available(C, i) and clause_available(D, i) and clause_at(D, i) => not clause_after(C, i+1)

    Requirements:
        we need to maintain subsumption information for the subsumtion checking constraint
        and a total order <<, which will simply be given by the order in which the clauses are found
    """

    # a list of all derivable clauses minus ones subsumed by either
    # an axiom or a level-1 clause (a resolvent of two axioms)
    # TODO: this is for MU only: level-1 clauses can always be introduced unconditionally,
    # because all preconditions are always met, so anything subsumed is superfluous
    n = len(F.exivars | F.univars)
    m = len(F.clauses)
    Q = CNF()
    vp = IDPool()
    clause_at, clause_until, clause_after, pair_until, clause_available = make_predicates_abstract(vp)

    r = len(G)

    clauses_of_size = [set() for i in range(n+1)]

    if is_mu:
        for i in range(m):
            #print(f"c {i+1}: " + " ".join(map(str, sorted(F[i][0], key=abs))))
            Q.append([clause_at(i, i)])

    if empty_clause == None:
        print("ERROR: cannot derive the empty clause; input satisfiable?")
        sys.exit(-1)

    Q.append([clause_at(empty_clause, s-1)])
    if known_lower_bound != None:
        Q.append([-clause_until(empty_clause, known_lower_bound-2)])

    for C in range(r):
        clauses_of_size[len(G[C])].add(C)

    for C in range(r):
        # 3rs - r clauses
        Q.append([ clause_until(C, 0), -clause_at(C, 0)])
        Q.append([-clause_until(C, 0),  clause_at(C, 0)])
        for i in range(1, s):
            Q.append([ clause_until(C, i), -clause_at(C, i)])
            Q.append([ clause_until(C, i), -clause_until(C, i-1)])
            Q.append([-clause_until(C, i),  clause_until(C, i-1), clause_at(C, i)])

        # 3rs - r clauses
        Q.append([ clause_after(C, s-1), -clause_at(C, s-1)])
        Q.append([-clause_after(C, s-1),  clause_at(C, s-1)])
        for i in range(s-1):
            Q.append([ clause_after(C, i), -clause_at(C, i)])
            Q.append([ clause_after(C, i), -clause_after(C, i+1)])
            Q.append([-clause_after(C, i),  clause_after(C, i+1), clause_at(C, i)])

        # rs clauses
        for i in range(s):
            Q.append([-clause_at(C, i), clause_available(C, i)])

        # optional
        for i in range(m, s-1):
            Q.append([-clause_available(C, i), clause_available(C, i+1)])


        # (r-1)(s-1) clauses
        if C != empty_clause:
            for i in range(s-1):
                Q.append([-clause_at(C, i), -clause_after(C, i+1)])

    size_basic = len(Q.clauses)
    size = len(Q.clauses)
    
    # 2sp clauses
    for parent_list in P.values():
        for D, E in parent_list:
            for i in range(1, s):
                Q.append([-pair_until(D, E, i),  clause_until(D, i)])
                Q.append([-pair_until(D, E, i),  clause_until(E, i)])
                Q.append([ pair_until(D, E, i), -clause_until(D, i), -clause_until(E, i)])
            # optional
            for i in range(1, s-1):
                Q.append([-pair_until(D, E, i), pair_until(D, E, i+1)])
                Q.append([-pair_until(D, E, i), clause_until(D, i-1), clause_until(E, i-1)])

    # assuming mu here
    # (s-1)(r+p) clauses
    for C in range(m):
        for i in range(m):
            Q.append([clause_available(C, i)])
        for i in range(m, s):
            Q.append([-clause_available(C, i)])
    for C in range(m, r):
        # non-axiom
        for i in range(m):
            Q.append([-clause_available(C, i)])
        if len(P[C]) == 0:
            # level-1 clause
            for i in range(m, s):
                Q.append([clause_available(C, i)])
        else:
            for i in range(m, s):
                Q.append([-clause_available(C, i)] + [pair_until(D, E, i-1) for D, E in P[C]])
                for D, E, in P[C]:
                    Q.append([clause_available(C, i), -pair_until(D, E, i-1)])

    size_structure = len(Q.clauses) - size
    size = len(Q.clauses)

    # as soon as a clause becomes available, no strict superset should ever be derived
    # sb clauses (b = number of strict subsumptions)
    for C in range(r):
        for D in range(r):
            if G[C] < G[D]:
                for i in range(s):
                    Q.append([-clause_available(C, i), -clause_after(D, i)])

    size_subsum = len(Q.clauses) - size
    size = len(Q.clauses)

    # symmetry breaking + only one clause at any given spot
    # sr(r-1)/2 clauses
    for C in range(r):
        for D in range(C+1, r):
            # if C is available and you want to use it at i or later, then you shouldn't pick
            # the lexicographically larger D
            for i in range(s):
                Q.append([-clause_available(C, i), -clause_at(D, i), -clause_after(C, i)])

    for C in range(r):
        for D in range(C+1, r):
            for i in range(s):
                Q.append([-clause_at(C, i), -clause_at(D, i)])

    size_symbreak = len(Q.clauses) - size
    size = len(Q.clauses)

    l = 1
    if known_lower_bound != None:
        l = known_lower_bound - 1

    S = clauses_of_size[0]
    for k in range(1, n):
        S |= clauses_of_size[k]
        for i in range(l, s):
            Q.append([-clause_at(empty_clause, i)] + [clause_at(C, i-k) for C in S])

    for i in range(m, s-n-1):
        Q.append([clause_at(C, i) for C in range(r)])

    size_cardbound = len(Q.clauses) - size
    size = len(Q.clauses)

    # TODO: add a constraint that every clause must be used: for every clause, explicitly enumerate
    # all clauses that it can directly resolve to, and say that one of them should appear afterwards
    #for i in range(m, s):
    #    Q.clauses.extend(CardEnc.atmost([clause_after(C, i) for C in range(r)], s-i, vpool=vp).clauses)

    ## DEBUG constraint: see if the encoding allows no clause in a place
    ##Q.clauses.extend([[-clause_at(C, m+1)] for C in range(r)])

    #size_useclause = len(Q.clauses) - size
    #size = len(Q.clauses)

    num_vars = Q.nv
    print(f"* predicted query size:    {size: 9d} clauses, {num_vars} vars")
    print(f"* basic constraint size:       {size_basic: 9d} clauses ({100*size_basic/size:.2g}%)")
    print(f"* structure constraint size:   {size_structure: 9d} clauses ({100*size_structure/size:.2g}%)")
    print(f"* subsumption constraint size: {size_subsum: 9d} clauses ({100*size_subsum/size:.2g}%)")
    print(f"* symbreaking constraint size: {size_symbreak: 9d} clauses ({100*size_symbreak/size:.2g}%)")
    print(f"* cardbound constraint size:   {size_cardbound: 9d} clauses ({100*size_cardbound/size:.2g}%)")
    #print(f"* useclause constraint size:   {size_useclause: 9d} clauses ({100*size_useclause/size:.2g}%)")
        
    return Q.clauses, vp

# TODO: fix to work for non-mu as well, return the proof in some more versatile format
def get_found_proof(model, F, s, vp):
    variables = sorted(F.exivars | F.univars)
    m = len(F.clauses)
    pos, neg, empty, piv, ax, isax, arc, exarc, upos, uneg, poscarry, negcarry, posdrop, negdrop =\
            make_predicates(vp)

    proof_string = "["
    proof_length = m
    mset = set(model)
    for i in range(m, s):
        proof_length += 1
        parents = []
        for y in range(i):
            if arc(y, i) in mset:
                parents.append(str(y + 1))
        proof_string += ",".join(parents) 
        if empty(i) not in mset:
            proof_string += ";"
        else:
            break
    proof_string += "]"
    return proof_string, proof_length


#def has_short_proof(F, s, is_mu, options, time_limit = None, known_lower_bound=None):
#    pass
def has_short_proof(F, l, u, is_mu=False, options=Options(), time_limit=None, G=None, P=None, empty_clause=None, var_orbits=None, sub_orbits=None):
    """
    Searches for a resolution proof of F of length s, where
        l <= s <= u
    Incremental linear search will call this method with u=l for increasing values of l.
    If a proof P of length s is found, returns the tuple
        True, P, s, t
    if no proof exists, returns the tuple
        False, None, None, t
    and otherwise returns
        None, None, None, t
    where t is the time taken.
    """

    # TODO: make sure it works correctly even for non-MU, etc.
    if u <= 2:
        # the only way there can be such a short proof is
        # if the matrix contains the empty clause
        #return min(len(c) for c in f.clauses) == 0
        if not all(F.clauses):
            return True, "[]", 1, 0.0
        else:
            return False, None, None, 0.0

    if options.verbosity >= 1:
        verb_query_begin(u)

    t_begin = perf_counter()

    assumptions=None
    if options.enc == "traditional":
        if var_orbits != None:
            # if we're specifying variable orbits, we must be looking for a proof of exact length for
            # technical reasons. The purpose of specifying orbits is to break the problem down by
            # the last resolution step (possibly more than just that) in order to parallelize. In that
            # case, do parallelize over proof lengths as well... it would require some substantial changes
            # to the encoding to allow fixing a suffix of the proof while allowing slack in proof length
            if l < u:
                print(f"WARNING: proof length lower bound does not match upper bound (l={l}, u={u})", file=sys.stderr)
                print(f"         when variable orbits are calculated and proof suffix is fixed, length must be exact", file=sys.stderr)
                print(f"         setting l={u}", file=sys.stderr)
                l = u
        query_clauses, vp, max_orig_var, assumptions = get_query(F, u, is_mu, options.cardnum, options.ldq, known_lower_bound=l, var_orbits=var_orbits, sub_orbits=sub_orbits, orbit_mode=options.orbit_mode, suborbit_mode=options.suborbit_mode)
    elif options.enc == "projected":
        query_clauses, vp = get_query_abstract(F, G, P, empty_clause, u, is_mu, known_lower_bound=l)

    t_end = perf_counter()

    if options.verbosity >= 1:
        verb_query_end(maxvar(query_clauses), len(query_clauses), size(query_clauses), t_end-t_begin)
    
    solver_wrapper = SolverWrapper(options.sat_solver, query_clauses, options.cnf, u)
    del query_clauses

    solver_wrapper.solve(time_limit=time_limit, assumptions=assumptions)
    if solver_wrapper.ans != None and options.verbosity >= 1:
        print(f"* Solved. ({solver_wrapper.time:.5g} sec)")
        sys.stdout.flush()

    P = None
    s = None
    if solver_wrapper.ans == True:
        if options.enc == "traditional":
            P, s = get_found_proof(solver_wrapper.model, F, u, vp)
        else:
            s = u
        if options.verbosity >= 1:
            print( "--------------------------------------")
            print(f"  Proof of length {s} found:")
            print()
            if options.enc == "traditional":
                reconstruct(solver_wrapper.model, F, u, vp)
            else:
                reconstruct_projected(solver_wrapper.model, s, vp, G)
                #print("* reconstrunction of the found proof unavailable")
            print( "--------------------------------------")

    return solver_wrapper.ans, P, s, solver_wrapper.time

def count_short_proofs(F, s, is_mu, options):
    """
    This function takes a CNF formula F and an integer s,
    and counts the number of resolution refutations of F
    whose length is at most s.
    """

    if s <= 2:
        # the only way there can be such a short proof is
        # if the matrix contains an empty clause
        return 1 if min(len(c) for c in f.clauses) == 0 else 0

    if options.verbosity >= 1:
        verb_query_begin(s)

    t_begin = perf_counter()
    query_clauses, vp, max_orig_var, assumptions = get_query(F, s, is_mu, options.cardnum)
    t_end = perf_counter()

    if options.verbosity >= 1:
        verb_query_end(maxvar(query_clauses), len(query_clauses), size(query_clauses), t_end-t_begin)

    solver = Solver(name=options.sat_solver, bootstrap_with=query_clauses)
    del query_clauses

    t = perf_counter()
    proofs = 0
    last_model = None

    if options.verbosity >= 1:
        print(f"Max orig var: {max_orig_var}")
    vt = vartable(F, s, vp)
    #print(sorted(vt))

    while solver.solve():
        proofs += 1
        model = solver.get_model()
        banning_clause = [-x for x in model if abs(x) <= max_orig_var]
        solver.add_clause(banning_clause)
        if last_model != None:
            #print("-------")
            #print(model)
            if options.verbosity >= 1:
                really_differs = False
                print("new model differs in: ", end="")
                for i in range(len(model)):
                    if model[i] != last_model[i]:
                        varname = vt.get(model[i], None)
                        if varname != None:
                            print(varname, end=" ")
                            really_differs = True
                        else:
                            print(model[i], end=" ")
                print()
                if options.verbosity >= 2:
                    reconstruct(model, n, m, s, vp)
        else:
            #print(model)
            if options.verbosity >= 2:
                reconstruct(model, F, s, vp)
        last_model = model

    return proofs


def find_shortest_proof(F, is_mu, options=Options(), lower_bound=None, upper_bound=None, time_budget=None, G=None, parents=None, empty_clause=None, var_orbits=None, sub_orbits=None):
    """
    This function takes a CNF formula f and by asking queries
    to has_short_proof determines the shortest proof that f has.
    """

    global machine_summary

    t_begin = perf_counter()

    if options.verbosity >= 1:
        print( "--------------------------------------")
        print( "* Finding shortest proof")
        print( "--------------------------------------")
        #print(f"* SAT solver: {options.sat_solver:>16}")
        print(f"* SAT solver:          {options.sat_solver}")
        print(f"* Cardnality encoding: {options.card} ")
        print( "* Formula: ")
        print()
        draw_formula(F)
        print( "--------------------------------------")

    # lower bound on the length of the proof
    l = 1
    if is_mu:
        # the shortest possible proof of an MU formula is read-once
        l = 2*len(F.clauses)-1
        if options.verbosity >= 1:
            print("*  The formula is MU     ")
            print("*  - using all axioms    ")
            print("*  - starting at s=2m-1  ")
            print("--------------------------------------")

    if lower_bound != None and lower_bound > l:
        l = lower_bound
        if options.verbosity >= 1:
            print("* user lower bound = {l}")
            print("--------------------------------------")

    u = upper_bound
    if u == None:
        u = l

    # TODO: implement binary search
    query_time = {}
    ans = None
    P = None
    t = 0.0
    t0 = perf_counter()
    try:
        ans, P, s, t = has_short_proof(F, l, u, is_mu=is_mu, options=options, time_limit=time_budget, G=G, P=parents, empty_clause=empty_clause, var_orbits=var_orbits, sub_orbits=sub_orbits)
        while ans == False:
            query_time[u] = t
            if options.verbosity >= 1:
                print(f"* No proof of length {u}")
                print("--------------------------------------")
            l += 1
            u += 1
            if time_budget != None:
                time_budget -= int(t)
            ans, P, s, t = has_short_proof(F, l, u, is_mu=is_mu, options=options, time_limit=time_budget, G=G, P=parents, empty_clause=empty_clause, var_orbits=var_orbits, sub_orbits=sub_orbits)
    except pysolvers.error:
        if options.verbosity >= 1 and sys.stdout.isatty():
            print(end="\r")
            print("* Aborted.")
            print(f"* No answer for length {u}")
            print("--------------------------------------")
        t = perf_counter() - t0
        ans = None

    query_time[u] = t

    t_end = perf_counter()
    if options.verbosity >= 1:
        print(f"* Time: {t_end - t_begin}")
        if ans == True:
            print(f"* Shortest proof found: {u}")
        elif ans == None:
            print(f"* Time out. Lower bound: {u}")

    if ans == True:
        machine_summary += f",OPT,{u},{t_end-t_begin:.2f}"
    elif ans == None:
        machine_summary += f",LB,{u},{t_end-t_begin:.2f}"

    return P, u, query_time

def read_proof_structure(prooffile):
    arcset = set()
    size = 0
    with open(prooffile) as pfp:
        for line in pfp:
            size += 1
            tokens = list(map(int, line.split()))
            current = tokens[0]
            idx = tokens.index(0) + 1
            while idx < len(tokens) and tokens[idx] != 0:
                arcset.add((tokens[idx], current))
                idx += 1
    return size, arcset

def assume_proof(arcset, vp):
    def arc(i, j):
        return vp.id(f"arc[{i},{j}]")
    return [arc(i-1, j-1) for i, j in arcset]


def main():
    if sys.version_info.major < 3 or sys.version_info.minor < 6:
        print("This script makes extensive use of f-strings"
                "[https://docs.python.org/3/tutorial/inputoutput.html#tut-f-strings],"
                "and as such requires Python version >= 3.6.")
        print("You appear to be running version %d.%d."
                % (sys.version_info.major, sys.version_info.major))
        sys.exit(36)

    global machine_summary

    parser = argparse.ArgumentParser()
    mu_group = parser.add_mutually_exclusive_group()
    parser.add_argument("cnf",
            help="filename of the formula whose shortest proof is to be determined")
    parser.add_argument("--sat-solver",
            help="specify which SAT solver to use. Valid choices are cadical, glucose, lingeling, maplesat, minisat for solvers provided by PySAT, or the name of the executable of any other SAT solver installed", default="cadical"#, choices=["cadical", "glucose", "lingeling", "maplesat", "minisat"]
            ) #TODO: check whether an external solver is a valid executable?
    parser.add_argument("--query",
            type=int,
            help="don't compute the shortest proof, only display the query formula")
    parser.add_argument("--card",
            help="type of cardinality constraint to use",
            default="seqcounter",
            choices=[
                "seqcounter",
                "sortnetwrk",
                "cardnetwrk",
                "totalizer",
                "mtotalizer",
                "kmtotalizer"])
    parser.add_argument("--enc",
            help="type of encoding",
            default="traditional",
            choices=[
                "traditional",
                "projected"])
    parser.add_argument("--count",
            type=int,
            help="count the number of shortest proofs")
    parser.add_argument("--lower-bound", "-l",
            type=int,
            help=" a lower bound on shortest proof length (no strictly shorter proof exists)")
    parser.add_argument("--upper-bound", "-u",
            type=int,
            help="an upper bound on shortest proof length (a proof of this length is known to exist)")
    parser.add_argument("--has",
            type=int,
            help="determine whether a proof of at most this length exists")
    parser.add_argument("--binary-search", "-b",
            action="store_true",
            help="apply binary search in the interval [l, u). If u is unknown, try values l + 2^n until SAT")
    parser.add_argument("--time-limit", "-t",
            type=int,
            help="time limit for the entire computation in seconds (only works with built-in minisat, glucose, and maplesat)")
    parser.add_argument("--ldq",
            action="store_true",
            help="search for long-distance Q-resolution proofs")
    parser.add_argument("--reductionless",
            action="store_true",
            help="disallow intermediate universal reductions in the proof (needs --ldq to be complete)")
    mu_group.add_argument("--mu",
            action="store_true",
            help="skip the minimal unsatisfiability check and assume the formula is MU")
    mu_group.add_argument("--not-mu",
            action="store_true",
            help="skip the minimal unsatisfiability check and assume the formula is not MU")
    mu_group.add_argument("--test",
            action="store_true",
            help="test the correctness of the encoding. Assumes the existence of the file CNF.proof")
    parser.add_argument("-v", "--verbosity",
            default=1,
            action="count",
            help="increase verbosity")
    parser.add_argument("-q", "--quiet",
            action="store_true",
            help="disable additional output")

    options = parser.parse_args()
    
    if options.quiet:
        options.verbosity = 0

    options.cardnum = {
            "seqcounter"  : EncType.seqcounter,
            "sortnetwrk"  : EncType.sortnetwrk,
            "cardnetwrk"  : EncType.sortnetwrk,
            "totalizer"   : EncType.totalizer,
            "mtotalizer"  : EncType.mtotalizer,
            "kmtotalizer" : EncType.kmtotalizer
            }[options.card]

    if options.sat_solver == "glucose":
        options.sat_solver = "glucose4"
    elif options.sat_solver == "minisat":
        options.sat_solver = "minisat22"

    #F = CNF(from_file=options.cnf)
    F = read_formula(options.cnf, options.reductionless)
    machine_summary += f"{options.cnf},{len(F.exivars) + len(F.univars)},{len(F.clauses)},{sum(len(cl) for cl in F.clauses)}"

    # instead of changing the constraints, we implement reductionless
    # long-distance Q-resolution simply by saying that all existential
    # variables block every universal variable, and hence reduction is
    # only possible at the end. Notice that for merging, we use F.unideps,
    # which is left unchanged, and so illegal merges are detected correctly.
    if options.reductionless:
        for u in F.univars:
            F.uniblockers[u] = F.exivars

    is_mu = False
    if options.mu:
        is_mu = True
    elif not options.not_mu:
        if not is_unsat(F):
            print("ERROR: Input formula is satisfiable.", file=sys.stderr)
            sys.exit(-1)
        is_mu = is_minimal(F)

    l = 2*len(F.clauses) - 1 if is_mu else 1
    if options.lower_bound != None:
        l = options.lower_bound

    G, P, empty_clause = None, None, None
    if options.enc == "projected":
        G, P, empty_clause = enumerate_resolvents(F)
        if empty_clause == None:
            print("ERROR: cannot derive the empty clause; input satisfiable?")
            sys.exit(-1)
        #heuristic_lb(F, G, P, empty_clause)
        proof = direct_shortest_proof(F, G, P, empty_clause)
        print(proof)
        print(len(proof))

    if options.test:
        # test the correctness of lower bounds produce by --has
        # reads an existing proof, then tries to plug it into longer queries to see if it satisfies them
        num_test_cases = 10
        size, proof_DAG = read_proof_structure(options.cnf + ".proof")
        for i in range(size, size+num_test_cases):
            Q, vp, mvar, assumptions = get_query(F, size, is_mu, options.cardnum, options.ldq, known_lower_bound=l) 
            s = Solver(name="cadical", bootstrap_with=Q)
            if s.solve(assumptions=assume_proof(proof_DAG, vp)) == False:
                print(f"query {size} unsatisfiable")
                print("FAILED")
                break
        else:
            print("PASSED")
    elif options.query:
        if options.enc == "traditional":
            print_formula(get_query(F, options.query, is_mu, options.cardnum, options.ldq, known_lower_bound=l)[0])
        elif options.enc == "projected":
            print_formula(get_query_abstract(F, G, P, empty_clause, options.query, is_mu, known_lower_bound=options.query)[0])
    elif options.has != None:
        ans, P, s, t = has_short_proof(F, l, options.has, is_mu, options, options.time_limit, G=G, P=P, empty_clause=empty_clause)
        if ans == False:
            if options.verbosity:
                print(f"No proof of length ≤ {options.has}")
            print(f"LB _ {options.has+1} {t:.2f}s")
        elif ans == True:
            print(f"UB {P} {s} {t:.2f}s")
        sys.exit(s)
    elif options.count:
        print(count_short_proofs(F, options.count, is_mu, options))
    else:
        P, shortest, query_time = find_shortest_proof(F, is_mu, options, lower_bound=options.lower_bound, upper_bound=options.upper_bound, time_budget=options.time_limit, G=G, parents=P, empty_clause=empty_clause)
        print(machine_summary)
        sys.exit(shortest)

if __name__ == "__main__":
    main()

