#!/usr/bin/env python3

from pysat.card import CardEnc, EncType
from pysat.formula import CNF, IDPool
from pysat.solvers import Solver, Lingeling, Glucose4, Minisat22, Cadical
from time import perf_counter

import sys
import math
import argparse

machine_summary = ""

class Formula:
    def __init__(self):
        self.clauses = []
        self.exivars = set()
        self.univars = set()
        # unideps maps u to existential variables left of u
        self.unideps = {}
        # uniblockers maps u to existential variables right of u
        self.uniblockers = {}

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


def implies(preconditions, postconditions):
    """
    Returns a set of clauses that encode that the
    conjunction of preconditions implies the conjunction
    of postconditions
    """
    neg_preconditions = [-x for x in preconditions]
    return [neg_preconditions + [x] for x in postconditions]

def maxvar(clauses):
    return max(max(abs(lit) for lit in clause) for clause in clauses)

def size(F):
    return sum(len(c) for c in F)

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
    return pos, neg, piv, ax, isax, arc, exarc, upos, uneg, poscarry, negcarry, posdrop, negdrop

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
    pos, neg, piv, ax, isax, arc, exarc, upos, uneg, poscarry, negcarry, posdrop, negdrop =\
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
        print(f"{i+1:2d}: {strcl:<15}  {(strxioms if axioms else strents)}")

def definitions(F, s, is_mu, vp):

    variables = sorted(F.exivars | F.univars)
    n = len(variables)
    m = len(F.clauses)
    fset = [set(C) for C in F.clauses]
    pos, neg, piv, ax, isax, arc, exarc, upos, uneg, poscarry, negcarry, posdrop, negdrop =\
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

    return definition_clauses


def essentials(F, s, is_mu, vp, ldq):

    variables = sorted(F.exivars | F.univars)
    n = len(variables)
    m = len(F.clauses)
    pos, neg, piv, ax, isax, arc, exarc, upos, uneg, poscarry, negcarry, posdrop, negdrop =\
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
    # this cardinality constraint uses no auxiliary variables
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


    # the last clause is empty
    essential_clauses += [[-pos(s-1, v)] for v in variables] +\
                   [[-neg(s-1, v)] for v in variables]

    return essential_clauses

def axiom_placement_clauses(F, s, is_mu, vp):

    variables = sorted(F.exivars | F.univars)
    n = len(variables)
    m = len(F.clauses)
    axioms = range(m)
    pos, neg, piv, ax, isax, arc, exarc, upos, uneg, poscarry, negcarry, posdrop, negdrop =\
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

def redundancy(F, s, is_mu, vp, card_encoding):

    variables = sorted(F.exivars | F.univars)
    n = len(variables)
    m = len(F.clauses)

    redundant_clauses = []
    pos, neg, piv, ax, isax, arc, exarc, upos, uneg, poscarry, negcarry, posdrop, negdrop =\
            make_predicates(vp)

    # when successively incrementing s, we know that every clause must be used
    redundant_clauses += [[arc(i, j) for j in range(i+1, s)] for i in range(s-1)]

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
                        for j in range(i+1, s-1)
                            for k in range(j+1, s)]
            redundant_clauses += [[-exarc(i, j), arc(i, j)]
                    for i in range(s-2)
                        for j in range(i+2, s)]
            redundant_clauses += [[-exarc(i, k)] + [arc(i, j) for j in range(i+1, k)]
                        for i in range(s-2)
                            for k in range(i+2, s)]

            # limit the number of extra arcs to s - 2m + 1
            redundant_clauses += CardEnc.atmost(
                    [exarc(i, j) for i in range(s-2) for j in range(i+2, s)],
                    bound=s-2*m+1,
                    encoding=card_encoding,
                    vpool=vp).clauses

    return redundant_clauses

def symmetry_breaking(F, s, is_mu, vp):

    pos, neg, piv, ax, isax, arc, exarc, upos, uneg, poscarry, negcarry, posdrop, negdrop =\
            make_predicates(vp)
    variables = sorted(F.exivars | F.univars)
    lits = sorted(variables + [-v for v in variables], key=lambda lit: (abs(lit), -lit))
    n = len(variables)
    m = len(F.clauses)

    symbreak = []

    # lexicographic ordering of consecutive clauses


    # geq[i,j,l] says that all literals up to and including position l,
    # are greater than or equal in clause j than in clause i
    def geq(i, j, l):
        return vp.id(f"geq[{i},{j},{l}]")

    prd = pos if lits[0] > 0 else neg
    v = abs(lits[0])
    symbreak += [c for i in range(s-1) for j in range(i+1, s) for c in [
                [-geq(i, j, lits[0]), -prd(i, v), prd(j, v)],
                [ geq(i, j, lits[0]), -prd(j, v)],
                [ geq(i, j, lits[0]),  prd(i, v)],
            ]
        ]
    for i in range(s-1):
        for j in range(i+1, s):
            for k in range(1, len(lits)):
                prd = pos if lits[k] > 0 else neg
                v = abs(lits[k])
                symbreak.extend([
                    [-geq(i, j, lits[k]),  geq(i, j,  lits[k-1])],
                    [-geq(i, j, lits[k]), -prd(i, v),  prd(j, v)],
                    [ geq(i, j, lits[k]), -geq(i, j,  lits[k-1]), -prd(j, v)],
                    [ geq(i, j, lits[k]), -geq(i, j,  lits[k-1]),  prd(i, v)],
                ])

    # simultaneous source property
    # sim[i,j] says that the if the clauses are being removed in this order,
    # at the time of removal of i (when i is a source), j is also a source
    def sim(i, j):
        return vp.id(f"sim[{i},{j}]")

    symbreak += [[ sim(i, i+1),  arc(i, i+1)] for i in range(s-1)] +\
                [[-sim(i, i+1), -arc(i, i+1)] for i in range(s-1)]

    # ϴ(s^2·n) clauses
    # ϴ(s^2·n) literals
    for i in range(s-2):
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
    for i in range(s-1):
        for j in range(i+1, s):
            symbreak.append([-sim(i, j), isax(i), first_prd(i, first_v), -first_prd(j, first_v)])
            for k in range(len(lits) - 1):
                prd = pos if lits[k] > 0 else neg
                v = abs(lits[k])
                symbreak.append([-sim(i, j), isax(i), -geq(i, j, lits[k]), prd(i, v), -prd(j, v)])
            symbreak.append([-geq(i, j, lits[-1])])

    # only for variable-transitive formulas, such as PHP: last clause must always be unit, so
    # we fix the variable in that clause to be x_{n-1}, because those are the smallest clauses
    # in the lexicographic ordering

    #symbreak += [[pos(s-2, variables[-1]), neg(s-2, variables[-1])]] +\
    #        [[-pos(s-2, v)] for v in variables[:-1]] +\
    #        [[-neg(s-2, v)] for v in variables[:-1]]


    return symbreak


def get_query(F, s, is_mu, card_encoding, ldq):
    """
    This function takes a CNF formula F and an integer s,
    and returns clauses that encode the statement:

    Does F have a resolution refutation of length at most s?

    WARNING: for optimisation reasons, the clauses currently
    returned say "F has a resolution refutation of length exactly s"

    It also returns lists of variables that are useful in order
    to recover the found proof.
    """

    variables = sorted(F.exivars | F.univars)
    n = len(variables)
    m = len(F.clauses)

    vp = IDPool()

    # clauses in the proof are indexed starting from 0

    # some helper notation
    axioms = range(m)
    proof_clauses = range(s)

    pos, neg, piv, ax, isax, arc, exarc, upos, uneg, poscarry, negcarry, posdrop, negdrop =\
            make_predicates(vp)

    definition_clauses = definitions(F, s, is_mu, vp)

    essential_clauses = essentials(F, s, is_mu, vp, ldq)

    ############### REDUNDANCY ###############

    redundant_clauses = redundancy(F, s, is_mu, vp, card_encoding)

    ############### SYMMETRY BREAKING ###############

    axiom_placement = axiom_placement_clauses(F, s, is_mu, vp)

    symbreak = symmetry_breaking(F, s, is_mu, vp)

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

    return all_clauses, vp, max_orig_var

def has_short_proof(F, s, is_mu, options):
    """
    This function takes a CNF formula f and an integer s,
    and returns true iff f has a resolution refutation of
    length at most s.
    """

    if s <= 2:
        # the only way there can be such a short proof is
        # if the matrix contains the empty clause
        #return min(len(c) for c in f.clauses) == 0
        return not all(f.clauses)

    if options.verbosity >= 1:
        verb_query_begin(s)

    t_begin = perf_counter()

    query_clauses, vp, max_orig_var = get_query(F, s, is_mu, options.cardnum, options.ldq)

    t_end = perf_counter()

    if options.verbosity >= 1:
        verb_query_end(maxvar(query_clauses), len(query_clauses), size(query_clauses), t_end-t_begin)
    
    solver = Solver(name=options.sat_solver, bootstrap_with=query_clauses)
    del query_clauses

    t_begin = perf_counter()
    ans = solver.solve()
    t_end = perf_counter()
    if options.verbosity >= 1:
        print(f"* Solved. ({t_end-t_begin:.5g} sec)")
        sys.stdout.flush()

    if ans:
        model = solver.get_model()
        if options.verbosity >= 1:
            print( "--------------------------------------")
            print(f"  Proof of length {s} found:")
            print()
            reconstruct(model, F, s, vp)
            print( "--------------------------------------")

    return ans

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
    query_clauses, vp, max_orig_var = get_query(F, s, is_mu, options.cardnum)
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


def find_shortest_proof(F, is_mu, options):
    """
    This function takes a CNF formula f and by asking queries
    to has_short_proof determines the shortest proof that f has.
    """

    global machine_summary

    t_begin = perf_counter()

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

    # length of the proof
    s = 1
    if is_mu:
        # the shortest possible proof of an MU formula is read-once
        s = 2*len(F.clauses)-1
        if options.verbosity >= 1:
            print("*  The formula is MU     ")
            print("*  - using all axioms    ")
            print("*  - starting at s=2m-1  ")
            print("--------------------------------------")

    while not has_short_proof(F, s, is_mu, options):
        if options.verbosity >= 1:
            print(f"* No proof of length {s}")
            print("--------------------------------------")
        s += 1

    t_end = perf_counter()
    print(f"* Time: {t_end - t_begin}")
    print(f"* Shortest proof found: {s}")

    # update machine-readable summary
    machine_summary += f",{s},{t_end-t_begin}"
    return s


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
            help="specify which SAT solver to use", default="cadical", choices=[
                "cadical",
                "glucose",
                "lingeling",
                "maplesat",
                "minisat"])
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
    parser.add_argument("--count",
            type=int,
            help="count the number of shortest proofs")
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
    parser.add_argument("-v", "--verbosity",
            default=0,
            action="count",
            help="increase verbosity")

    options = parser.parse_args()

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
    machine_summary += f"{options.cnf},{len(F.exivars) + len(F.univars)},{len(F.clauses)},{sum(len(cl) for cl in F.clauses)},graph6"

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


    if options.query:
        print_formula(get_query(F, options.query, is_mu, options.cardnum, options.ldq)[0])
    elif options.count:
        print(count_short_proofs(F, options.count, is_mu, options))
    else:
        shortest = find_shortest_proof(F, is_mu, options)
        print(machine_summary)
        sys.exit(shortest)

if __name__ == "__main__":
    main()

