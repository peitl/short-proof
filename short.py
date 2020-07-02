#!/usr/bin/env python3

from pysat.card import CardEnc, EncType
from pysat.formula import CNF, IDPool
from pysat.solvers import Solver, Lingeling, Glucose4, Minisat22, Cadical
from time import clock

import sys
import math
import argparse

def implies(preconditions, postconditions):
    """
    Returns a set of clauses that encode that the
    conjunction of preconditions implies the conjunction
    of postconditions
    """
    neg_preconditions = [-x for x in preconditions]
    return [neg_preconditions + [x] for x in postconditions]

def maxvar(F):
    return max(max(abs(lit) for lit in clause) for clause in F)

def size(F):
    return sum(len(c) for c in F)

def print_formula(F):
    print(f"p cnf {maxvar(F)} {len(F)}")
    print("".join((" ".join(map(str, clause)) + " 0\n") for clause in F), end="")

def draw_formula(F, padding="  "):
    for cl in F:
        print(padding, end="")
        cl_string = [" "] * maxvar(F)
        for lit in cl:
            if lit < 0:
                cl_string[abs(lit) - 1] = "-"
            else:
                cl_string[abs(lit) - 1] = "+"
        print("".join(cl_string))


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
    clause_vars = list(range(max_var + 1, max_var + len(f.clauses) + 1))
    solver = Lingeling(bootstrap_with=[c + [-clause_vars[i]] for i, c in enumerate(F.clauses)])
    for i in range(len(F.clauses)):
        clause_vars[i] *= -1
        ans = solver.solve(assumptions=clause_vars)
        clause_vars[i] *= -1
        if not ans:
            return False
    return True

def make_wrappers(vp):
    def pos(i, v):
        return vp.id(f"pos[{i},{v}]")
    def neg(i, v):
        return vp.id(f"neg[{i},{v}]")
    def piv(i, v):
        return vp.id(f"piv[{i},{v}]")
    def ax(i, j):
        return vp.id(f"ax[{i},{j}]")
    def isax(i):
        return vp.id(f"isax[{i}]")
    def arc(i, j):
        return vp.id(f"arc[{i},{j}]")
    return pos, neg, piv, ax, isax, arc

def vartable(vp, n, m, s):
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
        for name in names_cl_var for i in range(s) for v in range(n)      for pol in range(pol_num)})
    vt.update({pol_int[pol] * vp.id(f"{name}[{i},{j}]"):  f"{pol_str[pol]}{name}[{i},{j}]"
        for name in names_cl_ax  for i in range(s) for j in range(m)      for pol in range(pol_num)})
    vt.update({pol_int[pol] * vp.id(f"{name}[{i},{j}]"):  f"{pol_str[pol]}{name}[{i},{j}]"
        for name in names_cl_cl  for i in range(s) for j in range(i+1, s) for pol in range(pol_num)})
    vt.update({pol_int[pol] * vp.id(f"{name}[{i},{j},{v}]"):  f"{pol_str[pol]}{name}[{i},{j},{v}]"
        for name in names_cl_cl_var  for i in range(s) for j in range(i+1, s)
        for v in range(n) for pol in range(pol_num)})
    vt.update({pol_int[pol] * vp.id(f"{name}[{i},{j},{v}]"):  f"{pol_str[pol]}{name}[{i},{j},{v}]"
        for name in names_cl_cl_lit  for i in range(s) for j in range(i+1, s)
        for v in range(2*n) for pol in range(pol_num)})
    return vt

def reconstruct(model, n, m, s, vp):
    pos, neg, piv, ax, isax, arc = make_wrappers(vp)
    mset = set(model)
    for i in range(s):
        axioms = []
        parents = []
        clause = []
        for v in range(n):
            if pos(i, v) in mset:
                clause.append(v+1)
            if neg(i, v) in mset:
                clause.append(-v-1)
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


def get_query(F, n, m, s, is_mu=False):
    """
    This function takes a CNF formula F and an integer s,
    and returns clauses that encode the statement:

    Does F have a resolution refutation of length at most s?

    WARNING: for optimisation reasons, the clauses currently
    returned say "F has a resolution refutation of length exactly s"

    It also returns lists of variables that are useful in order
    to recover the found proof.
    """

    fset = [set(c) for c in F.clauses]

    # we define the set of original variables here
    # in fact, variables contains all original variables,
    # but may contain more if there are gaps.
    # It may be worth optimizing the size of variables later.
    variables = list(range(n))
    # variables are 0-indexed here, i.e. pos[i][0] means that
    # the variable 1 occurs in the clause i

    vp = IDPool()

    # clauses in the proof are indexed starting from 0

    # some helper notation
    axioms = range(m)
    proof_clauses = range(s)

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
        return vp.id(f"arc[{i},{j}]")

    # exarc[i,j] says that the arc from i to j is "extra", i.e. not the first outgoing arc from i
    def exarc(i, j):
        return vp.id(f"exarc[{i},{j}]")

    # {pos|neg}carry[i,j,v] says that the variable v occurs positively in i and
    # is carried over to j because of arc[i,j]
    def poscarry(i, j, v):
        return vp.id(f"poscarry[{i},{j},{v}]")
    def negcarry(i, j, v):
        return vp.id(f"negcarry[{i},{j},{v}]")

    # definition of being an axiom
    def_isax = [[-isax(i)] + [ax(i, j) for j in range(i, m)] for i in proof_clauses] +\
               [[-ax(i, j), isax(i)] for i in proof_clauses for j in range(i, m)]

    # definition of carries
    def_carries = [c for i in range(s-1) for j in range(i+1, s) for v in variables
                    for c in [
                        [-poscarry(i, j, v), pos(i, v)],
                        [-poscarry(i, j, v), arc(i, j)],
                        [poscarry(i, j, v), -pos(i, v), -arc(i, j)],
                        [-negcarry(i, j, v), neg(i, v)],
                        [-negcarry(i, j, v), arc(i, j)],
                        [negcarry(i, j, v), -neg(i, v), -arc(i, j)]
                    ]
                ]

    # set literals in axioms accordingly
    # this is optimized using the fact that axiom i appear no later
    # than as line i (if at all)
    set_axioms = []
    for j, c in enumerate(fset):
        for v in variables:
            w = v + 1
            if -w in c:
                set_axioms.extend([-ax(i, j), neg(i, v)] for i in range(j+1))
            elif w in c:
                set_axioms.extend([-ax(i, j), pos(i, v)] for i in range(j+1))
            else:
                set_axioms.extend([-ax(i, j), -neg(i, v)] for i in range(j+1))
                set_axioms.extend([-ax(i, j), -pos(i, v)] for i in range(j+1))

    # the first two clauses cannot possibly be resolvents
    proof_start_axioms = [[isax(0)], [isax(1)]]

    # axioms have no incoming arcs
    axioms_no_premises = [[-isax(j), -arc(i, j)] for j in range(1, min(s, m+1)) for i in range(j)]

    #######################################################################
    # here we define the resolution constraints via upos and uneg variables
    #######################################################################

    # defines which literals are in the union of the two premises of a resolvent
    def_uposneg = [c for j in range(2, s) for i in range(j) for v in variables
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
    def_pivot = [c for i in range(s) for v in variables
                    for c in [
                        [-piv(i, v), upos(i, v)],
                        [-piv(i, v), uneg(i, v)],
                        [-piv(i, v), -pos(i, v)],
                        [-piv(i, v), -neg(i, v)],
                        [-upos(i, v), -uneg(i, v), piv(i, v)]
                    ]
                ]

    # retention of non-pivot literals
    retention_non_piv = [c for i in range(2, s) for v in variables
                    for c in [
                        [piv(i, v), -upos(i, v), pos(i, v)],
                        [piv(i, v), -uneg(i, v), neg(i, v)]
                    ]
                ]
    
    # non-introduction
    non_introduction = [c for i in range(2, s) for v in variables
                    for c in [
                        [isax(i), -pos(i, v), upos(i, v)],
                        [isax(i), -neg(i, v), uneg(i, v)]
                    ]
                ]

    # resolvents have a pivot
    resolvents_have_pivot = None
    if is_mu:
        # we know exactly which lines are resolvents
        resolvents_have_pivot = [[piv(i, v) for v in variables] for i in range(m, s)]
    else:
        resolvents_have_pivot = [[isax(i)] + [piv(i, v) for v in variables] for i in range(2, s)]

    # at most one pivot
    # this cardinality constraint uses no auxiliary variables
    only_one_pivot = [c for i in proof_clauses
            for c in CardEnc.atmost([piv(i, v) for v in variables], encoding=0).clauses]

    # no variable occurs both positively and negatively in a clause
    no_tautology = [[-pos(i, v), -neg(i, v)] for i in range(s-1) for v in variables]

    # the last clause is empty
    empty_clause = [[-pos(s-1, v)] for v in variables] +\
                   [[-neg(s-1, v)] for v in variables]


    ############### SYMMETRY BREAKING ###############

    # axioms appear in original order, without duplicates
    # axiom j cannot possibly appear later than as clause j
    # all axioms are in the front
    # axioms have no pivot

    axiom_placement = []
    axioms_order = []
    axioms_in_front = []
    axioms_no_pivot = []
    axioms_no_uposneg = []
    if is_mu:
        axiom_placement += [[ax(i, i)] for i in axioms] + [[-isax(i)] for i in range(m, s)]
        axioms_no_pivot  = [[-piv(i, v)] for i in axioms for v in variables]
        axioms_no_uposneg = [[-upos(i, v)] for i in axioms for v in variables] +\
                            [[-uneg(i, v)] for i in axioms for v in variables]
    else:
        axioms_in_front  = [[-isax(i), isax(i-1)] for i in range(2, s)]
        axiom_placement += [[-ax(i, j)] for i in proof_clauses for j in range(min(i, m))]
        axioms_order = [[-ax(i, j), -ax(i+1, jj)]
                for i in range(s-1) for j in axioms for jj in range(j+1)]
        axioms_no_pivot = [[-isax(i), -piv(i, v)] for i in range(s-1) for v in variables]
        axioms_no_uposneg = [[-isax(i), -upos(i, v)] for i in axioms for v in variables] +\
                            [[-isax(i), -uneg(i, v)] for i in axioms for v in variables]

    # lexicographic ordering of consecutive clauses

    # eq[i,j,v] says that the clauses i and j are equal up to and including position v,
    # where the v ranges from 0 to 2variables - 1, and the clauses are represented as
    # vectors [pos[i][0], neg[i][0], pos[i][1], neg[i][1], pos[i][2], ...]
    def eq(i, j, v):
        return vp.id(f"eq[{i},{j},{v}]")

    # ϴ(s^2·n) clauses
    # ϴ(s^2·n) literals
    equality = [c for i in range(s-1) for j in range(i+1, s) for c in [
                [-eq(i, j, 0),  pos(i, 0), -pos(j, 0)],
                [-eq(i, j, 0), -pos(i, 0),  pos(j, 0)],
                [ eq(i, j, 0), -pos(i, 0), -pos(j, 0)],
                [ eq(i, j, 0),  pos(i, 0),  pos(j, 0)],
                [-eq(i, j, 1),   eq(i, j, 0)],
                [-eq(i, j, 1),  neg(i, 0), -neg(j, 0)],
                [-eq(i, j, 1), -neg(i, 0),  neg(j, 0)],
                [ eq(i, j, 1), - eq(i, j, 0), -neg(i, 0), -neg(j, 0)],
                [ eq(i, j, 1), - eq(i, j, 0),  neg(i, 0),  neg(j, 0)]
            ]
        ]
    for i in range(s-1):
        for j in range(i+1, s):
            for v in range(1, n):
                vpos = 2*v
                vneg = 2*v + 1
                equality.extend([
                    [-eq(i, j, vpos),   eq(i, j,  vpos-1)],
                    [-eq(i, j, vpos),  pos(i, v), -pos(j, v)],
                    [-eq(i, j, vpos), -pos(i, v),  pos(j, v)],
                    [ eq(i, j, vpos),  -eq(i, j,  vpos-1), -pos(i, v), -pos(j, v)],
                    [ eq(i, j, vpos),  -eq(i, j,  vpos-1),  pos(i, v),  pos(j, v)],
                    [-eq(i, j, vneg),   eq(i, j,  vneg-1)],
                    [-eq(i, j, vneg),  neg(i, v), -neg(j, v)],
                    [-eq(i, j, vneg), -neg(i, v),  neg(j, v)],
                    [ eq(i, j, vneg),  -eq(i, j,  vneg-1), -neg(i, v), -neg(j, v)],
                    [ eq(i, j, vneg),  -eq(i, j,  vneg-1),  neg(i, v),  neg(j, v)]
                ])

    # simultaneous source property
    # sim[i,j] says that the if the clauses are being removed in this order,
    # at the time of removal of i (when i is a source), j is also a source
    def sim(i, j):
        return vp.id(f"sim[{i},{j}]")

    simultaneous_sources = [[ sim(i, i+1),  arc(i, i+1)] for i in range(s-1)] +\
                           [[-sim(i, i+1), -arc(i, i+1)] for i in range(s-1)]

    # ϴ(s^2·n) clauses
    # ϴ(s^2·n) literals
    for i in range(s-2):
        for j in range(i+2, s):
            simultaneous_sources += [
                    [-sim(i, j),  sim(i+1, j)],
                    [-sim(i, j), -arc(i, j)],
                    [ sim(i, j), -sim(i+1, j), arc(i, j)]
                    ]

    # ϴ(s^2·n) clauses
    # ϴ(s^2·n) literals
    lex = []
    for i in range(s-1):
        for j in range(i+1, s):
            lex.append([-sim(i, j), isax(i), pos(i, 0), -pos(j, 0)])
            for v in variables:
                vpos = 2*v
                vneg = 2*v + 1
                lex.append([-sim(i, j), isax(i), -eq(i, j, vpos), neg(i, v), -neg(j, v)])
                if vneg < 2*n - 1:
                    lex.append([-sim(i, j), isax(i), -eq(i, j, vneg), pos(i, v+1), -pos(j, v+1)])
                else:
                    lex.append([-eq(i, j, vneg)])

    # only for variable-transitive formulas, such as PHP: last clause must always be unit, so
    # we fix the variable in that clause to be x_{n-1}, because those are the smallest clauses
    # in the lexicographic ordering

    #last_pigeon_standing = [[pos(s-2, n-1), neg(s-2, n-1)]] +\
            #[[-pos(s-2, v)] for v in range(n - 1)] +\
            #[[-neg(s-2, v)] for v in range(n - 1)]


    ############### REDUNDANCY ###############

    # when successively incrementing s, we know that every clause must be used
    every_clause_used = [[arc(i, j) for j in range(i+1, s)] for i in range(s-1)]

    all_clauses = def_isax + def_carries + def_pivot + def_uposneg + empty_clause + no_tautology +\
            retention_non_piv + non_introduction + resolvents_have_pivot + only_one_pivot +\
            set_axioms + axioms_no_premises + axioms_no_pivot + axioms_no_uposneg +\
            proof_start_axioms + axioms_in_front + axioms_order + axiom_placement + every_clause_used +\
            equality + lex + simultaneous_sources

    max_orig_var = maxvar(all_clauses)

    card_encoding = EncType.seqcounter

    extra_arcs = []
    if is_mu:
            # definition of an extra arc
            extra_arcs  = [[-arc(i, j), -arc(i, k), exarc(i, k)]
                    for i in range(s-2)
                        for j in range(i+1, s-1)
                            for k in range(j+1, s)]
            extra_arcs += [[-exarc(i, j), arc(i, j)]
                    for i in range(s-1)
                        for j in range(i+1, s)]
            extra_arcs += [[-exarc(i, k)] + [arc(i, j) for j in range(i+1, k)]
                        for i in range(s-1)
                            for k in range(i+2, s)]

            # limit the number of extra arcs to s - 2m + 1
            extra_arcs += CardEnc.atmost([exarc(i, j) for i in range(s-1) for j in range(i+1, s)],
                    bound=s-2*m+1,
                    encoding=card_encoding,
                    vpool=vp).clauses
    
    # resolvents have exactly two premises
    exactly_two_arcs = []
    if is_mu:
        exactly_two_arcs = [card_clause for j in range(m, s) for card_clause in
                CardEnc.equals([arc(i, j) for i in range(j)],
                    bound=2,
                    encoding=card_encoding,
                    vpool=vp).clauses]
    else:
        exactly_two_arcs = [[isax(j)] + card_clause for j in range(2, s) for card_clause in
                CardEnc.equals([arc(i, j) for i in range(j)],
                    bound=2,
                    encoding=card_encoding,
                    vpool=vp).clauses]

    all_clauses += exactly_two_arcs + extra_arcs

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

    n = maxvar(F.clauses)
    m = len(F.clauses)

    if options.verbosity >= 1:
        verb_query_begin(s)

    t_begin = clock()

    query_clauses, vp, max_orig_var = get_query(F, n, m, s, is_mu)

    t_end = clock()

    if options.verbosity >= 1:
        verb_query_end(maxvar(query_clauses), len(query_clauses), size(query_clauses), t_end-t_begin)
    
    solver = Solver(name=options.sat_solver, bootstrap_with=query_clauses)
    del query_clauses

    t_begin = clock()
    ans = solver.solve()
    t_end = clock()
    if options.verbosity >= 1:
        print(f"* Solved. ({t_end-t_begin:.5g} sec)")
        sys.stdout.flush()

    if ans:
        model = solver.get_model()
        if options.verbosity >= 1:
            print( "--------------------------------------")
            print(f"  Proof of length {s} found:")
            print()
            reconstruct(model, n, m, s, vp)
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

    n = maxvar(F.clauses)
    m = len(F.clauses)

    if options.verbosity >= 1:
        verb_query_begin(s)

    t_begin = clock()
    query_clauses, vp, max_orig_var = get_query(F, n, m, s, is_mu)
    t_end = clock()

    if options.verbosity >= 1:
        verb_query_end(maxvar(query_clauses), len(query_clauses), size(query_clauses), t_end-t_begin)

    solver = Solver(name=options.sat_solver, bootstrap_with=query_clauses)
    del query_clauses

    t = clock()
    proofs = 0
    last_model = None

    if options.verbosity >= 1:
        print(f"Max orig var: {max_orig_var}")
    vt = vartable(vp, n, m, s)
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
                reconstruct(model, n, m, s, vp)
        last_model = model

    return proofs


def find_shortest_proof(F, is_mu, options):
    """
    This function takes a CNF formula f and by asking queries
    to has_short_proof determines the shortest proof that f has.
    """

    t_begin = clock()

    print( "--------------------------------------")
    print( "* Finding shortest proof")
    print( "--------------------------------------")
    print(f"* SAT solver: {options.sat_solver:>16}")
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

    t_end = clock()
    print(f"* Time: {t_end - t_begin}")
    print(f"* Shortest proof found: {s}")
    return s


def main():
    if sys.version_info.major < 3 or sys.version_info.minor < 6:
        print("This script makes extensive use of f-strings"
                "[https://docs.python.org/3/tutorial/inputoutput.html#tut-f-strings],"
                "and as such requires Python version >= 3.6.")
        print("You appear to be running version %d.%d."
                % (sys.version_info.major, sys.version_info.major))
        sys.exit(36)

    parser = argparse.ArgumentParser()
    mu_group = parser.add_mutually_exclusive_group()
    parser.add_argument("cnf",
            help="filename of the formula whose shortest proof is to be determined")
    parser.add_argument("--sat-solver",
            help="specify which SAT solver to use", default="glucose", choices=[
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

    if options.sat_solver == "glucose":
        options.sat_solver = "glucose4"
    elif options.sat_solver == "minisat":
        options.sat_solver = "minisat22"

    F = CNF(from_file=options.cnf)
    if not is_unsat(F):
        print("ERROR: Input formula is satisfiable.", file=sys.stderr)

    is_mu = False
    if options.mu:
        is_mu = True
    elif not options.not_mu:
        is_mu = is_minimal(F)

    if options.query:
        print_formula(get_query(F, maxvar(F.clauses), len(F.clauses), options.query, is_mu)[0])
    elif options.count:
        print(count_short_proofs(F, options.count, is_mu, options))
    else:
        shortest = find_shortest_proof(F, is_mu, options)
        sys.exit(shortest)

if __name__ == "__main__":
    main()

