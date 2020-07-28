#!/usr/bin/env python3

import short as sh
from pysat.solvers import Lingeling
from pysat.card import EncType

def satisfies(tau, F, vt):
    unit_prop = set()
    remaining_clauses = set(range(len(F)))
    while True:
        to_remove = set()
        for cl_idx in remaining_clauses:
            unassigned = []
            sat = False
            for lit in F[cl_idx]:
                if lit in tau or lit in unit_prop:
                    sat = True
                    break
                if -lit not in tau and -lit not in unit_prop:
                    unassigned.append(lit)
            if sat:
                to_remove.add(cl_idx)
                continue
            if not unassigned:
                print("Falsified clause")
                #print(tau)
                #print(unit_prop)
                #print(F[cl_idx])
                #print(list(vt[lit] for lit in tau))
                #print()
                #print(list(vt[lit] for lit in unit_prop))
                #print()
                print(list(vt[lit] for lit in F[cl_idx]))
                return False
            if len(unassigned) == 1:
                unit_prop.add(unassigned[0])
                to_remove.add(cl_idx)
                #print(f"unit: {cl} ({unassigned[0]})")
        if to_remove:
            remaining_clauses -= to_remove
        else:
            break
    if remaining_clauses:
        print("Incomplete assignment")
        return False

    #solver = Lingeling(F)
    #return solver.solve()
    #return solver.solve(assumptions=list(tau))
    return True

def test_php_2_1_has_5():
    """
    Tests that the formula encoding the shortproof
    query for PHP(2, 1) with 5 clauses is
    satisfiable with a particular assignment.
    """
    php_2_1 = sh.Formula()
    php_2_1.add_clause([1])
    php_2_1.add_clause([2])
    php_2_1.add_clause([-1, -2])

    query, vp, _ = sh.get_query(php_2_1, 5, True, EncType.seqcounter, False)

    vt = sh.vartable(php_2_1, 5, vp)
    pos, neg, piv, ax, isax, arc, exarc, upos, uneg, poscarry, negcarry, posdrop, negdrop =\
            sh.make_predicates(vp)

    tau = { isax(0), isax(1), isax(2), -isax(3), -isax(4),
             ax(0, 0),   ax(1, 1),   ax(2, 2),
            pos(0, 1), -neg(0, 1), -pos(0, 2), -neg(0, 2),
           -pos(1, 1), -neg(1, 1),  pos(1, 2), -neg(1, 2),
           -pos(2, 1),  neg(2, 1), -pos(2, 2),  neg(2, 2),
           -pos(3, 1),  neg(3, 1), -pos(3, 2), -neg(3, 2),
           -pos(4, 1), -neg(4, 1), -pos(4, 2), -neg(4, 2),
           -arc(0, 1),
           -arc(0, 2), -arc(1, 2),
           -arc(0, 3),  arc(1, 3),  arc(2, 3),
            arc(0, 4), -arc(1, 4), -arc(2, 4), arc(3, 4),
           -piv(0, 1), -piv(0, 2),
           -piv(1, 1), -piv(1, 2),
           -piv(2, 1), -piv(2, 2),
           -piv(3, 1),  piv(3, 2),
            piv(4, 1), -piv(4, 2) }

    assert(satisfies(tau, query, vt))
    print("PHP(2,1): OK")

def test_smallest_has_3():
    """
    Tests that the formula encoding the shortproof
    query for "x and not x" with 3 clauses is
    satisfiable with a particular assignment.
    """
    small = sh.Formula()
    small.add_clause([1])
    small.add_clause([-1])

    query, vp, _ = sh.get_query(small, 3, True, EncType.seqcounter, False)

    vt = sh.vartable(small, 3, vp)
    pos, neg, piv, ax, isax, arc, exarc, upos, uneg, poscarry, negcarry, posdrop, negdrop =\
            sh.make_predicates(vp)

    tau = { isax(0), isax(1), -isax(2),
             ax(0, 0),   ax(1, 1),
            pos(0, 1), -neg(0, 1),
           -pos(1, 1),  neg(1, 1), 
           -pos(2, 1), -neg(2, 1), 
           -arc(0, 1),
            arc(0, 2),  arc(1, 2),
           -piv(0, 1),
           -piv(1, 1),
            piv(2, 1) }

    assert(satisfies(tau, query, vt))
    print("SMALLEST: OK")

def test_eq_1_has_ldq_5():
    """
    Tests that the formula encoding the shortproof
    query for "x and not x" with 3 clauses is
    satisfiable with a particular assignment.
    """
    eq1 = sh.Formula()
    eq1.add_vars([1], "e")
    eq1.add_vars([2], "a")
    eq1.add_vars([3], "e")
    eq1.add_clause([1, 2, 3])
    eq1.add_clause([-1, -2, 3])
    eq1.add_clause([-3])

    query, vp, _ = sh.get_query(eq1, 5, True, EncType.seqcounter, True)

    vt = sh.vartable(eq1, 5, vp)
    pos, neg, piv, ax, isax, arc, exarc, upos, uneg, poscarry, negcarry, posdrop, negdrop =\
            sh.make_predicates(vp)

    tau = { isax(0), isax(1), isax(2), -isax(3), -isax(4),
             ax(0, 0),   ax(1, 1),   ax(2, 2),
            pos(0, 1), -neg(0, 1),  pos(0, 2), -neg(0, 2),  pos(0, 3), -neg(0, 3),
           -pos(1, 1),  neg(1, 1), -pos(1, 2),  neg(1, 2),  pos(1, 3), -neg(1, 3),
           -pos(2, 1), -neg(2, 1), -pos(2, 2), -neg(2, 2), -pos(2, 3),  neg(2, 3),
           -pos(3, 1), -neg(3, 1),  pos(3, 2),  neg(3, 2),  pos(3, 3), -neg(3, 3),
           -pos(4, 1), -neg(4, 1), -pos(4, 2), -neg(4, 2), -pos(4, 3), -neg(4, 3),
           -arc(0, 1),
           -arc(0, 2), -arc(1, 2),
            arc(0, 3),  arc(1, 3), -arc(2, 3),
           -arc(0, 4), -arc(1, 4),  arc(2, 4), arc(3, 4),
           -piv(0, 1), -piv(0, 3),
           -piv(1, 1), -piv(1, 3),
           -piv(2, 1), -piv(2, 3),
            piv(3, 1), -piv(3, 3),
           -piv(4, 1),  piv(4, 3) }

    assert(satisfies(tau, query, vt))
    print("EQ(1):    OK")

if __name__ == "__main__":
    test_smallest_has_3()
    test_php_2_1_has_5()
    test_eq_1_has_ldq_5()

