#!/usr/bin/env python3
"""Unit test suite for zfc Coq formalization and set-theoretic verification."""

import itertools
import os
import shutil
import subprocess
import unittest

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


# Python reference model for hereditarily finite sets
def vide():
    return frozenset()


def sing(x):
    return frozenset({x})


def paire(x, y):
    return frozenset({x, y})


def union(s):
    return frozenset(elem for subset in s for elem in subset)


def power(s):
    elements = list(s)
    result = set()
    for r in range(len(elements) + 1):
        for combo in itertools.combinations(elements, r):
            result.add(frozenset(combo))
    return frozenset(result)


def comp(s, predicate):
    return frozenset(x for x in s if predicate(x))


def succ(s):
    return s | frozenset({s})


def von_neumann_ord(n):
    res = vide()
    for _ in range(n):
        res = succ(res)
    return res


def rank(s):
    if not s:
        return 0
    return 1 + max(rank(x) for x in s)


def is_transitive(s):
    for x in s:
        if not x.issubset(s):
            return False
    return True


def kuratowski_pair(a, b):
    return frozenset({frozenset({a}), frozenset({a, b})})


def dunaev_pair(a, b):
    # Tagged ordered pair: { {0, a}, {1, b} }
    zero = von_neumann_ord(0)
    one = von_neumann_ord(1)
    return frozenset({frozenset({zero, a}), frozenset({one, b})})


class TestZFC(unittest.TestCase):
    def test_core_coq_modules_exist(self):
        core = [
            "Axioms.v",
            "Sets.v",
            "Cartesian.v",
            "Constructive.v",
            "Hierarchy.v",
            "Omega.v",
            "Ordinal_succession.v",
            "Ordinal_theory.v",
            "Plump.v",
            "Replacement.v",
            "Russell.v",
            "Regularity.v",
            "Limit_ordinals.v",
            "Transfinite_recursion.v",
            "Choice.v",
            "3_Regularity.v",
            "zfc.v",
        ]
        for fname in core:
            fpath = os.path.join(ROOT, fname)
            self.assertTrue(os.path.isfile(fpath), f"Missing {fpath}")
            self.assertGreater(os.path.getsize(fpath), 100)

    def test_coq_compilation_all_modules(self):
        coqc = shutil.which("coqc")
        if not coqc:
            self.skipTest("coqc not available in environment")

        ordered_modules = [
            "Sets.v",
            "Axioms.v",
            "Cartesian.v",
            "Constructive.v",
            "Hierarchy.v",
            "Omega.v",
            "Ordinal_succession.v",
            "Plump.v",
            "Replacement.v",
            "Russell.v",
            "Regularity.v",
            "Ordinal_theory.v",
            "Limit_ordinals.v",
            "Transfinite_recursion.v",
            "Choice.v",
            "zfc.v",
        ]

        for mod in ordered_modules:
            cmd = [coqc, "-q", mod]
            res = subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True)
            self.assertEqual(
                res.returncode,
                0,
                f"Compilation failed for {mod}:\nSTDOUT: {res.stdout}\nSTDERR: {res.stderr}",
            )

    def test_set_constructors_and_axioms(self):
        # Axiom of Empty Set
        empty = vide()
        self.assertEqual(len(empty), 0)

        # Axiom of Pairing
        a = sing(empty)
        p = paire(empty, a)
        self.assertEqual(len(p), 2)
        self.assertIn(empty, p)
        self.assertIn(a, p)

        # Axiom of Union
        u = union(p)
        self.assertEqual(u, empty | a)

        # Axiom of Powerset
        pow_p = power(p)
        self.assertEqual(len(pow_p), 2 ** len(p))
        self.assertIn(vide(), pow_p)
        self.assertIn(p, pow_p)

        # Axiom of Separation (Comprehension)
        separated = comp(p, lambda x: x == empty)
        self.assertEqual(separated, frozenset({empty}))

    def test_ordinal_constructors_and_ranks(self):
        # von Neumann ordinals: 0 = {}, 1 = {0}, 2 = {0, 1}, 3 = {0, 1, 2}
        ord0 = von_neumann_ord(0)
        ord1 = von_neumann_ord(1)
        ord2 = von_neumann_ord(2)
        ord3 = von_neumann_ord(3)
        ord4 = von_neumann_ord(4)

        self.assertEqual(len(ord0), 0)
        self.assertEqual(len(ord1), 1)
        self.assertEqual(len(ord2), 2)
        self.assertEqual(len(ord3), 3)
        self.assertEqual(len(ord4), 4)

        # Transitivity of ordinals
        self.assertTrue(is_transitive(ord0))
        self.assertTrue(is_transitive(ord1))
        self.assertTrue(is_transitive(ord2))
        self.assertTrue(is_transitive(ord3))
        self.assertTrue(is_transitive(ord4))

        # Strict containment (membership)
        self.assertIn(ord0, ord1)
        self.assertIn(ord1, ord2)
        self.assertIn(ord2, ord3)
        self.assertIn(ord3, ord4)

        # Rank verification
        self.assertEqual(rank(ord0), 0)
        self.assertEqual(rank(ord1), 1)
        self.assertEqual(rank(ord2), 2)
        self.assertEqual(rank(ord3), 3)
        self.assertEqual(rank(ord4), 4)

    def test_cumulative_hierarchy_v_ranks(self):
        # V_0 = {}
        # V_{n+1} = P(V_n)
        v0 = vide()
        v1 = power(v0)
        v2 = power(v1)
        v3 = power(v2)

        self.assertEqual(rank(v0), 0)
        self.assertEqual(rank(v1), 1)
        self.assertEqual(rank(v2), 2)
        self.assertEqual(rank(v3), 3)

        self.assertEqual(len(v0), 0)
        self.assertEqual(len(v1), 1)
        self.assertEqual(len(v2), 2)
        self.assertEqual(len(v3), 4)

    def test_epsilon_foundation_and_regularity(self):
        # Axiom of Regularity / Foundation: every non-empty set has an epsilon-minimal element
        sets_to_test = [
            paire(vide(), sing(vide())),
            von_neumann_ord(4),
            power(paire(vide(), sing(vide()))),
        ]
        for s in sets_to_test:
            if s:
                # Find minimal element y in s such that y intersect s == empty
                minimal_elements = [y for y in s if (y & s) == vide()]
                self.assertGreater(
                    len(minimal_elements),
                    0,
                    f"Set {s} violates regularity: no epsilon-minimal element found",
                )

    def test_pairing_and_choice_functions(self):
        # Kuratowski pairing injectivity
        p1 = kuratowski_pair(von_neumann_ord(1), von_neumann_ord(2))
        p2 = kuratowski_pair(von_neumann_ord(1), von_neumann_ord(2))
        p3 = kuratowski_pair(von_neumann_ord(2), von_neumann_ord(1))
        self.assertEqual(p1, p2)
        self.assertNotEqual(p1, p3)

        # Dunaev tagged ordered pairing injectivity
        dp1 = dunaev_pair(von_neumann_ord(1), von_neumann_ord(2))
        dp2 = dunaev_pair(von_neumann_ord(1), von_neumann_ord(2))
        dp3 = dunaev_pair(von_neumann_ord(2), von_neumann_ord(1))
        self.assertEqual(dp1, dp2)
        self.assertNotEqual(dp1, dp3)

        # Choice function on family of non-empty sets
        family = frozenset({
            von_neumann_ord(1),  # {0}
            von_neumann_ord(2),  # {0, 1}
            von_neumann_ord(3),  # {0, 1, 2}
        })
        # A valid choice function selects an element from each set
        choice_graph = frozenset(
            (s, next(iter(s))) for s in family
        )
        self.assertEqual(len(choice_graph), len(family))
        for s, chosen in choice_graph:
            self.assertIn(chosen, s)


if __name__ == "__main__":
    unittest.main()
