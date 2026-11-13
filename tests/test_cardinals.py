#!/usr/bin/env python3
"""Unit test suite for ZFC Cardinals, Hartogs' Theorem, and Initial Ordinals."""

import glob
import os
import re
import shutil
import subprocess
import unittest

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


# Python reference model functions for cardinal verification
def vide():
    return frozenset()


def sing(x):
    return frozenset({x})


def paire(x, y):
    return frozenset({x, y})


def power(s):
    elements = list(s)
    result = set()
    import itertools
    for r in range(len(elements) + 1):
        for combo in itertools.combinations(elements, r):
            result.add(frozenset(combo))
    return frozenset(result)


def von_neumann_ord(n):
    res = vide()
    for _ in range(n):
        res = res | frozenset({res})
    return res


def can_inject(s1, s2):
    # Finite sets can inject iff |s1| <= |s2|
    return len(s1) <= len(s2)


def are_equipotent(s1, s2):
    # Finite sets are equipotent iff |s1| == |s2|
    return len(s1) == len(s2)


def is_initial_ordinal(n):
    # An ordinal n is initial if for all m < n, not (n ~ m)
    ord_n = von_neumann_ord(n)
    for m in range(n):
        ord_m = von_neumann_ord(m)
        if are_equipotent(ord_n, ord_m):
            return False
    return True


def hartogs_finite(s):
    # Hartogs number for a finite set of size n is n + 1
    return len(s) + 1


class TestCardinals(unittest.TestCase):
    def test_cardinal_module_exists(self):
        fpath = os.path.join(ROOT, "Cardinal.v")
        self.assertTrue(os.path.isfile(fpath), f"Missing {fpath}")
        self.assertGreater(os.path.getsize(fpath), 500)

    def test_cardinal_coq_compilation(self):
        coqc = shutil.which("coqc")
        if not coqc:
            self.skipTest("coqc not available in environment")

        cmd = [coqc, "-q", "Cardinal.v"]
        res = subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True)
        self.assertEqual(
            res.returncode,
            0,
            f"Compilation failed for Cardinal.v:\nSTDOUT: {res.stdout}\nSTDERR: {res.stderr}",
        )

    def test_zero_admitted_in_all_coq_theories(self):
        v_files = glob.glob(os.path.join(ROOT, "*.v"))
        self.assertGreater(len(v_files), 10, "Expected at least 10 Coq theory files")

        admitted_pattern = re.compile(r"\b(Admitted|admit)\b", re.IGNORECASE)

        for vf in v_files:
            bname = os.path.basename(vf)
            with open(vf, "r", encoding="utf-8") as f:
                content = f.read()

            # Strip comments (* ... *) before searching for admitted
            cleaned = re.sub(r"\(\*.*?\*\)", "", content, flags=re.DOTALL)
            matches = admitted_pattern.findall(cleaned)
            self.assertEqual(
                len(matches),
                0,
                f"Found unclosed proofs (Admitted/admit) in {bname}: {matches}",
            )

    def test_cantor_theorem_properties(self):
        # Cantor's Theorem: for any set x, |x| < |P(x)| and not (P(x) <= x)
        for n in range(5):
            x = von_neumann_ord(n)
            px = power(x)
            self.assertTrue(can_inject(x, px), f"x should inject into P(x) for n={n}")
            self.assertFalse(can_inject(px, x), f"P(x) should not inject into x for n={n}")
            self.assertFalse(are_equipotent(x, px), f"x should not be equipotent to P(x) for n={n}")
            self.assertEqual(len(px), 2 ** len(x))

    def test_initial_ordinals_and_cardinals(self):
        # 0, 1, 2, 3, 4 are all initial ordinals (finite cardinals)
        for n in range(6):
            self.assertTrue(is_initial_ordinal(n), f"von Neumann ordinal {n} should be initial")

    def test_hartogs_theorem_finite_model(self):
        # For any finite set s, hartogs(s) = |s| + 1 cannot inject into s
        for n in range(5):
            s = von_neumann_ord(n)
            h = hartogs_finite(s)
            self.assertFalse(
                can_inject(von_neumann_ord(h), s),
                f"Hartogs ordinal {h} should not inject into set of size {n}",
            )
            # But every strictly smaller ordinal CAN inject into s
            for m in range(h):
                self.assertTrue(
                    can_inject(von_neumann_ord(m), s),
                    f"Ordinal {m} < {h} should inject into set of size {n}",
                )

    def test_equipotence_equivalence_relation(self):
        # Reflexive, symmetric, transitive
        s1 = von_neumann_ord(3)
        s2 = power(paire(vide(), sing(vide())))  # size 2^2 = 4
        s3 = von_neumann_ord(4)

        # Reflexive
        self.assertTrue(are_equipotent(s1, s1))
        self.assertTrue(are_equipotent(s2, s2))

        # Equipotent between s2 and s3 (both size 4)
        self.assertTrue(are_equipotent(s2, s3))
        self.assertTrue(are_equipotent(s3, s2))

        # Non-equipotent between s1 (size 3) and s2 (size 4)
        self.assertFalse(are_equipotent(s1, s2))


if __name__ == "__main__":
    unittest.main()
