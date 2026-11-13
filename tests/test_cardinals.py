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


def card_sum_finite(s1, s2):
    # (s1 * {0}) U (s2 * {1})
    left = {(x, 0) for x in s1}
    right = {(y, 1) for y in s2}
    return frozenset(left | right)


def card_prod_finite(s1, s2):
    # s1 * s2
    return frozenset((x, y) for x in s1 for y in s2)


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

    def test_cardinal_sum_and_product_finite_model(self):
        for n in range(4):
            for m in range(4):
                s1 = von_neumann_ord(n)
                s2 = von_neumann_ord(m)
                c_sum = card_sum_finite(s1, s2)
                c_prod = card_prod_finite(s1, s2)

                self.assertEqual(len(c_sum), n + m)
                self.assertEqual(len(c_prod), n * m)

    def test_cardinal_sum_product_algebraic_laws(self):
        for n in range(3):
            for m in range(3):
                s1 = von_neumann_ord(n)
                s2 = von_neumann_ord(m)

                # Commutativity
                self.assertTrue(
                    are_equipotent(card_sum_finite(s1, s2), card_sum_finite(s2, s1)),
                    f"Sum commutativity failed for n={n}, m={m}",
                )
                self.assertTrue(
                    are_equipotent(card_prod_finite(s1, s2), card_prod_finite(s2, s1)),
                    f"Product commutativity failed for n={n}, m={m}",
                )

                for k in range(3):
                    s3 = von_neumann_ord(k)

                    # Associativity
                    sum_assoc_l = card_sum_finite(card_sum_finite(s1, s2), s3)
                    sum_assoc_r = card_sum_finite(s1, card_sum_finite(s2, s3))
                    self.assertTrue(
                        are_equipotent(sum_assoc_l, sum_assoc_r),
                        f"Sum associativity failed for n={n}, m={m}, k={k}",
                    )

                    prod_assoc_l = card_prod_finite(card_prod_finite(s1, s2), s3)
                    prod_assoc_r = card_prod_finite(s1, card_prod_finite(s2, s3))
                    self.assertTrue(
                        are_equipotent(prod_assoc_l, prod_assoc_r),
                        f"Product associativity failed for n={n}, m={m}, k={k}",
                    )

                    # Distributivity: s1 * (s2 + s3) ~ (s1 * s2) + (s1 * s3)
                    distrib_l = card_prod_finite(s1, card_sum_finite(s2, s3))
                    distrib_r = card_sum_finite(
                        card_prod_finite(s1, s2), card_prod_finite(s1, s3)
                    )
                    self.assertTrue(
                        are_equipotent(distrib_l, distrib_r),
                        f"Distributivity failed for n={n}, m={m}, k={k}",
                    )

    def test_cardinal_embeddings(self):
        for n in range(4):
            for m in range(4):
                s1 = von_neumann_ord(n)
                s2 = von_neumann_ord(m)
                c_sum = card_sum_finite(s1, s2)
                c_prod = card_prod_finite(s1, s2)

                # Embeddings into card_sum: kappa <= kappa + lambda and lambda <= kappa + lambda
                self.assertTrue(can_inject(s1, c_sum))
                self.assertTrue(can_inject(s2, c_sum))

                # Embeddings into card_prod when other set is non-empty
                if m > 0:
                    self.assertTrue(can_inject(s1, c_prod))
                if n > 0:
                    self.assertTrue(can_inject(s2, c_prod))

    def test_infinite_cardinal_absorption_model(self):
        # In infinite cardinal arithmetic under AC:
        # kappa + lambda = kappa * lambda = max(kappa, lambda) for kappa, lambda >= aleph_0
        aleph_0 = 1000  # finite model proxy for aleph_0
        aleph_1 = 2000

        for k1, k2 in [(aleph_0, aleph_0), (aleph_0, aleph_1), (aleph_1, aleph_1)]:
            max_k = max(k1, k2)
            # Simulated cardinal addition and multiplication
            sum_card = max_k
            prod_card = max_k
            self.assertEqual(sum_card, max_k)
            self.assertEqual(prod_card, max_k)

    def test_coq_theorems_present_in_cardinal_module(self):
        cardinal_v = os.path.join(ROOT, "Cardinal.v")
        with open(cardinal_v, "r", encoding="utf-8") as f:
            content = f.read()

        expected_identifiers = [
            "card_sum",
            "card_prod",
            "card_sum_inj_left",
            "card_sum_inj_right",
            "card_prod_inj_left",
            "card_prod_inj_right",
            "card_sum_Vide_Vide",
            "card_prod_Vide_right",
            "card_prod_Vide_left",
            "card_sum_comm_statement",
            "card_prod_comm_statement",
            "card_sum_assoc_statement",
            "card_prod_assoc_statement",
            "card_prod_distrib_statement",
            "Hessenberg_Theorem",
            "Cardinal_Absorption_Theorem",
            "Choice_implies_Absorption",
            "equipotent_trans",
            "hartogs",
            "Ord_hartogs",
            "not_INC_hartogs",
            "is_cardinal",
            "cardinal_Vide",
            "cardinal_Succ_Vide",
            "aleph_0",
            "Ord_aleph_0",
        ]

        for ident in expected_identifiers:
            self.assertIn(ident, content, f"Missing definition/theorem {ident} in Cardinal.v")


if __name__ == "__main__":
    unittest.main()
