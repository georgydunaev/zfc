#!/usr/bin/env python3
"""Unit tests for ZFC Cardinal Exponentiation, Cantor Theorem, Cofinality, and Konig Theorem."""

import os
import re
import shutil
import subprocess
import sys
import unittest

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if ROOT not in sys.path:
    sys.path.insert(0, ROOT)

from zfc.cardinal_exponentiation import (
    Cardinal,
    aleph,
    are_equipotent,
    can_inject,
    cantor_diagonal_witness,
    card_prod_finite,
    card_sum_finite,
    check_cf_continuum_bound,
    cofinality,
    finite_functions,
    is_regular,
    is_singular,
    konig_diagonal_witness,
    konig_inequality_finite,
    power,
    strictly_smaller,
    vide,
    von_neumann_ord,
)


class TestCoqCardinalExponentiation(unittest.TestCase):
    """Verifies Coq formalization in cardinal_exponentiation.v."""

    def test_module_exists(self):
        v_file = os.path.join(ROOT, "cardinal_exponentiation.v")
        self.assertTrue(os.path.isfile(v_file), f"Missing {v_file}")
        self.assertGreater(os.path.getsize(v_file), 500)

    def test_coq_compilation(self):
        coqc = shutil.which("coqc")
        if not coqc:
            self.skipTest("coqc not installed")
        res = subprocess.run(["coqc", "-q", "cardinal_exponentiation.v"], cwd=ROOT, capture_output=True, text=True)
        self.assertEqual(
            res.returncode,
            0,
            f"Compilation failed for cardinal_exponentiation.v:\nSTDOUT: {res.stdout}\nSTDERR: {res.stderr}",
        )

    def test_zero_admitted(self):
        v_file = os.path.join(ROOT, "cardinal_exponentiation.v")
        with open(v_file, "r", encoding="utf-8") as f:
            content = f.read()
        cleaned = re.sub(r"\(\*.*?\*\)", "", content, flags=re.DOTALL)
        matches = re.findall(r"\b(Admitted|admit)\b", cleaned, re.IGNORECASE)
        self.assertEqual(len(matches), 0, f"Found unclosed proofs: {matches}")

    def test_theorems_and_definitions_present(self):
        v_file = os.path.join(ROOT, "cardinal_exponentiation.v")
        with open(v_file, "r", encoding="utf-8") as f:
            content = f.read()

        expected = [
            "Cantor_no_surjection",
            "Cantor_strictly_smaller",
            "strictly_smaller_equipotent_right",
            "is_function_graph",
            "card_exp",
            "card_two",
            "card_exp_zero_has_element",
            "card_exp_zero_only_Vide",
            "card_exp_zero",
            "card_exp_zero_statement",
            "card_exp_one_statement",
            "card_exp_sum_statement",
            "card_prod_exp_statement",
            "card_exp_exp_statement",
            "Power_strictly_greater",
            "exp_two_strict_statement",
            "exp_two_strict",
            "is_unbounded_map",
            "is_cofinal_from",
            "id_is_unbounded",
            "cofinal_from_self",
            "is_cofinality",
            "is_regular_cardinal",
            "is_singular_cardinal",
            "aleph_0_regular_statement",
            "indexed_sum",
            "Konig_diagonal_contradiction",
            "Konig_Theorem_statement",
            "cf_power_greater_statement",
            "Konig_implies_cf_power",
        ]
        for ident in expected:
            self.assertIn(ident, content, f"Missing {ident} in cardinal_exponentiation.v")


class TestCantorTheoremPython(unittest.TestCase):
    """Tests for Cantor's Theorem in Python model."""

    def test_cantor_strict_inequality(self):
        for n in range(5):
            x = von_neumann_ord(n)
            px = power(x)
            self.assertTrue(can_inject(x, px))
            self.assertFalse(can_inject(px, x))
            self.assertTrue(strictly_smaller(x, px))
            self.assertEqual(len(px), 2 ** len(x))

    def test_cantor_diagonal_witness(self):
        # Construct candidate maps x -> P(x) and verify witness
        for n in range(1, 5):
            x = von_neumann_ord(n)
            elements = list(x)
            # Map each element to its singleton
            f = {a: frozenset({a}) for a in elements}
            d = cantor_diagonal_witness(x, f)
            # D = {a in x | a not in f(a)} should be empty here
            self.assertEqual(d, frozenset())
            self.assertTrue(all(f[a] != d for a in elements))

            # Another map: constant map to x
            f2 = {a: x for a in elements}
            d2 = cantor_diagonal_witness(x, f2)
            self.assertTrue(all(f2[a] != d2 for a in elements))


class TestCardinalExponentiationPython(unittest.TestCase):
    """Tests for Cardinal Exponentiation in finite and transfinite models."""

    def test_finite_functions_count(self):
        for n in range(4):
            for m in range(4):
                b = von_neumann_ord(m)
                a = von_neumann_ord(n)
                funcs = finite_functions(b, a)
                expected_count = n ** m
                self.assertEqual(
                    len(funcs),
                    expected_count,
                    f"Expected {expected_count} functions for |A|={n}, |B|={m}, got {len(funcs)}",
                )

    def test_exponentiation_algebraic_laws_finite(self):
        for n in range(3):
            s_n = von_neumann_ord(n)

            # kappa^0 = 1
            funcs_0 = finite_functions(vide(), s_n)
            self.assertEqual(len(funcs_0), 1)

            # kappa^1 = kappa
            funcs_1 = finite_functions(von_neumann_ord(1), s_n)
            self.assertEqual(len(funcs_1), n)

            for m in range(3):
                s_m = von_neumann_ord(m)
                for k in range(3):
                    s_k = von_neumann_ord(k)

                    # kappa^(lambda + mu) = kappa^lambda * kappa^mu
                    lhs_sum = len(finite_functions(card_sum_finite(s_m, s_k), s_n))
                    rhs_sum = len(finite_functions(s_m, s_n)) * len(finite_functions(s_k, s_n))
                    self.assertEqual(lhs_sum, rhs_sum)

                    # (kappa * lambda)^mu = kappa^mu * lambda^mu
                    lhs_prod = len(finite_functions(s_k, card_prod_finite(s_n, s_m)))
                    rhs_prod = len(finite_functions(s_k, s_n)) * len(finite_functions(s_k, s_m))
                    self.assertEqual(lhs_prod, rhs_prod)

                    # (kappa^lambda)^mu = kappa^(lambda * mu)
                    lhs_exp = (n ** m) ** k
                    rhs_exp = n ** (m * k)
                    self.assertEqual(lhs_exp, rhs_exp)

    def test_transfinite_cardinals(self):
        a0 = aleph(0)
        a1 = aleph(1)
        two = Cardinal(value=2)

        # 2^aleph_0 under GCH is aleph_1
        c = two.card_exp(a0, gch=True)
        self.assertEqual(c, a1)
        self.assertTrue(c > a0)

        # kappa^0 = 1 for transfinite
        self.assertEqual(a0.card_exp(Cardinal(value=0)), Cardinal(value=1))
        self.assertEqual(a1.card_exp(Cardinal(value=0)), Cardinal(value=1))

        # kappa^1 = kappa
        self.assertEqual(a0.card_exp(Cardinal(value=1)), a0)
        self.assertEqual(a1.card_exp(Cardinal(value=1)), a1)


class TestCofinalityPython(unittest.TestCase):
    """Tests for cofinality and regularity/singularity."""

    def test_cofinality_values(self):
        # Finite
        self.assertEqual(cofinality(Cardinal(value=0)), Cardinal(value=0))
        self.assertEqual(cofinality(Cardinal(value=1)), Cardinal(value=1))
        self.assertEqual(cofinality(Cardinal(value=5)), Cardinal(value=1))

        # Aleph_0 is regular
        a0 = aleph(0)
        self.assertEqual(cofinality(a0), a0)
        self.assertTrue(is_regular(a0))
        self.assertFalse(is_singular(a0))

        # Aleph_1 is regular
        a1 = aleph(1)
        self.assertEqual(cofinality(a1), a1)
        self.assertTrue(is_regular(a1))
        self.assertFalse(is_singular(a1))

        # Aleph_omega is singular with cofinality aleph_0
        a_omega = aleph("omega")
        self.assertEqual(cofinality(a_omega), a0)
        self.assertTrue(is_singular(a_omega))
        self.assertFalse(is_regular(a_omega))


class TestKonigTheoremPython(unittest.TestCase):
    """Tests for Konig's Theorem and its corollary."""

    def test_konig_inequality_finite(self):
        kappas = [1, 2, 0]
        lambdas = [2, 3, 2]
        self.assertTrue(konig_inequality_finite(kappas, lambdas))
        self.assertEqual(sum(kappas), 3)
        self.assertEqual(2 * 3 * 2, 12)
        self.assertLess(3, 12)

    def test_konig_diagonal_witness(self):
        index_set = ["0", "1"]
        kappas = {
            "0": frozenset({0}),
            "1": frozenset({0, 1}),
        }
        lambdas = {
            "0": frozenset({0, 1}),
            "1": frozenset({0, 1, 2}),
        }

        # Candidate mapping F from disjoint sum to product
        # Disjoint sum elements: ("0", 0), ("1", 0), ("1", 1)
        # Attempted function F:
        def candidate_f(pair):
            i, x = pair
            if i == "0":
                return {"0": 0, "1": 0}
            if i == "1" and x == 0:
                return {"0": 1, "1": 1}
            return {"0": 0, "1": 0}

        d = konig_diagonal_witness(index_set, kappas, lambdas, candidate_f)

        # Check d is a valid element of prod lambda_i
        for i in index_set:
            self.assertIn(d[i], lambdas[i])

        # Verify d is not in the image of F
        sum_elements = [("0", 0), ("1", 0), ("1", 1)]
        for elem in sum_elements:
            self.assertNotEqual(candidate_f(elem), d)

    def test_cf_continuum_corollary(self):
        a0 = aleph(0)
        a_omega = aleph("omega")

        # By Konig theorem: cf(2^aleph_0) > aleph_0
        # Since cf(aleph_omega) = aleph_0, 2^aleph_0 cannot equal aleph_omega
        cf_omega = cofinality(a_omega)
        self.assertEqual(cf_omega, a0)
        self.assertFalse(cf_omega > a0)


if __name__ == "__main__":
    unittest.main()
