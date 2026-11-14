"""Unit tests for GCH, Hausdorff formula, Bernstein formula, Silver's theorem,

and Easton's theorem algorithms.
"""

import unittest

from zfc.cardinal_exponentiation import Cardinal, aleph, cofinality, is_regular, is_singular
from zfc.gch_singular import (
    EastonModel,
    bernstein_formula_evaluate,
    card_succ,
    check_silver_condition,
    gch_card_exp,
    gch_power,
    hausdorff_formula_evaluate,
    is_valid_easton_function,
    validate_cardinal_power_assignment,
)


class TestGCHExponentiation(unittest.TestCase):
    """Test suite for GCH exponentiation rules and algebraic base cases."""

    def test_base_cases(self):
        # 0^0 = 1, kappa^0 = 1
        self.assertEqual(gch_card_exp(Cardinal(0), Cardinal(0)), Cardinal(1))
        self.assertEqual(gch_card_exp(aleph(0), Cardinal(0)), Cardinal(1))
        self.assertEqual(gch_card_exp(aleph(1), Cardinal(0)), Cardinal(1))

        # 0^lambda = 0 for lambda > 0
        self.assertEqual(gch_card_exp(Cardinal(0), Cardinal(5)), Cardinal(0))
        self.assertEqual(gch_card_exp(Cardinal(0), aleph(0)), Cardinal(0))

        # 1^lambda = 1
        self.assertEqual(gch_card_exp(Cardinal(1), aleph(2)), Cardinal(1))

        # Finite exponentiation
        self.assertEqual(gch_card_exp(Cardinal(2), Cardinal(3)), Cardinal(8))
        self.assertEqual(gch_card_exp(Cardinal(3), Cardinal(4)), Cardinal(81))

        # Infinite base, finite exponent
        self.assertEqual(gch_card_exp(aleph(0), Cardinal(5)), aleph(0))
        self.assertEqual(gch_card_exp(aleph(1), Cardinal(10)), aleph(1))

    def test_regular_cardinals_le(self):
        # Under GCH, if kappa <= lambda: kappa^lambda = 2^lambda = lambda^+
        self.assertEqual(gch_card_exp(aleph(0), aleph(0)), aleph(1))
        self.assertEqual(gch_card_exp(aleph(0), aleph(1)), aleph(2))
        self.assertEqual(gch_card_exp(aleph(1), aleph(1)), aleph(2))
        self.assertEqual(gch_card_exp(aleph(1), aleph(2)), aleph(3))
        self.assertEqual(gch_card_exp(aleph(2), aleph(2)), aleph(3))

    def test_regular_cardinals_greater(self):
        # Under GCH, if lambda < kappa with kappa regular: kappa^lambda = kappa = max(kappa, lambda)
        self.assertEqual(gch_card_exp(aleph(1), aleph(0)), aleph(1))
        self.assertEqual(gch_card_exp(aleph(2), aleph(0)), aleph(2))
        self.assertEqual(gch_card_exp(aleph(2), aleph(1)), aleph(2))
        self.assertEqual(gch_card_exp(aleph(3), aleph(1)), aleph(3))
        self.assertEqual(gch_card_exp(aleph(3), aleph(2)), aleph(3))

    def test_singular_cardinals(self):
        # aleph_omega has cf(aleph_omega) = aleph_0
        # If lambda = cf(kappa) = aleph_0: aleph_omega^aleph_0 = aleph_(omega + 1)
        res_omega_0 = gch_card_exp(aleph("omega"), aleph(0))
        self.assertEqual(res_omega_0, aleph("omega+1"))

        # If lambda = aleph_1: cf(kappa) <= lambda < kappa implies kappa^lambda = kappa^+
        res_omega_1 = gch_card_exp(aleph("omega"), aleph(1))
        self.assertEqual(res_omega_1, aleph("omega+1"))

        # aleph_(omega_1) has cf = aleph_1. For lambda = aleph_0 < cf: kappa^lambda = kappa
        res_omega1_0 = gch_card_exp(aleph("omega_1"), aleph(0))
        self.assertEqual(res_omega1_0, aleph("omega_1"))


class TestHausdorffAndBernsteinFormulas(unittest.TestCase):
    """Test suite for Hausdorff and Bernstein formula evaluations."""

    def test_hausdorff_formula_instances(self):
        # aleph_(alpha + 1)^aleph_beta = aleph_alpha^aleph_beta * aleph_(alpha + 1)
        test_pairs = [
            (0, 0),  # aleph_1^aleph_0 = aleph_0^aleph_0 * aleph_1 = aleph_1 * aleph_1 = aleph_1
            (1, 0),  # aleph_2^aleph_0 = aleph_1^aleph_0 * aleph_2 = aleph_1 * aleph_2 = aleph_2
            (0, 1),  # aleph_1^aleph_1 = aleph_0^aleph_1 * aleph_1 = aleph_2 * aleph_1 = aleph_2
            (1, 1),  # aleph_2^aleph_1 = aleph_1^aleph_1 * aleph_2 = aleph_2 * aleph_2 = aleph_2
            (2, 1),  # aleph_3^aleph_1 = aleph_2^aleph_1 * aleph_3 = aleph_2 * aleph_3 = aleph_3
            (2, 2),  # aleph_3^aleph_2 = aleph_2^aleph_2 * aleph_3 = aleph_3 * aleph_3 = aleph_3
        ]
        for alpha, beta in test_pairs:
            with self.subTest(alpha=alpha, beta=beta):
                left, right = hausdorff_formula_evaluate(alpha, beta)
                self.assertEqual(left, right)

    def test_bernstein_formula_instances(self):
        # aleph_n^aleph_beta = 2^aleph_beta * aleph_n
        test_pairs = [
            (0, 0),  # aleph_0^aleph_0 = 2^aleph_0 * aleph_0 = aleph_1 * aleph_0 = aleph_1
            (1, 0),  # aleph_1^aleph_0 = 2^aleph_0 * aleph_1 = aleph_1 * aleph_1 = aleph_1
            (2, 0),  # aleph_2^aleph_0 = 2^aleph_0 * aleph_2 = aleph_1 * aleph_2 = aleph_2
            (3, 0),  # aleph_3^aleph_0 = 2^aleph_0 * aleph_3 = aleph_1 * aleph_3 = aleph_3
            (0, 1),  # aleph_0^aleph_1 = 2^aleph_1 * aleph_0 = aleph_2 * aleph_0 = aleph_2
            (1, 1),  # aleph_1^aleph_1 = 2^aleph_1 * aleph_1 = aleph_2 * aleph_1 = aleph_2
            (2, 1),  # aleph_2^aleph_1 = 2^aleph_1 * aleph_2 = aleph_2 * aleph_2 = aleph_2
            (3, 1),  # aleph_3^aleph_1 = 2^aleph_1 * aleph_3 = aleph_2 * aleph_3 = aleph_3
        ]
        for n, beta in test_pairs:
            with self.subTest(n=n, beta=beta):
                left, right = bernstein_formula_evaluate(n, beta)
                self.assertEqual(left, right)


class TestSilverTheorem(unittest.TestCase):
    """Test suite for Silver's Singular Cardinal Theorem consistency validation."""

    def test_silver_applies_uncountable_cofinality(self):
        # aleph_(omega_1) is singular with cf = aleph_1 > aleph_0
        lambda_c = aleph("omega_1")
        self.assertTrue(is_singular(lambda_c))
        self.assertGreater(cofinality(lambda_c), aleph(0))

        # Consistent case: 2^aleph_(omega_1) = aleph_(omega_1 + 1)
        res_ok = check_silver_condition(
            lambda_card=lambda_c,
            gch_below=True,
            power_at_lambda=aleph("omega_1+1"),
        )
        self.assertTrue(res_ok["silver_applies"])
        self.assertTrue(res_ok["consistent"])

        # Inconsistent case: 2^aleph_(omega_1) = aleph_(omega_1 + 2) violates Silver's Theorem
        res_bad = check_silver_condition(
            lambda_card=lambda_c,
            gch_below=True,
            power_at_lambda=aleph("omega_1+2"),
        )
        self.assertTrue(res_bad["silver_applies"])
        self.assertFalse(res_bad["consistent"])
        self.assertIn("Inconsistent with Silver Theorem", res_bad["explanation"])

    def test_silver_does_not_apply_to_countable_cofinality(self):
        # aleph_omega is singular with cf = aleph_0 (countable cofinality)
        lambda_c = aleph("omega")
        self.assertTrue(is_singular(lambda_c))
        self.assertEqual(cofinality(lambda_c), aleph(0))

        res = check_silver_condition(
            lambda_card=lambda_c,
            gch_below=True,
            power_at_lambda=aleph("omega+2"),
        )
        self.assertFalse(res["silver_applies"])
        self.assertTrue(res["consistent"])
        self.assertIn("countable cofinality", res["explanation"])

    def test_silver_does_not_apply_to_regular_cardinals(self):
        # aleph_1 is regular
        lambda_c = aleph(1)
        self.assertTrue(is_regular(lambda_c))

        res = check_silver_condition(
            lambda_card=lambda_c,
            gch_below=True,
            power_at_lambda=aleph(2),
        )
        self.assertFalse(res["silver_applies"])
        self.assertTrue(res["consistent"])


class TestEastonTheorem(unittest.TestCase):
    """Test suite for Easton function validation and forcing model simulation."""

    def test_valid_easton_functions(self):
        # Standard GCH is a valid Easton function
        f_gch = {aleph(0): aleph(1), aleph(1): aleph(2), aleph(2): aleph(3), aleph(3): aleph(4)}
        is_val, errs = is_valid_easton_function(f_gch)
        self.assertTrue(is_val)
        self.assertEqual(len(errs), 0)

        # Easton jump assignment: 2^aleph_0 = aleph_2, 2^aleph_1 = aleph_2, 2^aleph_2 = aleph_5
        # cf(aleph_2) = aleph_2 > aleph_0 and > aleph_1
        # cf(aleph_5) = aleph_5 > aleph_2
        f_jump = {aleph(0): aleph(2), aleph(1): aleph(2), aleph(2): aleph(5), aleph(3): aleph(5)}
        is_val_jump, errs_jump = is_valid_easton_function(f_jump)
        self.assertTrue(is_val_jump)
        self.assertEqual(len(errs_jump), 0)

    def test_invalid_easton_cantor_violation(self):
        # Violates Cantor: F(aleph_1) = aleph_1 < aleph_2
        f_bad = {aleph(0): aleph(1), aleph(1): aleph(1), aleph(2): aleph(3), aleph(3): aleph(4)}
        is_val, errs = is_valid_easton_function(f_bad)
        self.assertFalse(is_val)
        self.assertTrue(any("Cantor bound violated" in e for e in errs))

    def test_invalid_easton_monotonicity_violation(self):
        # Violates Monotonicity: F(aleph_0) = aleph_3 > F(aleph_1) = aleph_2
        f_bad = {aleph(0): aleph(3), aleph(1): aleph(2), aleph(2): aleph(3), aleph(3): aleph(4)}
        is_val, errs = is_valid_easton_function(f_bad)
        self.assertFalse(is_val)
        self.assertTrue(any("Monotonicity violated" in e for e in errs))

    def test_invalid_easton_konig_violation(self):
        # Violates Konig: F(aleph_1) = aleph_omega has cf = aleph_0 <= aleph_1
        f_bad = {aleph(0): aleph(1), aleph(1): aleph("omega"), aleph(2): aleph("omega+1"), aleph(3): aleph("omega+2")}
        is_val, errs = is_valid_easton_function(f_bad)
        self.assertFalse(is_val)
        self.assertTrue(any("Konig cofinality condition violated" in e for e in errs))

    def test_easton_model_simulator(self):
        assignment = {
            aleph(0): aleph(2),
            aleph(1): aleph(2),
            aleph(2): aleph(5),
            aleph(3): aleph(5),
        }
        model = EastonModel(assignment)

        # Power values
        self.assertEqual(model.power(aleph(0)), aleph(2))
        self.assertEqual(model.power(aleph(1)), aleph(2))
        self.assertEqual(model.power(aleph(2)), aleph(5))

        # Exponentiation values
        # aleph_0^aleph_1 = 2^aleph_1 = aleph_2
        self.assertEqual(model.exp(aleph(0), aleph(1)), aleph(2))
        # aleph_1^aleph_0 = max(aleph_1, 2^aleph_0) = aleph_2
        self.assertEqual(model.exp(aleph(1), aleph(0)), aleph(2))
        # aleph_2^aleph_1 = max(aleph_2, 2^aleph_1) = aleph_2
        self.assertEqual(model.exp(aleph(2), aleph(1)), aleph(2))
        # aleph_2^aleph_2 = 2^aleph_2 = aleph_5
        self.assertEqual(model.exp(aleph(2), aleph(2)), aleph(5))


class TestGlobalPowerAssignmentValidation(unittest.TestCase):
    """Test suite for global cardinal power assignment validation."""

    def test_valid_global_assignment(self):
        powers = {
            aleph(0): aleph(1),
            aleph(1): aleph(2),
            aleph(2): aleph(3),
            aleph("omega_1"): aleph("omega_1+1"),
        }
        is_val, errs = validate_cardinal_power_assignment(powers)
        self.assertTrue(is_val)
        self.assertEqual(len(errs), 0)

    def test_silver_violation_in_global_assignment(self):
        powers = {
            aleph(0): aleph(1),
            aleph(1): aleph(2),
            aleph(2): aleph(3),
            aleph("omega_1"): aleph("omega_1+2"),  # Violates Silver's Theorem
        }
        is_val, errs = validate_cardinal_power_assignment(powers)
        self.assertFalse(is_val)
        self.assertTrue(any("Inconsistent with Silver Theorem" in e for e in errs))


if __name__ == "__main__":
    unittest.main()
