"""Unit tests for Closed Unbounded (Club) Sets, Stationary Sets,

Diagonal Intersections, Fodor's Pressing Down Lemma, and Solovay's Splitting Theorem.
"""

import os
import unittest

from zfc.stationary import (
    closure,
    default_limit_points,
    diagonal_intersection,
    fodor_constant_witness,
    generate_canonical_clubs,
    is_closed,
    is_club,
    is_regressive,
    is_stationary,
    is_unbounded,
    solovay_split,
)


class TestCoqClubAndStationaryFormalization(unittest.TestCase):
    """Verifies that club_and_stationary.v exists and contains all required formal entities."""

    def test_coq_theories_and_symbols(self):
        root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
        v_file = os.path.join(root, "club_and_stationary.v")
        self.assertTrue(os.path.exists(v_file), "club_and_stationary.v must exist")

        with open(v_file, "r", encoding="utf-8") as f:
            content = f.read()

        expected_symbols = [
            "In",
            "is_limit_point_of",
            "is_closed_subset",
            "is_unbounded_subset",
            "is_club_subset",
            "inter2",
            "closed_intersection",
            "club_intersection",
            "diagonal_intersection",
            "diagonal_intersection_is_club",
            "is_stationary_subset",
            "stationary_intersects_club",
            "club_is_stationary",
            "is_regressive_on",
            "fodor_fiber",
            "Fodors_Lemma_statement",
            "Fodors_Lemma_conditional",
            "is_stationary_partition",
            "Solovay_Splitting_statement",
            "Solovay_Splitting_conditional",
        ]
        for symbol in expected_symbols:
            self.assertIn(symbol, content, f"Missing {symbol} in club_and_stationary.v")


class TestClubSubsets(unittest.TestCase):
    """Test suite for closed unbounded (club) sets, closures, and intersections."""

    def setUp(self):
        self.kappa = 30
        self.limits = {10, 20}

    def test_full_set_is_club(self):
        full = set(range(self.kappa))
        self.assertTrue(is_unbounded(full, self.kappa))
        self.assertTrue(is_closed(full, self.kappa, self.limits))
        self.assertTrue(is_club(full, self.kappa, self.limits))

    def test_tail_is_club(self):
        tail = set(range(5, self.kappa))
        self.assertTrue(is_unbounded(tail, self.kappa))
        self.assertTrue(is_closed(tail, self.kappa, self.limits))
        self.assertTrue(is_club(tail, self.kappa, self.limits))

    def test_bounded_set_is_not_club(self):
        bounded = set(range(self.kappa - 2))
        self.assertFalse(is_unbounded(bounded, self.kappa))
        self.assertFalse(is_club(bounded, self.kappa, self.limits))

    def test_unclosed_set_is_not_club(self):
        # Set approaches limit 10 (contains 9) but omits 10
        unclosed = set(range(self.kappa)) - {10}
        self.assertTrue(is_unbounded(unclosed, self.kappa))
        self.assertFalse(is_closed(unclosed, self.kappa, self.limits))
        self.assertFalse(is_club(unclosed, self.kappa, self.limits))

    def test_topological_closure(self):
        # Set missing 10 and 20
        raw = set(range(self.kappa)) - {10, 20}
        self.assertFalse(is_closed(raw, self.kappa, self.limits))
        cl = closure(raw, self.kappa, self.limits)
        self.assertIn(10, cl)
        self.assertIn(20, cl)
        self.assertTrue(is_closed(cl, self.kappa, self.limits))
        self.assertTrue(is_club(cl, self.kappa, self.limits))

    def test_club_intersection(self):
        # Intersection of two clubs is a club
        c1 = set(range(4, self.kappa))
        c2 = set(range(8, self.kappa))
        inter = c1 & c2
        self.assertTrue(is_club(c1, self.kappa, self.limits))
        self.assertTrue(is_club(c2, self.kappa, self.limits))
        self.assertTrue(is_club(inter, self.kappa, self.limits))


class TestDiagonalIntersection(unittest.TestCase):
    """Test suite for diagonal intersections of club families."""

    def setUp(self):
        self.kappa = 25
        self.limits = {10, 20}

    def test_diagonal_intersection_contains_zero(self):
        # Any diagonal intersection vacuously contains 0
        clubs = [set(range(self.kappa)) for _ in range(self.kappa)]
        diag = diagonal_intersection(clubs, self.kappa)
        self.assertIn(0, diag)

    def test_diagonal_intersection_characteristic_property(self):
        # Define family C_alpha = [alpha, kappa)
        clubs = [set(range(a, self.kappa)) for a in range(self.kappa)]
        diag = diagonal_intersection(clubs, self.kappa)

        # For any xi in kappa, xi in diag if and only if for all alpha < xi, xi in C_alpha
        for xi in range(self.kappa):
            expected = all(xi in clubs[alpha] for alpha in range(xi))
            self.assertEqual(xi in diag, expected)

    def test_diagonal_intersection_of_clubs_is_club(self):
        # Define clubs: tails [a, kappa)
        clubs = [closure(set(range(min(a, self.kappa - 1), self.kappa)), self.kappa, self.limits) for a in range(self.kappa)]
        diag = diagonal_intersection(clubs, self.kappa)
        self.assertTrue(is_unbounded(diag, self.kappa))
        self.assertTrue(is_closed(diag, self.kappa, self.limits))
        self.assertTrue(is_club(diag, self.kappa, self.limits))


class TestStationarySets(unittest.TestCase):
    """Test suite for stationary set verification."""

    def setUp(self):
        self.kappa = 20
        self.limits = {5, 10, 15}

    def test_club_is_stationary(self):
        club = set(range(self.kappa))
        self.assertTrue(is_stationary(club, self.kappa, limit_points=self.limits))

    def test_tail_is_stationary(self):
        tail = set(range(3, self.kappa))
        self.assertTrue(is_stationary(tail, self.kappa, limit_points=self.limits))

    def test_bounded_set_is_not_stationary(self):
        bounded = {1, 2, 3, 4}
        self.assertFalse(is_stationary(bounded, self.kappa, limit_points=self.limits))

    def test_empty_set_is_not_stationary(self):
        self.assertFalse(is_stationary(set(), self.kappa, limit_points=self.limits))

    def test_complement_of_club_is_not_stationary(self):
        # Tail [5, kappa) is club, so its complement [0, 5) contains no club
        # and misses the club [5, kappa)
        tail = set(range(5, self.kappa))
        comp = set(range(5))
        self.assertTrue(is_club(tail, self.kappa, self.limits))
        self.assertFalse(is_stationary(comp, self.kappa, limit_points=self.limits))


class TestFodorsLemma(unittest.TestCase):
    """Test suite for regressive functions and Fodor's Pressing Down Lemma."""

    def setUp(self):
        self.kappa = 30
        self.limits = {10, 20}
        self.stationary_set = set(range(self.kappa))

    def test_is_regressive_valid(self):
        # Predecessor map f(alpha) = max(0, alpha - 1)
        f = {a: max(0, a - 1) for a in self.stationary_set}
        self.assertTrue(is_regressive(f, self.stationary_set))

    def test_is_regressive_invalid_identity(self):
        # Identity f(alpha) = alpha is not regressive
        f_id = {a: a for a in self.stationary_set}
        self.assertFalse(is_regressive(f_id, self.stationary_set))

    def test_is_regressive_invalid_exceeding(self):
        # Exceeding map f(alpha) = alpha + 1 is not regressive
        f_ex = {a: a + 1 for a in self.stationary_set}
        self.assertFalse(is_regressive(f_ex, self.stationary_set))

    def test_fodor_witness_constant_fiber(self):
        # Regressive function: maps elements to residue or step
        # f(alpha) = alpha // 10 is strictly less than alpha for all alpha >= 2
        f = {a: (a // 10 if a >= 2 else 0) for a in self.stationary_set}
        self.assertTrue(is_regressive(f, self.stationary_set))

        gamma, fiber = fodor_constant_witness(
            self.stationary_set, f, self.kappa, limit_points=self.limits
        )
        self.assertGreaterEqual(gamma, 0)
        self.assertLess(gamma, self.kappa)
        self.assertTrue(len(fiber) > 0)
        # All elements in fiber have f(alpha) == gamma
        for a in fiber:
            self.assertEqual(f[a], gamma)

    def test_fodor_witness_predecessor_function(self):
        # Constant on segments regressive function
        def reg_fn(x: int) -> int:
            return 0 if x <= 5 else 3

        f = {a: reg_fn(a) for a in self.stationary_set}
        self.assertTrue(is_regressive(f, self.stationary_set))

        gamma, fiber = fodor_constant_witness(
            self.stationary_set, f, self.kappa, limit_points=self.limits
        )
        self.assertIn(gamma, [0, 3])
        self.assertTrue(is_stationary(fiber, self.kappa, limit_points=self.limits))


class TestSolovaySplitting(unittest.TestCase):
    """Test suite for Solovay's Splitting partition construction."""

    def setUp(self):
        self.kappa = 30
        self.limits = {10, 20}
        self.stationary_set = set(range(self.kappa))

    def test_solovay_split_two_parts(self):
        parts = solovay_split(self.stationary_set, self.kappa, n_parts=2, limit_points=self.limits)
        self.assertEqual(len(parts), 2)
        s0, s1 = parts[0], parts[1]

        # Disjoint
        self.assertEqual(s0 & s1, set())
        # Union equals S
        self.assertEqual(s0 | s1, self.stationary_set)
        # Both non-empty
        self.assertTrue(len(s0) > 0)
        self.assertTrue(len(s1) > 0)
        # Both stationary
        self.assertTrue(is_stationary(s0, self.kappa, limit_points=self.limits))
        self.assertTrue(is_stationary(s1, self.kappa, limit_points=self.limits))

    def test_solovay_split_three_parts(self):
        parts = solovay_split(self.stationary_set, self.kappa, n_parts=3, limit_points=self.limits)
        self.assertEqual(len(parts), 3)

        # Pairwise disjoint
        for i in range(3):
            for j in range(i + 1, 3):
                self.assertEqual(parts[i] & parts[j], set())

        # Union equals S
        union_all = set().union(*parts)
        self.assertEqual(union_all, self.stationary_set)

        # All parts stationary
        for p in parts:
            self.assertTrue(len(p) > 0)
            self.assertTrue(is_stationary(p, self.kappa, limit_points=self.limits))


if __name__ == "__main__":
    unittest.main()
