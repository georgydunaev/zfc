#!/usr/bin/env python3
"""Unit test wrapper for zfc Coq formalization."""

import os
import unittest

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


class TestZFC(unittest.TestCase):
    def test_core_coq_modules_exist(self):
        core = [
            "Axioms.v",
            "Sets.v",
            "Cartesian.v",
            "Constructive.v",
            "Hierarchy.v",
            "Omega.v",
            "Ordinal_theory.v",
            "Plump.v",
            "Replacement.v",
            "Russell.v",
            "3_Regularity.v",
            "zfc.v",
        ]
        for fname in core:
            fpath = os.path.join(ROOT, fname)
            self.assertTrue(os.path.isfile(fpath), f"Missing {fpath}")
            self.assertGreater(os.path.getsize(fpath), 100)


if __name__ == "__main__":
    unittest.main()
