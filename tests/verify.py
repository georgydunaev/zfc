#!/usr/bin/env python3
"""Standalone script to verify compilation of all Coq ZFC theories."""

import os
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

# List of Coq files in dependency order
coq_files = [
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
    "Cardinal.v",
    "cardinal_exponentiation.v",
    "gch_and_singular_cardinals.v",
    "zfc.v",
]

all_passed = True

for file in coq_files:
    path = os.path.join(ROOT, file)
    try:
        res = subprocess.run(["coqc", "-q", file], cwd=ROOT, check=True, capture_output=True, text=True)
        print(f"Successfully verified {file}")
    except subprocess.CalledProcessError as e:
        print(f"Failed to verify {file}: exit code {e.returncode}\n{e.stderr}")
        all_passed = False
        break

if not all_passed:
    sys.exit(1)
print("All Coq files successfully verified.")
