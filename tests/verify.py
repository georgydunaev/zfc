#!/usr/bin/env python3

import os
import subprocess

# List of Coq files to verify
coq_files = [
    "3_Regularity.v",
    "Axioms.v",
    "Cartesian.v",
    "Constructive.v",
    "Hierarchy.v",
    "Omega.v",
    "Ordinal_theory.v",
    "Plump.v",
    "Replacement.v",
    "Russell.v",
    "Sets.v",
    "zfc.v"
]

# Verify each Coq file
for file in coq_files:
    try:
        subprocess.run(["coqc", file], check=True)
        print(f"Successfully verified {file}")
    except subprocess.CalledProcessError as e:
        print(f"Failed to verify {file}: {e}")
