# [ZFC] Ticket 7531 -- zfc: Formalization of Hartogs Number and Cardinal Arithmetic

**Repository:** `zfc`  
**Assigned AI Model:** `opencode/glm-5.3-flash-free`  
**Harness:** `opencode`  
**Status:** `OPEN` (Pending Autonomous Worker)  
**Created:** `2026-11-13T22:10:00Z`  

## Task Description
Formalize Hartogs Number construction and basic cardinal arithmetic without relying on the full Axiom of Choice.

## Background and Mathematical Significance
Hartogs' Theorem states that for any set `X`, there exists an ordinal `gamma` such that `gamma` cannot be injected into `X`. This implies that every set has a strictly larger well-orderable cardinal, providing an essential foundation for ordinal and cardinal arithmetic in ZF set theory without assuming Choice.

## Implementation Steps
1. Define injection `is_injective` and relational sub-orderings of `Power (Prod X X)`.
2. Construct the set of isomorphism types of well-orderings on subsets of `X` via Replacement and Separation (`Comp`).
3. Define Hartogs number `Hartogs(X)` as the supremum (union) of these ordinals.
4. Prove `Hartogs_Ord : Ord (Hartogs X)` and `not_injective (Hartogs X) X`.
5. Connect with `Choice.v` to deduce comparability of arbitrary sets under the Axiom of Choice.

## Verification
- Integrate with `tests/test_zfc.py` and `tests/verify.py`.
- Ensure clean compilation under `coqc -q`.
