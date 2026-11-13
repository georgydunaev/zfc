# [ZFC] Ticket TKT-016: Formalization of Initial Ordinals and Cardinal Numbers

**Repository:** `zfc`
**Status:** RESOLVED
**Milestone:** Cardinality and Ordinal Embeddings
**Dependencies:** `Sets.v`, `Plump.v`, `Limit_ordinals.v`, `Cardinal.v`

## Summary
Formalize the concept of initial ordinals and cardinal numbers in Coq. An ordinal alpha is a cardinal number if and only if it cannot be put in one-to-one correspondence with any strictly smaller ordinal beta in alpha.

## Mathematical Formulation
In von Neumann cardinal assignment:
1. An ordinal alpha is initial (is_cardinal alpha) if for all beta in alpha, not (equipotent alpha beta).
2. The empty set Vide is the cardinal 0.
3. The successor ordinal Succ Vide is the cardinal 1.
4. The first limit ordinal Omega_vn (Union Omega_vn) represents aleph_0, the least infinite cardinal.
5. In ZFC with Choice, every set has a unique cardinal; without Choice, initial ordinals represent well-orderable cardinalities.

## Deliverables
1. Define is_cardinal and is_initial_ordinal in Cardinal.v. (Completed)
2. Prove cardinal_Vide: is_cardinal Vide. (Completed)
3. Prove cardinal_Succ_Vide: is_cardinal (Succ Vide). (Completed)
4. Formulate the definition of aleph_0 and verify its ordinal property. (Completed: `aleph_0`, `Ord_aleph_0`)
5. Ensure 0 Admitted and 0 admit across all proofs. (Completed: verified 0 Admitted across all theories)
