# [ZFC] Ticket TKT-015: Formalization of Hartogs Theorem in Coq

**Repository:** `zfc`
**Status:** IN PROGRESS
**Milestone:** Cardinality and Ordinal Embeddings
**Dependencies:** `Sets.v`, `Axioms.v`, `Plump.v`, `Ordinal_theory.v`

## Summary
Formalize Hartogs' Theorem in ZFC set theory within Coq without reliance on the Axiom of Choice.
For every set x, there exists an ordinal alpha that cannot be injectively embedded into x.

## Mathematical Formulation
In ZF set theory, Hartogs (1915) established that the class of well-orderable cardinals is unbounded.
Specifically, for any set x:
1. The collection of ordinals that can be injectively embedded into x is bounded by the powerset structure of x.
2. The supremum (or collection of ordinal subsets) forms a von Neumann ordinal alpha.
3. If alpha were injectively embedded into x, then alpha would belong to alpha, contradicting well-foundedness (E_not_IN_E).
4. Therefore, not (injects alpha x).

## Deliverables
1. Define injectivity (injects x y, or x <= y) and equinumerosity (equipotent x y, or x ~ y) in Cardinal.v.
2. Define Hartogs ordinal constructor hartogs(x).
3. Prove Ord (hartogs x) using the plump ordinal characterization (Ord_intro).
4. Prove non-embeddability: not (injects (hartogs x) x) or not (INC (hartogs x) x).
5. Ensure 0 Admitted and 0 admit.
