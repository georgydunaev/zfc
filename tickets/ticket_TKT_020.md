# [ZFC] Ticket TKT-020: Closed Unbounded Sets, Stationary Sets, Fodor's Lemma, and Solovay's Splitting Theorem

**Repository:** `zfc`
**Status:** RESOLVED
**Milestone:** Modern Set Theory, Club Filters, and Combinatorial Principles
**Dependencies:** `Sets.v`, `Axioms.v`, `Cartesian.v`, `Plump.v`, `Ordinal_theory.v`, `Ordinal_succession.v`, `Limit_ordinals.v`, `Choice.v`, `Cardinal.v`, `cardinal_exponentiation.v`, `gch_and_singular_cardinals.v`

## Summary
Formalize Closed Unbounded (Club) subsets of a regular uncountable cardinal kappa, the Club filter closed under finite and diagonal intersections, Stationary subsets intersecting every club, Fodor's Pressing Down Lemma for regressive functions, and Solovay's Splitting Theorem on partitioning stationary sets in Coq ZFC. Implement reference Python evaluation models and comprehensive unit tests.

## Mathematical Formulation
1. Closed Unbounded (Club) Subsets:
   Let kappa be an uncountable regular cardinal.
   A subset C of kappa is closed in the order topology if for every limit ordinal delta in kappa, if delta is a limit point of C (supremum of C cap delta equals delta), then delta belongs to C.
   A subset C of kappa is unbounded in kappa if for every alpha in kappa, there exists beta in C such that alpha is less than beta.
   A subset C is club if it is both closed and unbounded.

2. Club Filter and Intersection Properties:
   The family of club subsets of kappa forms a kappa-complete filter denoted Club_kappa:
   - If C1 and C2 are club subsets of kappa, then C1 cap C2 is a club subset of kappa.
   - If F = (C_alpha)_{alpha in kappa} is a kappa-sequence of club subsets, their diagonal intersection:
     Delta_{alpha in kappa} C_alpha = { xi in kappa : forall alpha in xi, xi in C_alpha }
     is also a club subset of kappa.

3. Stationary Sets:
   A subset S of kappa is stationary if S intersects every club subset C of kappa:
   for all club C in kappa, there exists alpha in kappa such that alpha in S and alpha in C.
   Equivalently, kappa setminus S contains no club subset.
   Every club set is stationary, and non-stationary subsets form an ideal dual to the club filter.

4. Fodor's Pressing Down Lemma (1956):
   Let kappa be an uncountable regular cardinal and S a stationary subset of kappa.
   Let f : S to kappa be a regressive function, meaning f(alpha) is strictly smaller than alpha for all non-zero alpha in S.
   Then there exists gamma in kappa such that the fiber:
     f^{-1}({gamma}) = { alpha in S : f(alpha) = gamma }
   is stationary in kappa.
   This establishes that the non-stationary ideal is normal (closed under diagonal unions).

5. Solovay's Splitting Theorem (1971):
   Let kappa be an uncountable regular cardinal and S a stationary subset of kappa.
   Then S can be partitioned into kappa pairwise disjoint stationary subsets:
   there exists a family (S_i)_{i in kappa} of pairwise disjoint stationary subsets of kappa whose union is S.

## Deliverables
1. Coq formalization in `club_and_stationary.v`:
   - Closed subset predicate `is_closed_subset`.
   - Unbounded subset predicate `is_unbounded_subset`.
   - Club subset predicate `is_club_subset`.
   - Intersection of two clubs is a club.
   - Diagonal intersection of a family of clubs `diagonal_intersection`.
   - Diagonal intersection of kappa clubs is a club.
   - Stationary subset predicate `is_stationary_subset`.
   - Fodor's Pressing Down Lemma formal statement `Fodors_Lemma_statement`.
   - Solovay's Splitting Theorem formal statement `Solovay_Splitting_statement`.
   - Clean compilation with 0 Admitted and 0 errors across all theories.
2. Python implementation in `zfc/stationary.py`:
   - Club verifier `is_club` and closure and unboundedness checks.
   - Diagonal intersection computation `diagonal_intersection`.
   - Stationary subset verifier `is_stationary`.
   - Fodor's lemma witness extractor `fodor_constant_witness` returning a stationary fiber.
   - Solovay's splitting partition constructor for canonical stationary sets.
   - Re-export symbols in `zfc/__init__.py`.
3. Unit test suite in `tests/test_club_and_stationary.py`:
   - Test cases covering clubs, diagonal intersection, stationary test, regressive functions, and Fodor's witness extraction.
   - Verify full test suite passes with 100 percent pass rate.
4. Build configuration updates:
   - Register `club_and_stationary.v` in `Make`, `Makefile`, and `tests/verify.py`.
