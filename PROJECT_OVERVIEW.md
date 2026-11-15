# Project Overview: Aczel Iterative Set Theory and ZFC in Coq (`zfc`)

## 1. Purpose and Scope
`zfc` (`/botworkspace/zfc`) is a constructive and classical Coq formalization of Zermelo-Fraenkel Set Theory with Choice (`ZFC`) built on Peter Aczel's inductive type of iterative sets (`Ens := sup (A : Type) (f : A to Ens)`). Compiled `.vo` files are strictly immutable per Fact 11.

## 2. Core Coq Modules
- [Sets.v](file:///botworkspace/zfc/Sets.v) and [Axioms.v](file:///botworkspace/zfc/Axioms.v) — Inductive definition of `Ens`, extensional equality `EQ`, membership `IN`, empty set `Vide`, pairing `Paire`, union `Union`, intersection `Inter`, power set `Power`, and bounded comprehension `Comp`.
- [Cartesian.v](file:///botworkspace/zfc/Cartesian.v) and [Constructive.v](file:///botworkspace/zfc/Constructive.v) — Kuratowski ordered pairs `Couple`, Cartesian products `Prod`, and constructive relation properties.
- [Russell.v](file:///botworkspace/zfc/Russell.v) and [Regularity.v](file:///botworkspace/zfc/Regularity.v) — Russell's paradox (no universal set) and epsilon-induction / Foundation (`eps_ind`, `WF`).
- [Omega.v](file:///botworkspace/zfc/Omega.v), [Ordinal_succession.v](file:///botworkspace/zfc/Ordinal_succession.v), [Plump.v](file:///botworkspace/zfc/Plump.v), [Limit_ordinals.v](file:///botworkspace/zfc/Limit_ordinals.v), and [Ordinal_theory.v](file:///botworkspace/zfc/Ordinal_theory.v) — Finite and transfinite ordinals, plump ordinals, cumulative hierarchy stages `Hierarchy.v`, and rank existence (`ex_rk`).
- [Transfinite_recursion.v](file:///botworkspace/zfc/Transfinite_recursion.v), [Replacement.v](file:///botworkspace/zfc/Replacement.v), [Choice.v](file:///botworkspace/zfc/Choice.v), and [Cardinal.v](file:///botworkspace/zfc/Cardinal.v) — Transfinite recursion, Replacement, Choice, and cardinal arithmetic.
- `tests/` — Automated Python verification suite.

## 3. Verification
```bash
python3 -m unittest discover -s /botworkspace/zfc/tests -p "test_*.py"
```
