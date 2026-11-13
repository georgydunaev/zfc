# ZFC (Zermelo-Fraenkel Set Theory in Coq)

This repository provides a constructive formalization of Zermelo-Fraenkel set theory with Choice (ZFC) in the Coq proof assistant, based on Peter Aczel's inductive model of iterative sets (`Ens`).

## Core Architecture and The Model

The formalization builds set theory constructively on top of the Calculus of Inductive Constructions:

- `Sets.v`: The fundamental definition of the inductive type `Ens := sup (A : Type) (f : A to Ens)`, membership `IN`, and extensional equality `EQ`.
- `Axioms.v`: Core set-theoretic operations including empty set `Vide`, unordered pairing `Paire`, union `Union`, intersection `Inter`, powerset `Power`, and specification `Comp`.
- `Cartesian.v`: Ordered pairs `Couple`, Cartesian products `Prod`, and their injective properties.
- `Constructive.v`: Constructive logic foundations and properties of set relations.
- `Hierarchy.v`: Cumulative hierarchy stages.
- `Omega.v`: Set of natural numbers `Omega` as the first infinite limit set.
- `Ordinal_succession.v`: Successor operator `Class_succ` ($x \cup \{x\}$) and its properties.
- `Plump.v`: Plump ordinals (`Ord`), transitive closure, and ordinal monotonicity.
- `Replacement.v`: Relations between Type-theoretic choice, collection, and classical replacement.
- `Russell.v`: Russell's paradox establishing non-existence of a universal set.
- `Regularity.v` (and `3_Regularity.v`): Epsilon-induction `eps_ind`, well-foundedness `WF`, and derivation of the Axiom of Foundation (Regularity).
- `Ordinal_theory.v`: Cumulative hierarchy rank theorem `ex_rk`, proving $E \in V_L$ for every set $E$.
- `Limit_ordinals.v`: Definition of limit ordinals, construction of von Neumann ordinals `vn_nat`, and limit properties of `Union Omega_vn`.
- `Transfinite_recursion.v`: Transfinite induction schema on ordinals and bounded ordinal induction.
- `Choice.v`: Set-theoretic Axiom of Choice, choice function graphs, and Zermelo's Well-Ordering Theorem formulation.
- `zfc.v`: Monolithic unified formalization unit.

## Verification and Testing

### Prerequisites
- Coq 8.20+ (`coqc`)
- Python 3.10+

### Running the Test Suite
The repository includes a comprehensive Python test suite that verifies both Coq compilation of all 16 theory files and Python reference models for set-theoretic constructors and ordinal ranks:

```bash
python3 -m unittest discover -s tests -p 'test_*.py'
```

To run standalone Coq theory verification:

```bash
python3 tests/verify.py
```

## Ticket Tracking
Open and resolved architectural tickets are tracked in `tickets/`.
