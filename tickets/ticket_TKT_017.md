# [ZFC] Ticket TKT-017: Mechanization of Cardinal Addition and Multiplication

**Repository:** `zfc`
**Status:** OPEN
**Milestone:** Cardinal Arithmetic
**Dependencies:** `Cardinal.v`, `Cartesian.v`, `Choice.v`

## Summary
Mechanize cardinal addition, multiplication, and the absorption law for infinite cardinals in Coq:
kappa + lambda = kappa * lambda = max(kappa, lambda) for infinite cardinals kappa and lambda under the Axiom of Choice.

## Mathematical Formulation
1. Disjoint sum (cardinal addition): kappa + lambda is modeled as the cardinality of (kappa * {0}) U (lambda * {1}).
2. Cartesian product (cardinal multiplication): kappa * lambda is modeled as the cardinality of Prod kappa lambda.
3. For infinite initial ordinals kappa >= aleph_0, Hessenberg's theorem states kappa * kappa = kappa via canonical well-ordering of pairs (max(alpha, beta), alpha, beta).
4. As a corollary, for infinite cardinals kappa and lambda, kappa + lambda = kappa * lambda = max(kappa, lambda).

## Deliverables
1. Define cardinal sum constructor card_sum and product constructor card_prod.
2. Establish commutativity, associativity, and distributivity of cardinal operations up to equinumerosity.
3. Prove embedding lemmas: kappa <= card_sum kappa lambda and lambda <= card_sum kappa lambda.
4. Formalize the absorption theorem under Axiom of Choice.
5. Automated verification via Coq test suite with 0 Admitted.
