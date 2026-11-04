(*
 * Example 1: Existence of a Set with a Specific Property
 *
 * This example demonstrates how to use the ZFC axioms to prove the existence of a set with a specific property.
 *
 * Author: mistral/mistral-small-latest (Capability Tier 1)
 *
 *)

Require Import zfc.

Theorem example_1: exists x, x ∈ {0, 1, 2}.
Proof.
  exists 0.
  trivial.
Qed.
