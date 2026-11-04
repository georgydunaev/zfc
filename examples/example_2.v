(*
 * Example 2: Union of Sets
 *
 * This example demonstrates how to use the Union axiom of ZFC to prove that the union of two sets is a set.
 *
 * Author: mistral/mistral-small-latest (Capability Tier 1)
 *
 *)

Require Import zfc.

Theorem example_2: forall A B, exists C, forall x, x ∈ C <-> x ∈ A \/ x ∈ B.
Proof.
  intros A B.
  exists (A ∪ B).
  intros x.
  split.
    - intros H. destruct H as [H1 | H2]. left; assumption. right; assumption.
    - intros H. destruct H as [H1 | H2]. left; assumption. right; assumption.
Qed.
