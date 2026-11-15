(*
  Auto-generated / Mechanized Coq Bridge File
  Source context: /botworkspace/zfc (Sets.v, Axioms.v, Cartesian.v),
                  /botworkspace/article_isabelle_in_zfc (recursion.thy, additional.thy),
                  /hostramdisk/set_theory_prover (MKTD1-theory and MKTD2-theory)
  Generator / Author: Cross-System Set Theory Bridge Specialist
  Verification command: coqc -Q /botworkspace/zfc "" /tmp/CrossSystemSetTheoryBridge.v -o /tmp/CrossSystemSetTheoryBridge.vo
*)

Require Import Sets.
Require Import Axioms.
Require Import Cartesian.

Section CrossSystemBridge.

(* ========================================================================== *)
(* Part 1: Aczel-Werner Sets (Ens) Embedded into MKTD1 / MKTD2 Classes        *)
(* ========================================================================== *)

Definition ClassPred : Type := Ens -> Prop.

Definition extensional_class (C : ClassPred) : Prop :=
  forall x y : Ens, EQ x y -> C x -> C y.

Definition class_sub (C1 C2 : ClassPred) : Prop :=
  forall x : Ens, C1 x -> C2 x.

Definition class_eq (C1 C2 : ClassPred) : Prop :=
  forall x : Ens, C1 x <-> C2 x.

Definition set_to_class (E : Ens) : ClassPred :=
  fun x : Ens => IN x E.

Theorem set_to_class_extensional :
  forall E : Ens, extensional_class (set_to_class E).
Proof.
  unfold extensional_class, set_to_class.
  intros E x y Heq Hx.
  apply IN_sound_left with x; auto with zfc.
Qed.

Theorem set_to_class_sub_iff :
  forall E1 E2 : Ens, class_sub (set_to_class E1) (set_to_class E2) <-> INC E1 E2.
Proof.
  intros E1 E2; unfold class_sub, set_to_class, INC; split; intros H; exact H.
Qed.

Theorem set_to_class_eq_iff :
  forall E1 E2 : Ens, class_eq (set_to_class E1) (set_to_class E2) <-> EQ E1 E2.
Proof.
  intros E1 E2; unfold class_eq, set_to_class; split; intros H.
  - apply INC_EQ; unfold INC; intros x Hx; destruct (H x) as [H12 H21]; auto.
  - intros x; split; intros Hx.
    + apply IN_sound_right with E1; auto with zfc.
    + apply IN_sound_right with E2; auto with zfc.
Qed.

Definition UniversalClass : ClassPred := fun _ : Ens => True.

Theorem UniversalClass_extensional : extensional_class UniversalClass.
Proof.
  unfold extensional_class, UniversalClass; intros; exact I.
Qed.

Definition isSetClass (C : ClassPred) : Prop :=
  EXType Ens (fun E : Ens => class_eq C (set_to_class E)).

Theorem every_Ens_isSetClass :
  forall E : Ens, isSetClass (set_to_class E).
Proof.
  intros E; unfold isSetClass; exists E; unfold class_eq; intros x; split; auto.
Qed.

(* Class comprehension { x in V | P x } in MKTD1-theory / MKTD2-theory *)
Definition ClassComp (P : Ens -> Prop) : ClassPred := P.

(* Intersection of a class with a set yields a small set via Axioms.Comp *)
Theorem Separation_preserves_isSetClass :
  forall (E : Ens) (C : ClassPred),
  extensional_class C ->
  class_eq (fun x : Ens => IN x E /\ C x) (set_to_class (Comp E C)).
Proof.
  intros E C Hext x; unfold set_to_class; split; intros H.
  - destruct H as [HxE HxC].
    apply IN_P_Comp; auto.
    intros w1 w2 Hw1 Heq; apply (Hext w1 w2 Heq Hw1).
  - split.
    + apply (Comp_INC E C x H).
    + apply (IN_Comp_P E x C); auto.
      intros w1 w2 Hw1 Heq; apply (Hext w1 w2 Heq Hw1).
Qed.


(* ========================================================================== *)
(* Part 2: Isabelle/ZF Kuratowski Pairs and Double-Union Domain Bound         *)
(* ========================================================================== *)

(* In article_isabelle_in_zfc (recursion.thy / additional.thy), the ordered   *)
(* pair of sets a, b is the Kuratowski pair {{a}, {a, b}}.                    *)

Definition KuratowskiPair (A B : Ens) : Ens :=
  Paire (Sing A) (Paire A B).

Theorem KuratowskiPair_sound_left :
  forall A A' B : Ens, EQ A A' -> EQ (KuratowskiPair A B) (KuratowskiPair A' B).
Proof.
  unfold KuratowskiPair; intros A A' B Heq.
  apply EQ_tran with (Paire (Sing A') (Paire A B)).
  - apply Paire_sound_left; apply Sing_sound; exact Heq.
  - apply Paire_sound_right; apply Paire_sound_left; exact Heq.
Qed.

Theorem KuratowskiPair_sound_right :
  forall A B B' : Ens, EQ B B' -> EQ (KuratowskiPair A B) (KuratowskiPair A B').
Proof.
  unfold KuratowskiPair; intros A B B' Heq.
  apply Paire_sound_right; apply Paire_sound_right; exact Heq.
Qed.

(* Counterpart of theorem sinup in article_isabelle_in_zfc/recursion.thy:     *)
(* {A} in <A, B>_Kur and A in \Union <A, B>_Kur                               *)

Theorem sinup_bridge :
  forall A B : Ens, IN (Sing A) (KuratowskiPair A B).
Proof.
  intros A B; unfold KuratowskiPair; apply IN_Paire_left.
Qed.

Theorem Kuratowski_fst_in_Union :
  forall A B : Ens, IN A (Union (KuratowskiPair A B)).
Proof.
  intros A B.
  apply IN_Union with (Sing A).
  - apply sinup_bridge.
  - apply IN_Sing.
Qed.

Theorem Kuratowski_snd_in_Union :
  forall A B : Ens, IN B (Union (KuratowskiPair A B)).
Proof.
  intros A B.
  apply IN_Union with (Paire A B).
  - unfold KuratowskiPair; apply IN_Paire_right.
  - apply IN_Paire_right.
Qed.

(* Counterpart of lemma2 in article_isabelle_in_zfc/additional.thy:           *)
(* If <x, y>_Kur in f, then x in \Union (\Union f).                           *)

Theorem Isabelle_ZF_domain_in_Union_Union :
  forall f x y : Ens,
  IN (KuratowskiPair x y) f -> IN x (Union (Union f)).
Proof.
  intros f x y Hpair.
  apply IN_Union with (Sing x).
  - apply IN_Union with (KuratowskiPair x y).
    + exact Hpair.
    + apply sinup_bridge.
  - apply IN_Sing.
Qed.


(* ========================================================================== *)
(* Part 3: Dunaev Tagged Ordered Pairs for MKTD1-theory and MKTD2-theory      *)
(* ========================================================================== *)

(* In MKTD1-theory and MKTD2-theory, proper classes cannot be placed inside   *)
(* Kuratowski singletons {A} because a proper class is not an element of V.   *)
(* Dunaev Tagged Ordered Pairs [A, B]_D := ({0} x A) \cup ({1} x B) work      *)
(* uniformly for arbitrary classes A, B (both sets and proper classes).       *)

Definition Tag0 : Ens := Vide.
Definition Tag1 : Ens := Sing Vide.

Lemma Tag0_neq_Tag1 : EQ Tag0 Tag1 -> False.
Proof.
  intros Heq.
  cut F.
  - simple induction 1.
  - apply (not_EQ_Vide_Sing Vide Heq).
Qed.

Lemma Tag1_neq_Tag0 : EQ Tag1 Tag0 -> False.
Proof.
  intros Heq.
  cut F.
  - simple induction 1.
  - apply (not_EQ_Sing_Vide Vide Heq).
Qed.

Definition DunaevTaggedClassPair (A B : ClassPred) : ClassPred :=
  fun z : Ens =>
    (EXType Ens (fun x : Ens => A x /\ EQ z (Couple Tag0 x))) \/
    (EXType Ens (fun y : Ens => B y /\ EQ z (Couple Tag1 y))).

Theorem DunaevTaggedClassPair_extensional :
  forall A B : ClassPred,
  extensional_class (DunaevTaggedClassPair A B).
Proof.
  intros A B z1 z2 Heq Hz1.
  unfold DunaevTaggedClassPair in *.
  destruct Hz1 as [[x [Hx Hz1x]] | [y [Hy Hz1y]]].
  - left; exists x; split; [exact Hx |].
    apply EQ_tran with z1; [apply EQ_sym; exact Heq | exact Hz1x].
  - right; exists y; split; [exact Hy |].
    apply EQ_tran with z1; [apply EQ_sym; exact Heq | exact Hz1y].
Qed.

(* Unconditional injectivity of Dunaev Tagged Class Pairs for ALL extensional *)
(* classes A, A', B, B', including proper classes like UniversalClass V!      *)

Theorem DunaevTaggedClassPair_inj_left :
  forall A A' B B' : ClassPred,
  extensional_class A ->
  extensional_class A' ->
  class_eq (DunaevTaggedClassPair A B) (DunaevTaggedClassPair A' B') ->
  class_eq A A'.
Proof.
  intros A A' B B' HextA HextA' Heq x; split; intros Hx.
  - assert (Hin : DunaevTaggedClassPair A B (Couple Tag0 x)).
    { left; exists x; split; [exact Hx | apply EQ_refl]. }
    destruct (Heq (Couple Tag0 x)) as [Hlr _].
    destruct (Hlr Hin) as [[x' [Hx' Hcpl]] | [y' [Hy' Hcpl]]].
    + assert (Heqx : EQ x' x).
      { apply EQ_sym; apply (Couple_inj_right Tag0 x Tag0 x' Hcpl). }
      apply (HextA' x' x Heqx Hx').
    + exfalso.
      assert (Htag : EQ Tag0 Tag1).
      { apply (Couple_inj_left Tag0 x Tag1 y' Hcpl). }
      apply (Tag0_neq_Tag1 Htag).
  - assert (Hin : DunaevTaggedClassPair A' B' (Couple Tag0 x)).
    { left; exists x; split; [exact Hx | apply EQ_refl]. }
    destruct (Heq (Couple Tag0 x)) as [_ Hrl].
    destruct (Hrl Hin) as [[x' [Hx' Hcpl]] | [y' [Hy' Hcpl]]].
    + assert (Heqx : EQ x' x).
      { apply EQ_sym; apply (Couple_inj_right Tag0 x Tag0 x' Hcpl). }
      apply (HextA x' x Heqx Hx').
    + exfalso.
      assert (Htag : EQ Tag0 Tag1).
      { apply (Couple_inj_left Tag0 x Tag1 y' Hcpl). }
      apply (Tag0_neq_Tag1 Htag).
Qed.

Theorem DunaevTaggedClassPair_inj_right :
  forall A A' B B' : ClassPred,
  extensional_class B ->
  extensional_class B' ->
  class_eq (DunaevTaggedClassPair A B) (DunaevTaggedClassPair A' B') ->
  class_eq B B'.
Proof.
  intros A A' B B' HextB HextB' Heq y; split; intros Hy.
  - assert (Hin : DunaevTaggedClassPair A B (Couple Tag1 y)).
    { right; exists y; split; [exact Hy | apply EQ_refl]. }
    destruct (Heq (Couple Tag1 y)) as [Hlr _].
    destruct (Hlr Hin) as [[x' [Hx' Hcpl]] | [y' [Hy' Hcpl]]].
    + exfalso.
      assert (Htag : EQ Tag1 Tag0).
      { apply (Couple_inj_left Tag1 y Tag0 x' Hcpl). }
      apply (Tag1_neq_Tag0 Htag).
    + assert (Heqy : EQ y' y).
      { apply EQ_sym; apply (Couple_inj_right Tag1 y Tag1 y' Hcpl). }
      apply (HextB' y' y Heqy Hy').
  - assert (Hin : DunaevTaggedClassPair A' B' (Couple Tag1 y)).
    { right; exists y; split; [exact Hy | apply EQ_refl]. }
    destruct (Heq (Couple Tag1 y)) as [_ Hrl].
    destruct (Hrl Hin) as [[x' [Hx' Hcpl]] | [y' [Hy' Hcpl]]].
    + exfalso.
      assert (Htag : EQ Tag1 Tag0).
      { apply (Couple_inj_left Tag1 y Tag0 x' Hcpl). }
      apply (Tag1_neq_Tag0 Htag).
    + assert (Heqy : EQ y' y).
      { apply EQ_sym; apply (Couple_inj_right Tag1 y Tag1 y' Hcpl). }
      apply (HextB y' y Heqy Hy').
Qed.

(* Set-level Dunaev pair in Ens when both components are small sets E1, E2 *)
Definition DunaevEnsPair (E1 E2 : Ens) : Ens :=
  Union (Paire (Prod (Sing Tag0) E1) (Prod (Sing Tag1) E2)).

Theorem DunaevEnsPair_matches_ClassPair :
  forall E1 E2 : Ens,
  class_eq
    (set_to_class (DunaevEnsPair E1 E2))
    (DunaevTaggedClassPair (set_to_class E1) (set_to_class E2)).
Proof.
  intros E1 E2 z; unfold set_to_class, DunaevEnsPair, DunaevTaggedClassPair; split; intros Hz.
  - destruct (Union_IN (Paire (Prod (Sing Tag0) E1) (Prod (Sing Tag1) E2)) z Hz) as [W [HW HzW]].
    destruct (Paire_IN (Prod (Sing Tag0) E1) (Prod (Sing Tag1) E2) W HW) as [HW0 | HW1].
    + assert (Hz0 : IN z (Prod (Sing Tag0) E1)).
      { apply IN_sound_right with W; auto with zfc. }
      destruct (IN_Prod_EXType (Sing Tag0) E1 z Hz0) as [t [x Heq_tx]].
      assert (Hin_tx : IN (Couple t x) (Prod (Sing Tag0) E1)).
      { apply IN_sound_left with z; auto with zfc. }
      destruct (Couple_Prod_IN (Sing Tag0) E1 t x Hin_tx) as [Ht Hx].
      assert (Ht0 : EQ t Tag0) by (apply IN_Sing_EQ; exact Ht).
      left; exists x; split; [exact Hx |].
      apply EQ_tran with (Couple t x).
      * apply EQ_sym; exact Heq_tx.
      * apply Couple_sound_left; exact Ht0.
    + assert (Hz1 : IN z (Prod (Sing Tag1) E2)).
      { apply IN_sound_right with W; auto with zfc. }
      destruct (IN_Prod_EXType (Sing Tag1) E2 z Hz1) as [t [y Heq_ty]].
      assert (Hin_ty : IN (Couple t y) (Prod (Sing Tag1) E2)).
      { apply IN_sound_left with z; auto with zfc. }
      destruct (Couple_Prod_IN (Sing Tag1) E2 t y Hin_ty) as [Ht Hy].
      assert (Ht1 : EQ t Tag1) by (apply IN_Sing_EQ; exact Ht).
      right; exists y; split; [exact Hy |].
      apply EQ_tran with (Couple t y).
      * apply EQ_sym; exact Heq_ty.
      * apply Couple_sound_left; exact Ht1.
  - destruct Hz as [[x [Hx Hz0]] | [y [Hy Hz1]]].
    + apply IN_Union with (Prod (Sing Tag0) E1).
      * apply IN_Paire_left.
      * apply IN_sound_left with (Couple Tag0 x); [apply EQ_sym; exact Hz0 |].
        apply Couple_IN_Prod; [apply IN_Sing | exact Hx].
    + apply IN_Union with (Prod (Sing Tag1) E2).
      * apply IN_Paire_right.
      * apply IN_sound_left with (Couple Tag1 y); [apply EQ_sym; exact Hz1 |].
        apply Couple_IN_Prod; [apply IN_Sing | exact Hy].
Qed.

Corollary DunaevTaggedClassPair_preserves_isSetClass :
  forall E1 E2 : Ens,
  isSetClass (DunaevTaggedClassPair (set_to_class E1) (set_to_class E2)).
Proof.
  intros E1 E2; unfold isSetClass.
  exists (DunaevEnsPair E1 E2).
  intros z; destruct (DunaevEnsPair_matches_ClassPair E1 E2 z) as [H1 H2].
  split; auto.
Qed.

End CrossSystemBridge.
