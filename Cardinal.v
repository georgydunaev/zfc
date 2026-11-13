(* This program is free software; you can redistribute it and/or      *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2.1   *)
(* of the License, or (at your option) any later version.             *)
(*                                                                    *)
(* This program is distributed in the hope that it will be useful,    *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU General Public License for more details.                       *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 02110-1301 USA                                                     *)

(* Formalization of Cardinals, Cantor's Theorem, Hartogs' Ordinal,    *)
(* and Initial Ordinals in ZFC set theory.                            *)

Require Import Sets.
Require Import Axioms.
Require Import Cartesian.
Require Import Plump.
Require Import Ordinal_succession.
Require Import Limit_ordinals.
Require Import Choice.

(* ================================================================= *)
(* Section 1: Set Maps, Injections, Surjections, and Bijections     *)
(* ================================================================= *)

Definition is_map (x y : Ens) (f : Ens -> Ens) : Prop :=
  (forall a : Ens, IN a x -> IN (f a) y) /\
  (forall a b : Ens, IN a x -> IN b x -> EQ a b -> EQ (f a) (f b)).

Definition is_inj (x y : Ens) (f : Ens -> Ens) : Prop :=
  is_map x y f /\
  (forall a b : Ens, IN a x -> IN b x -> EQ (f a) (f b) -> EQ a b).

Definition is_surj (x y : Ens) (f : Ens -> Ens) : Prop :=
  is_map x y f /\
  (forall b : Ens, IN b y -> EXType Ens (fun a => IN a x /\ EQ (f a) b)).

Definition is_bij (x y : Ens) (f : Ens -> Ens) : Prop :=
  is_inj x y f /\ is_surj x y f.

Definition injects (x y : Ens) : Prop :=
  EXType (Ens -> Ens) (fun f => is_inj x y f).

Definition equipotent (x y : Ens) : Prop :=
  EXType (Ens -> Ens) (fun f => is_bij x y f).

Definition strictly_smaller (x y : Ens) : Prop :=
  injects x y /\ ~ injects y x.

Theorem injects_refl : forall x : Ens, injects x x.
Proof.
intros x.
exists (fun a => a).
split.
- split.
  + intros a Ina. exact Ina.
  + intros a b Ina Inb Heq. exact Heq.
- intros a b Ina Inb Heq. exact Heq.
Qed.

Theorem equipotent_refl : forall x : Ens, equipotent x x.
Proof.
intros x.
exists (fun a => a).
split.
- split.
  + split.
    * intros a Ina. exact Ina.
    * intros a b Ina Inb Heq. exact Heq.
  + intros a b Ina Inb Heq. exact Heq.
- split.
  + split.
    * intros a Ina. exact Ina.
    * intros a b Ina Inb Heq. exact Heq.
  + intros b Inb.
    exists b.
    split; [exact Inb | apply EQ_refl].
Qed.

Theorem equipotent_injects : forall x y : Ens,
  equipotent x y -> injects x y.
Proof.
intros x y [f [Hinj Hsurj]].
exists f.
exact Hinj.
Qed.

Theorem equipotent_trans : forall x y z : Ens,
  equipotent x y -> equipotent y z -> equipotent x z.
Proof.
intros x y z [f [[[Hf_in Hf_ext] Hf_inj] [_ Hf_surj]]] [g [[[Hg_in Hg_ext] Hg_inj] [_ Hg_surj]]].
exists (fun a => g (f a)).
split.
- split.
  + split.
    * intros a Ina. apply Hg_in. apply Hf_in. exact Ina.
    * intros a b Ina Inb Heq. apply Hg_ext.
      -- apply Hf_in. exact Ina.
      -- apply Hf_in. exact Inb.
      -- apply Hf_ext; assumption.
  + intros a b Ina Inb Heq.
    assert (Heq_fab : EQ (f a) (f b)).
    {
      apply Hg_inj.
      - apply Hf_in. exact Ina.
      - apply Hf_in. exact Inb.
      - exact Heq.
    }
    apply (Hf_inj a b Ina Inb Heq_fab).
- split.
  + split.
    * intros a Ina. apply Hg_in. apply Hf_in. exact Ina.
    * intros a b Ina Inb Heq. apply Hg_ext.
      -- apply Hf_in. exact Ina.
      -- apply Hf_in. exact Inb.
      -- apply Hf_ext; assumption.
  + intros c Inc.
    destruct (Hg_surj c Inc) as [b [Inb Heq_gb_c]].
    destruct (Hf_surj b Inb) as [a [Ina Heq_fa_b]].
    exists a.
    split; [exact Ina |].
    apply EQ_tran with (g b).
    * apply Hg_ext.
      -- apply Hf_in. exact Ina.
      -- exact Inb.
      -- exact Heq_fa_b.
    * exact Heq_gb_c.
Qed.

Theorem injects_trans : forall x y z : Ens,
  injects x y -> injects y z -> injects x z.
Proof.
intros x y z [f [[Hf_in Hf_ext] Hf_inj]] [g [[Hg_in Hg_ext] Hg_inj]].
exists (fun a => g (f a)).
split.
- split.
  + intros a Ina.
    apply Hg_in.
    apply Hf_in.
    exact Ina.
  + intros a b Ina Inb Heq.
    apply Hg_ext.
    * apply Hf_in. exact Ina.
    * apply Hf_in. exact Inb.
    * apply Hf_ext; assumption.
- intros a b Ina Inb Heq.
  assert (Heq_fab : EQ (f a) (f b)).
  {
    apply Hg_inj.
    - apply Hf_in. exact Ina.
    - apply Hf_in. exact Inb.
    - exact Heq.
  }
  apply (Hf_inj a b Ina Inb Heq_fab).
Qed.

Theorem not_injects_nonempty_Vide : forall y : Ens,
  (EXType Ens (fun e => IN e y)) -> injects y Vide -> False.
Proof.
intros y [e Ine] [f [[Hf_in _] _]].
assert (Hin : IN (f e) Vide).
{ apply (Hf_in e Ine). }
elim (Vide_est_vide (f e) Hin).
Qed.

(* ================================================================= *)
(* Section 2: Cantor's Theorem (x strictly smaller than Power x)    *)
(* ================================================================= *)

Theorem Cantor_inj : forall x : Ens, injects x (Power x).
Proof.
intros x.
exists (fun a => Sing a).
split.
- split.
  + intros a Ina.
    apply INC_IN_Power.
    unfold INC.
    intros e Ine.
    assert (Heq : EQ e a).
    { apply (IN_Sing_EQ e a Ine). }
    apply (IN_sound_left a e x).
    * apply EQ_sym. exact Heq.
    * exact Ina.
  + intros a b Ina Inb Heq.
    apply (Sing_sound a b Heq).
- intros a b Ina Inb Heq.
  apply (IN_Sing_EQ a b).
  apply (IN_sound_right a (Sing a) (Sing b) Heq).
  apply IN_Sing.
Qed.

Theorem Cantor_no_surj : forall (x : Ens) (f : Ens -> Ens),
  is_map x (Power x) f ->
  (forall b : Ens, IN b (Power x) -> EXType Ens (fun a => IN a x /\ EQ (f a) b)) ->
  False.
Proof.
intros x f [Hf_in Hf_ext] Hsurj.
set (P := fun a : Ens =>
  forall a' : Ens, EQ a a' -> IN a' x -> IN a' (f a') -> False).
set (D := Comp x P).
assert (Hinc_D : INC D x).
{ apply Comp_INC. }
assert (Hin_D_pow : IN D (Power x)).
{ apply INC_IN_Power. exact Hinc_D. }
destruct (Hsurj D Hin_D_pow) as [d [Hin_d_x Heq_fd_D]].
assert (HP_sound : forall w1 w2 : Ens, P w1 -> EQ w1 w2 -> P w2).
{
  intros w1 w2 HPw1 Heq12 a' Heq2a Ina' Inf.
  apply (HPw1 a').
  - apply (EQ_tran w1 w2 a'); assumption.
  - exact Ina'.
  - exact Inf.
}
assert (Hnot_d_D : IN d D -> False).
{
  intro Hin_d_D.
  assert (HPd : P d).
  { apply (IN_Comp_P x d P HP_sound Hin_d_D). }
  apply (HPd d (EQ_refl d) Hin_d_x).
  apply (IN_sound_right d D (f d)).
  - apply EQ_sym. exact Heq_fd_D.
  - exact Hin_d_D.
}
assert (Hin_d_D : IN d D).
{
  apply (IN_P_Comp x d P HP_sound Hin_d_x).
  intros a' Heq_da Ina' Hin_a'_fa'.
  apply Hnot_d_D.
  assert (Heq_fda_fa' : EQ (f d) (f a')).
  { apply Hf_ext; assumption. }
  assert (Hin_d_D : IN d D).
  {
    apply (IN_sound_right d (f d) D Heq_fd_D).
    apply (IN_sound_right d (f a') (f d)).
    - apply EQ_sym. exact Heq_fda_fa'.
    - apply (IN_sound_left a' d (f a')).
      + apply EQ_sym. exact Heq_da.
      + exact Hin_a'_fa'.
  }
  exact Hin_d_D.
}
exact (Hnot_d_D Hin_d_D).
Qed.

Theorem Cantor_no_inj : forall (x : Ens) (g : Ens -> Ens),
  is_inj (Power x) x g -> False.
Proof.
intros x g [Hmap Hinj].
destruct Hmap as [Hmap_in Hmap_ext].
set (P := fun z : Ens =>
  EXType Ens (fun A : Ens =>
    IN A (Power x) /\ EQ z (g A) /\ (IN z A -> False))).
set (D := Comp x P).
assert (Hinc_D : INC D x).
{ apply Comp_INC. }
assert (Hin_D_pow : IN D (Power x)).
{ apply INC_IN_Power. exact Hinc_D. }
set (d := g D).
assert (Hin_d_x : IN d x).
{ apply (Hmap_in D Hin_D_pow). }
assert (HP_sound : forall w1 w2 : Ens, P w1 -> EQ w1 w2 -> P w2).
{
  intros w1 w2 [A [HinA [Heq1 Hnot]]] Heq12.
  exists A.
  split; [exact HinA |].
  split.
  - apply (EQ_tran w2 w1 (g A)).
    + apply EQ_sym. exact Heq12.
    + exact Heq1.
  - intro Hin_w2_A.
    apply Hnot.
    apply (IN_sound_left w2 w1 A).
    + apply EQ_sym. exact Heq12.
    + exact Hin_w2_A.
}
assert (Hnot_in_d_D : IN d D -> False).
{
  intro Hin_d_D.
  assert (HPd : P d).
  { apply (IN_Comp_P x d P HP_sound Hin_d_D). }
  destruct HPd as [A [HinA [Heq_d_gA Hnot_d_A]]].
  assert (Heq_gD_gA : EQ (g D) (g A)).
  { exact Heq_d_gA. }
  assert (Heq_D_A : EQ D A).
  { apply (Hinj D A Hin_D_pow HinA Heq_gD_gA). }
  assert (Hin_d_A : IN d A).
  { apply (IN_sound_right d D A Heq_D_A Hin_d_D). }
  exact (Hnot_d_A Hin_d_A).
}
assert (Hin_d_D : IN d D).
{
  apply (IN_P_Comp x d P HP_sound Hin_d_x).
  exists D.
  split; [exact Hin_D_pow |].
  split; [apply EQ_refl |].
  exact Hnot_in_d_D.
}
exact (Hnot_in_d_D Hin_d_D).
Qed.

Theorem Cantor_not_injects : forall x : Ens,
  injects (Power x) x -> False.
Proof.
intros x [g Hg].
exact (Cantor_no_inj x g Hg).
Qed.

Theorem Cantor_strict : forall x : Ens,
  strictly_smaller x (Power x).
Proof.
intros x.
split.
- apply Cantor_inj.
- intro H.
  apply (Cantor_not_injects x H).
Qed.

(* ================================================================= *)
(* Section 3: Hartogs' Ordinal Construction and Non-Inclusion       *)
(* ================================================================= *)

Definition hartogs (x : Ens) : Ens :=
  Comp (Power x) Ord.

Lemma Ord_hartogs : forall x : Ens, Ord (hartogs x).
Proof.
intros x.
unfold hartogs.
apply Ord_intro.
- intros E' InE'.
  apply (IN_Comp_P (Power x) E' Ord).
  + intros w1 w2 Ow1 Heq. apply (Ord_sound w1 w2 Heq Ow1).
  + exact InE'.
- intros E1 E2 OE1 OE2 InE1 IncE21.
  apply IN_P_Comp.
  + intros w1 w2 Ow1 Heq. apply (Ord_sound w1 w2 Heq Ow1).
  + apply INC_IN_Power.
    apply INC_tran with E1.
    * exact IncE21.
    * apply IN_Power_INC.
      apply (Comp_INC (Power x) Ord E1 InE1).
  + exact OE2.
Qed.

Theorem not_INC_hartogs : forall x : Ens,
  INC (hartogs x) x -> False.
Proof.
intros x Hinc.
assert (Hin : IN (hartogs x) (hartogs x)).
{
  unfold hartogs.
  apply IN_P_Comp.
  - intros w1 w2 Ow1 Heq. apply (Ord_sound w1 w2 Heq Ow1).
  - apply INC_IN_Power. exact Hinc.
  - apply Ord_hartogs.
}
elim (E_not_IN_E (hartogs x) Hin).
Qed.

Theorem not_injects_hartogs_Vide : injects (hartogs Vide) Vide -> False.
Proof.
intros [f [[Hf_in _] _]].
assert (Hin_Vide : IN Vide (hartogs Vide)).
{
  unfold hartogs.
  apply IN_P_Comp.
  - intros w1 w2 Ow1 Heq. apply (Ord_sound w1 w2 Heq Ow1).
  - apply INC_IN_Power.
    apply INC_refl.
  - apply Ord_Vide.
}
assert (Hbad : IN (f Vide) Vide).
{ apply (Hf_in Vide Hin_Vide). }
elim (Vide_est_vide (f Vide) Hbad).
Qed.

Definition is_hartogs (x alpha : Ens) : Prop :=
  Ord alpha /\ ~ injects alpha x /\
  (forall beta : Ens, Ord beta -> IN beta alpha -> injects beta x).

Theorem Hartogs_Vide : EXType Ens (fun alpha => Ord alpha /\ ~ injects alpha Vide).
Proof.
exists (hartogs Vide).
split.
- apply Ord_hartogs.
- intro H. apply (not_injects_hartogs_Vide H).
Qed.

(* ================================================================= *)
(* Section 4: Initial Ordinals and Cardinal Numbers                 *)
(* ================================================================= *)

Definition is_cardinal (alpha : Ens) : Prop :=
  Ord alpha /\
  (forall beta : Ens, IN beta alpha -> equipotent alpha beta -> False).

Definition is_initial_ordinal := is_cardinal.

Lemma cardinal_Vide : is_cardinal Vide.
Proof.
split.
- apply Ord_Vide.
- intros beta InBeta Heq.
  elim (Vide_est_vide beta InBeta).
Qed.

Lemma cardinal_Succ_Vide : is_cardinal (Succ Vide).
Proof.
split.
- apply Ord_Succ. apply Ord_Vide.
- intros beta InBeta [f [[[Hf_in Hf_ext] Hf_inj] Hf_surj]].
  assert (Hinc_beta : INC beta Vide).
  {
    unfold Succ in InBeta.
    assert (Hin_pow : IN beta (Power Vide)).
    {
      apply (Comp_INC (Power Vide) Ord beta InBeta).
    }
    apply (IN_Power_INC Vide beta Hin_pow).
  }
  assert (Hin_vide_succ : IN Vide (Succ Vide)).
  { apply Succ_incr. apply Ord_Vide. }
  assert (Hin_fvide_beta : IN (f Vide) beta).
  { apply (Hf_in Vide Hin_vide_succ). }
  assert (Hin_fvide_vide : IN (f Vide) Vide).
  { apply (Hinc_beta (f Vide) Hin_fvide_beta). }
  elim (Vide_est_vide (f Vide) Hin_fvide_vide).
Qed.

Definition aleph_0 : Ens := Union Omega_vn.

Lemma Ord_aleph_0 : Ord aleph_0.
Proof.
apply Ord_Union_Omega_vn.
Qed.

(* ================================================================= *)
(* Section 5: Cardinal Arithmetic: Sum and Product                  *)
(* ================================================================= *)

Definition card_sum (kappa lambda : Ens) : Ens :=
  Union (Paire (Prod kappa (Sing Vide)) (Prod lambda (Sing (Succ Vide)))).

Definition card_prod (kappa lambda : Ens) : Ens :=
  Prod kappa lambda.

Lemma not_EQ_Vide_Succ_Vide : EQ Vide (Succ Vide) -> False.
Proof.
intros Heq.
assert (Hin : IN Vide (Succ Vide)).
{ apply Succ_incr. apply Ord_Vide. }
assert (Heq_sym : EQ (Succ Vide) Vide).
{ apply EQ_sym. exact Heq. }
assert (Hbad : IN Vide Vide).
{ apply (IN_sound_right Vide (Succ Vide) Vide Heq_sym Hin). }
elim (Vide_est_vide Vide Hbad).
Qed.

Lemma card_sum_disjoint : forall a b : Ens,
  EQ (Couple a Vide) (Couple b (Succ Vide)) -> False.
Proof.
intros a b Heq.
assert (Heq_tags : EQ Vide (Succ Vide)).
{ apply (Couple_inj_right a Vide b (Succ Vide) Heq). }
exact (not_EQ_Vide_Succ_Vide Heq_tags).
Qed.

Theorem card_sum_inj_left : forall kappa lambda : Ens,
  injects kappa (card_sum kappa lambda).
Proof.
intros kappa lambda.
exists (fun a => Couple a Vide).
split.
- split.
  + intros a Ina.
    unfold card_sum.
    apply IN_Union with (Prod kappa (Sing Vide)).
    * apply IN_Paire_left.
    * apply Couple_IN_Prod.
      -- exact Ina.
      -- apply IN_Sing.
  + intros a b Ina Inb Heq.
    apply Couple_sound_left.
    exact Heq.
- intros a b Ina Inb Heq.
  apply (Couple_inj_left a Vide b Vide Heq).
Qed.

Theorem card_sum_inj_right : forall kappa lambda : Ens,
  injects lambda (card_sum kappa lambda).
Proof.
intros kappa lambda.
exists (fun b => Couple b (Succ Vide)).
split.
- split.
  + intros b Inb.
    unfold card_sum.
    apply IN_Union with (Prod lambda (Sing (Succ Vide))).
    * apply IN_Paire_right.
    * apply Couple_IN_Prod.
      -- exact Inb.
      -- apply IN_Sing.
  + intros a b Ina Inb Heq.
    apply Couple_sound_left.
    exact Heq.
- intros a b Ina Inb Heq.
  apply (Couple_inj_left a (Succ Vide) b (Succ Vide) Heq).
Qed.

Theorem card_prod_inj_left : forall (kappa lambda : Ens) (y : Ens),
  IN y lambda -> injects kappa (card_prod kappa lambda).
Proof.
intros kappa lambda y Iny.
unfold card_prod.
exists (fun a => Couple a y).
split.
- split.
  + intros a Ina.
    apply Couple_IN_Prod; assumption.
  + intros a b Ina Inb Heq.
    apply Couple_sound_left.
    exact Heq.
- intros a b Ina Inb Heq.
  apply (Couple_inj_left a y b y Heq).
Qed.

Theorem card_prod_inj_right : forall (kappa lambda : Ens) (x : Ens),
  IN x kappa -> injects lambda (card_prod kappa lambda).
Proof.
intros kappa lambda x Inx.
unfold card_prod.
exists (fun b => Couple x b).
split.
- split.
  + intros b Inb.
    apply Couple_IN_Prod; assumption.
  + intros a b Ina Inb Heq.
    apply Couple_sound_right.
    exact Heq.
- intros a b Ina Inb Heq.
  apply (Couple_inj_right x a x b Heq).
Qed.

Theorem card_sum_Vide_Vide_empty : forall e : Ens,
  IN e (card_sum Vide Vide) -> False.
Proof.
intros e Hin.
destruct (Union_IN (Paire (Prod Vide (Sing Vide)) (Prod Vide (Sing (Succ Vide)))) e Hin)
  as [E1 [HinE1 HinE1_e]].
destruct (Paire_IN (Prod Vide (Sing Vide)) (Prod Vide (Sing (Succ Vide))) E1 HinE1)
  as [Heq1 | Heq2].
- assert (Hin_prod : IN e (Prod Vide (Sing Vide))).
  { apply (IN_sound_right e E1 (Prod Vide (Sing Vide)) Heq1 HinE1_e). }
  destruct (IN_Prod_EXType Vide (Sing Vide) e Hin_prod) as [a [b Heq_ab]].
  assert (Heq_e_ab : EQ e (Couple a b)).
  { apply EQ_sym. exact Heq_ab. }
  assert (Hin_c : IN (Couple a b) (Prod Vide (Sing Vide))).
  { apply (IN_sound_left e (Couple a b) (Prod Vide (Sing Vide)) Heq_e_ab Hin_prod). }
  destruct (Couple_Prod_IN Vide (Sing Vide) a b Hin_c) as [Ina _].
  elim (Vide_est_vide a Ina).
- assert (Hin_prod : IN e (Prod Vide (Sing (Succ Vide)))).
  { apply (IN_sound_right e E1 (Prod Vide (Sing (Succ Vide))) Heq2 HinE1_e). }
  destruct (IN_Prod_EXType Vide (Sing (Succ Vide)) e Hin_prod) as [a [b Heq_ab]].
  assert (Heq_e_ab : EQ e (Couple a b)).
  { apply EQ_sym. exact Heq_ab. }
  assert (Hin_c : IN (Couple a b) (Prod Vide (Sing (Succ Vide)))).
  { apply (IN_sound_left e (Couple a b) (Prod Vide (Sing (Succ Vide))) Heq_e_ab Hin_prod). }
  destruct (Couple_Prod_IN Vide (Sing (Succ Vide)) a b Hin_c) as [Ina _].
  elim (Vide_est_vide a Ina).
Qed.

Theorem card_sum_Vide_Vide : equipotent (card_sum Vide Vide) Vide.
Proof.
exists (fun a => a).
split.
- split.
  + split.
    * intros a Ina. elim (card_sum_Vide_Vide_empty a Ina).
    * intros a b Ina Inb Heq. exact Heq.
  + intros a b Ina Inb Heq. exact Heq.
- split.
  + split.
    * intros a Ina. elim (card_sum_Vide_Vide_empty a Ina).
    * intros a b Ina Inb Heq. exact Heq.
  + intros b Inb. elim (Vide_est_vide b Inb).
Qed.

Theorem card_prod_Vide_right_empty : forall (kappa : Ens) (e : Ens),
  IN e (card_prod kappa Vide) -> False.
Proof.
intros kappa e Hin.
unfold card_prod in Hin.
destruct (IN_Prod_EXType kappa Vide e Hin) as [a [b Heq_ab]].
assert (Heq_e_ab : EQ e (Couple a b)).
{ apply EQ_sym. exact Heq_ab. }
assert (Hin_c : IN (Couple a b) (Prod kappa Vide)).
{ apply (IN_sound_left e (Couple a b) (Prod kappa Vide) Heq_e_ab Hin). }
destruct (Couple_Prod_IN kappa Vide a b Hin_c) as [_ Inb].
elim (Vide_est_vide b Inb).
Qed.

Theorem card_prod_Vide_right : forall kappa : Ens,
  equipotent (card_prod kappa Vide) Vide.
Proof.
intros kappa.
exists (fun a => a).
split.
- split.
  + split.
    * intros a Ina. elim (card_prod_Vide_right_empty kappa a Ina).
    * intros a b Ina Inb Heq. exact Heq.
  + intros a b Ina Inb Heq. exact Heq.
- split.
  + split.
    * intros a Ina. elim (card_prod_Vide_right_empty kappa a Ina).
    * intros a b Ina Inb Heq. exact Heq.
  + intros b Inb. elim (Vide_est_vide b Inb).
Qed.

Theorem card_prod_Vide_left_empty : forall (lambda : Ens) (e : Ens),
  IN e (card_prod Vide lambda) -> False.
Proof.
intros lambda e Hin.
unfold card_prod in Hin.
destruct (IN_Prod_EXType Vide lambda e Hin) as [a [b Heq_ab]].
assert (Heq_e_ab : EQ e (Couple a b)).
{ apply EQ_sym. exact Heq_ab. }
assert (Hin_c : IN (Couple a b) (Prod Vide lambda)).
{ apply (IN_sound_left e (Couple a b) (Prod Vide lambda) Heq_e_ab Hin). }
destruct (Couple_Prod_IN Vide lambda a b Hin_c) as [Ina _].
elim (Vide_est_vide a Ina).
Qed.

Theorem card_prod_Vide_left : forall lambda : Ens,
  equipotent (card_prod Vide lambda) Vide.
Proof.
intros lambda.
exists (fun a => a).
split.
- split.
  + split.
    * intros a Ina. elim (card_prod_Vide_left_empty lambda a Ina).
    * intros a b Ina Inb Heq. exact Heq.
  + intros a b Ina Inb Heq. exact Heq.
- split.
  + split.
    * intros a Ina. elim (card_prod_Vide_left_empty lambda a Ina).
    * intros a b Ina Inb Heq. exact Heq.
  + intros b Inb. elim (Vide_est_vide b Inb).
Qed.

(* Algebraic laws of cardinal operations up to equinumerosity *)

Definition card_sum_comm_statement : Prop :=
  forall kappa lambda : Ens, equipotent (card_sum kappa lambda) (card_sum lambda kappa).

Definition card_prod_comm_statement : Prop :=
  forall kappa lambda : Ens, equipotent (card_prod kappa lambda) (card_prod lambda kappa).

Definition card_sum_assoc_statement : Prop :=
  forall kappa lambda mu : Ens,
  equipotent (card_sum (card_sum kappa lambda) mu) (card_sum kappa (card_sum lambda mu)).

Definition card_prod_assoc_statement : Prop :=
  forall kappa lambda mu : Ens,
  equipotent (card_prod (card_prod kappa lambda) mu) (card_prod kappa (card_prod lambda mu)).

Definition card_prod_distrib_statement : Prop :=
  forall kappa lambda mu : Ens,
  equipotent (card_prod kappa (card_sum lambda mu))
             (card_sum (card_prod kappa lambda) (card_prod kappa mu)).

(* ================================================================= *)
(* Section 6: Cardinal Absorption Theorem under Axiom of Choice     *)
(* ================================================================= *)

(* Hessenberg's theorem states that for every infinite cardinal kappa, kappa * kappa = kappa *)
Definition Hessenberg_Theorem : Prop :=
  forall kappa : Ens,
  is_cardinal kappa ->
  injects aleph_0 kappa ->
  equipotent (card_prod kappa kappa) kappa.

(* Absorption theorem for infinite cardinals under Choice / Hessenberg: *)
(* If kappa and lambda are infinite cardinals with lambda <= kappa,     *)
(* then kappa + lambda = kappa * lambda = kappa.                         *)
Definition Cardinal_Absorption_Theorem : Prop :=
  forall kappa lambda : Ens,
  is_cardinal kappa ->
  is_cardinal lambda ->
  injects aleph_0 kappa ->
  injects lambda kappa ->
  equipotent (card_sum kappa lambda) kappa /\
  equipotent (card_prod kappa lambda) kappa.

(* Hessenberg implies Absorption *)
Definition Hessenberg_implies_Absorption : Prop :=
  Hessenberg_Theorem -> Cardinal_Absorption_Theorem.

(* Formalization of Absorption under the Axiom of Choice *)
Definition Choice_implies_Absorption : Prop :=
  Axiom_of_Choice_fun -> Cardinal_Absorption_Theorem.

