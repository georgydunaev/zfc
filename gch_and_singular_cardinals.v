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

(* Formalization of the Generalized Continuum Hypothesis (GCH),       *)
(* Hausdorff Formula, Bernstein Formula, Silver's Theorem on          *)
(* Singular Cardinals, and Easton's Theorem in ZFC Set Theory.        *)

Require Import Sets.
Require Import Axioms.
Require Import Cartesian.
Require Import Plump.
Require Import Ordinal_theory.
Require Import Ordinal_succession.
Require Import Limit_ordinals.
Require Import Choice.
Require Import Cardinal.
Require Import cardinal_exponentiation.

(* ================================================================= *)
(* Section 1: Ordinals and the Aleph Function Hierarchy              *)
(* ================================================================= *)

Definition is_ordinal (alpha : Ens) : Prop := Ord alpha.

Lemma is_ordinal_sound : forall a b : Ens,
  EQ a b -> is_ordinal a -> is_ordinal b.
Proof.
intros a b Heq Hord.
apply (Ord_sound a b Heq Hord).
Qed.

Lemma is_ordinal_Vide : is_ordinal Vide.
Proof.
apply Ord_Vide.
Qed.

Lemma is_ordinal_Succ : forall alpha : Ens,
  is_ordinal alpha -> is_ordinal (Succ alpha).
Proof.
intros alpha Hord.
apply Ord_Succ.
exact Hord.
Qed.

(* Postulated Aleph function mapping each ordinal to its initial ordinal *)
Parameter aleph : Ens -> Ens.

Parameter aleph_Ord : forall alpha : Ens,
  is_ordinal alpha -> is_ordinal (aleph alpha).

Parameter aleph_is_cardinal : forall alpha : Ens,
  is_ordinal alpha -> is_cardinal (aleph alpha).

Parameter aleph_increasing : forall alpha beta : Ens,
  is_ordinal alpha -> is_ordinal beta ->
  IN alpha beta -> strictly_smaller (aleph alpha) (aleph beta).

(* ================================================================= *)
(* Section 2: Generalized Continuum Hypothesis (GCH) and Weak GCH    *)
(* ================================================================= *)

Definition GCH_statement : Prop :=
  forall alpha : Ens,
  is_ordinal alpha ->
  equipotent (Power (aleph alpha)) (aleph (Succ alpha)).

Definition Weak_GCH_statement : Prop :=
  forall alpha : Ens,
  is_ordinal alpha ->
  strictly_smaller (Power (aleph alpha)) (Power (aleph (Succ alpha))).

Theorem strictly_smaller_equipotent_left : forall x y z : Ens,
  equipotent x y ->
  strictly_smaller y z ->
  strictly_smaller x z.
Proof.
intros x y z Heq_xy [Hinj_yz Hnot_zy].
split.
- apply injects_trans with y.
  + apply equipotent_injects. exact Heq_xy.
  + exact Hinj_yz.
- intro Hinj_zx.
  apply Hnot_zy.
  apply injects_trans with x.
  + exact Hinj_zx.
  + apply equipotent_injects. exact Heq_xy.
Qed.

Theorem GCH_implies_Weak_GCH :
  GCH_statement -> Weak_GCH_statement.
Proof.
intros Hgch alpha Hord.
assert (Heq : equipotent (Power (aleph alpha)) (aleph (Succ alpha))).
{ apply (Hgch alpha Hord). }
apply (strictly_smaller_equipotent_left (Power (aleph alpha)) (aleph (Succ alpha)) (Power (aleph (Succ alpha))) Heq).
apply Cantor_strict.
Qed.

Theorem GCH_strict_step : forall alpha : Ens,
  GCH_statement ->
  is_ordinal alpha ->
  strictly_smaller (aleph alpha) (aleph (Succ alpha)).
Proof.
intros alpha Hgch Hord.
assert (Heq : equipotent (Power (aleph alpha)) (aleph (Succ alpha))).
{ apply (Hgch alpha Hord). }
apply (strictly_smaller_equipotent_right (aleph alpha) (Power (aleph alpha)) (aleph (Succ alpha))).
- apply Cantor_strict.
- exact Heq.
Qed.

(* ================================================================= *)
(* Section 3: Hausdorff Formula and Bernstein Formula                *)
(* ================================================================= *)

Definition Hausdorff_formula_statement : Prop :=
  forall alpha beta : Ens,
  is_ordinal alpha ->
  is_ordinal beta ->
  equipotent (card_exp (aleph (Succ alpha)) (aleph beta))
             (card_prod (card_exp (aleph alpha) (aleph beta)) (aleph (Succ alpha))).

Definition Bernstein_formula_statement : Prop :=
  forall n beta : Ens,
  IN n aleph_0 ->
  is_ordinal beta ->
  equipotent (card_exp (aleph n) (aleph beta))
             (card_prod (Power (aleph beta)) (aleph n)).

(* ================================================================= *)
(* Section 4: Silver's Theorem on Singular Cardinals                 *)
(* ================================================================= *)

Definition Silvers_Theorem_statement : Prop :=
  forall lambda beta : Ens,
  is_ordinal lambda ->
  is_limit_ord lambda ->
  is_cofinality beta lambda ->
  strictly_smaller aleph_0 beta ->
  (forall alpha : Ens, IN alpha lambda -> is_ordinal alpha ->
    equipotent (Power (aleph alpha)) (aleph (Succ alpha))) ->
  equipotent (Power (aleph lambda)) (aleph (Succ lambda)).

Definition Silvers_Hypothesis (lambda beta : Ens) : Prop :=
  is_ordinal lambda /\
  is_limit_ord lambda /\
  is_cofinality beta lambda /\
  strictly_smaller aleph_0 beta.

Theorem Silvers_Theorem_conditional :
  Silvers_Theorem_statement ->
  forall lambda beta : Ens,
  Silvers_Hypothesis lambda beta ->
  (forall alpha : Ens, IN alpha lambda -> is_ordinal alpha ->
    equipotent (Power (aleph alpha)) (aleph (Succ alpha))) ->
  equipotent (Power (aleph lambda)) (aleph (Succ lambda)).
Proof.
intros Hsilver lambda beta [Hord [Hlim [Hcof Hunc]]] Hgch_below.
apply (Hsilver lambda beta Hord Hlim Hcof Hunc Hgch_below).
Qed.

(* ================================================================= *)
(* Section 5: Easton's Function and Easton's Theorem                 *)
(* ================================================================= *)

Definition is_easton_function (F : Ens -> Ens) : Prop :=
  (forall kappa : Ens, is_regular_cardinal kappa -> is_cardinal (F kappa)) /\
  (forall kappa lambda : Ens,
    is_regular_cardinal kappa -> is_regular_cardinal lambda ->
    injects kappa lambda -> injects (F kappa) (F lambda)) /\
  (forall kappa beta : Ens,
    is_regular_cardinal kappa ->
    is_cofinality beta (F kappa) ->
    strictly_smaller kappa beta).

Definition Eastons_Theorem_statement : Prop :=
  forall F : Ens -> Ens,
  is_easton_function F ->
  forall kappa : Ens,
  is_regular_cardinal kappa ->
  equipotent (Power kappa) (F kappa).

(* ================================================================= *)
(* Section 6: Exponentiation Laws for Regular Cardinals under GCH     *)
(* ================================================================= *)

Definition GCH_regular_exp_smaller (kappa lambda : Ens) : Prop :=
  is_regular_cardinal kappa ->
  is_regular_cardinal lambda ->
  strictly_smaller lambda kappa ->
  equipotent (card_exp kappa lambda) kappa.

Definition GCH_regular_exp_le (kappa lambda succ_lambda : Ens) : Prop :=
  is_regular_cardinal kappa ->
  is_regular_cardinal lambda ->
  injects kappa lambda ->
  equipotent (Power lambda) succ_lambda ->
  equipotent (card_exp kappa lambda) succ_lambda.

Definition GCH_regular_exp_same (kappa succ_kappa : Ens) : Prop :=
  is_regular_cardinal kappa ->
  equipotent (Power kappa) succ_kappa ->
  equipotent (card_exp kappa kappa) succ_kappa.

Theorem GCH_same_from_le : forall kappa succ_kappa : Ens,
  (forall k l s : Ens, GCH_regular_exp_le k l s) ->
  GCH_regular_exp_same kappa succ_kappa.
Proof.
intros kappa succ_kappa Hle Hreg Hpow.
apply (Hle kappa kappa succ_kappa Hreg Hreg (injects_refl kappa) Hpow).
Qed.

Definition GCH_regular_exponentiation_law : Prop :=
  forall kappa lambda succ_lambda : Ens,
  is_regular_cardinal kappa ->
  is_regular_cardinal lambda ->
  equipotent (Power lambda) succ_lambda ->
  ((strictly_smaller lambda kappa -> equipotent (card_exp kappa lambda) kappa) /\
   (injects kappa lambda -> equipotent (card_exp kappa lambda) succ_lambda)).

Theorem GCH_regular_law_implies_smaller :
  GCH_regular_exponentiation_law ->
  forall kappa lambda : Ens,
  GCH_regular_exp_smaller kappa lambda.
Proof.
intros Hlaw kappa lambda Hreg_k Hreg_l Hlt.
destruct (Hlaw kappa lambda (Power lambda) Hreg_k Hreg_l (equipotent_refl (Power lambda))) as [Hsm _].
apply (Hsm Hlt).
Qed.

Theorem GCH_regular_law_implies_le :
  GCH_regular_exponentiation_law ->
  forall kappa lambda succ_lambda : Ens,
  GCH_regular_exp_le kappa lambda succ_lambda.
Proof.
intros Hlaw kappa lambda succ_lambda Hreg_k Hreg_l Hinj Hpow.
destruct (Hlaw kappa lambda succ_lambda Hreg_k Hreg_l Hpow) as [_ Hle].
apply (Hle Hinj).
Qed.

Theorem GCH_regular_law_implies_same :
  GCH_regular_exponentiation_law ->
  forall kappa succ_kappa : Ens,
  GCH_regular_exp_same kappa succ_kappa.
Proof.
intros Hlaw kappa succ_kappa Hreg Hpow.
apply GCH_same_from_le.
- apply (GCH_regular_law_implies_le Hlaw).
- exact Hreg.
- exact Hpow.
Qed.
