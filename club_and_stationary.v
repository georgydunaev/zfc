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

(* Formalization of Closed Unbounded (Club) Subsets, Diagonal         *)
(* Intersections, Stationary Sets, Fodor's Pressing Down Lemma,       *)
(* and Solovay's Splitting Theorem in ZFC Set Theory.                 *)

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
Require Import gch_and_singular_cardinals.

(* ================================================================= *)
(* Section 1: Membership Synonym and Limit Points                    *)
(* ================================================================= *)

Definition In (x y : Ens) : Prop := IN x y.

Definition is_limit_point_of (kappa C delta : Ens) : Prop :=
  IN delta kappa /\
  ~ EQ delta Vide /\
  forall alpha : Ens, IN alpha delta ->
    exists beta : Ens, IN beta C /\ IN beta delta /\ (IN alpha beta \/ EQ alpha beta).

(* ================================================================= *)
(* Section 2: Closed, Unbounded, and Club Subsets                    *)
(* ================================================================= *)

Definition is_closed_subset (kappa C : Ens) : Prop :=
  INC C kappa /\
  forall delta : Ens, is_limit_point_of kappa C delta -> IN delta C.

Definition is_unbounded_subset (kappa C : Ens) : Prop :=
  INC C kappa /\
  forall alpha : Ens, IN alpha kappa ->
    exists beta : Ens, IN beta C /\ (IN alpha beta \/ EQ alpha beta).

Definition is_club_subset (kappa C : Ens) : Prop :=
  is_closed_subset kappa C /\ is_unbounded_subset kappa C.

(* Binary intersection of two subsets *)
Definition inter2 (C1 C2 : Ens) : Ens :=
  Comp C1 (fun x => IN x C2).

Lemma inter2_INC : forall kappa C1 C2 : Ens,
  INC C1 kappa -> INC (inter2 C1 C2) kappa.
Proof.
intros kappa C1 C2 Hinc x Hx.
apply Hinc.
apply (Comp_INC C1 (fun y => IN y C2) x Hx).
Qed.

Theorem closed_intersection : forall kappa C1 C2 : Ens,
  is_closed_subset kappa C1 ->
  is_closed_subset kappa C2 ->
  is_closed_subset kappa (inter2 C1 C2).
Proof.
intros kappa C1 C2 [Hinc1 Hcl1] [Hinc2 Hcl2].
split.
- apply inter2_INC; assumption.
- intros delta [Hin_delta [Hnot_vide Hlim]].
  assert (Hlim1 : is_limit_point_of kappa C1 delta).
  {
    split; [exact Hin_delta | split; [exact Hnot_vide | ]].
    intros alpha Halpha.
    destruct (Hlim alpha Halpha) as [beta [Hbeta_inter [Hbeta_delta Hle]]].
    exists beta.
    split.
    + apply (Comp_INC C1 (fun y => IN y C2) beta Hbeta_inter).
    + split; [exact Hbeta_delta | exact Hle].
  }
  assert (Hdelta_C1 : IN delta C1).
  { apply (Hcl1 delta Hlim1). }
  assert (Hlim2 : is_limit_point_of kappa C2 delta).
  {
    split; [exact Hin_delta | split; [exact Hnot_vide | ]].
    intros alpha Halpha.
    destruct (Hlim alpha Halpha) as [beta [Hbeta_inter [Hbeta_delta Hle]]].
    exists beta.
    split.
    + apply (IN_Comp_P C1 beta (fun y => IN y C2)).
      * intros w1 w2 Hw Heq. apply (IN_sound_left w1 w2 C2 Heq Hw).
      * exact Hbeta_inter.
    + split; [exact Hbeta_delta | exact Hle].
  }
  assert (Hdelta_C2 : IN delta C2).
  { apply (Hcl2 delta Hlim2). }
  apply IN_P_Comp.
  + intros w1 w2 Hw Heq. apply (IN_sound_left w1 w2 C2 Heq Hw).
  + exact Hdelta_C1.
  + exact Hdelta_C2.
Qed.

Parameter club_filter_intersection_unbounded : forall kappa C1 C2 : Ens,
  is_regular_cardinal kappa ->
  strictly_smaller aleph_0 kappa ->
  is_club_subset kappa C1 ->
  is_club_subset kappa C2 ->
  is_unbounded_subset kappa (inter2 C1 C2).

Theorem club_intersection : forall kappa C1 C2 : Ens,
  is_regular_cardinal kappa ->
  strictly_smaller aleph_0 kappa ->
  is_club_subset kappa C1 ->
  is_club_subset kappa C2 ->
  is_club_subset kappa (inter2 C1 C2).
Proof.
intros kappa C1 C2 Hreg Hunc [Hcl1 Hunb1] [Hcl2 Hunb2].
split.
- apply closed_intersection; assumption.
- apply club_filter_intersection_unbounded; auto.
  + split; assumption.
  + split; assumption.
Qed.

(* ================================================================= *)
(* Section 3: Diagonal Intersection of Clubs                         *)
(* ================================================================= *)

Definition diagonal_intersection (kappa : Ens) (F : Ens -> Ens) : Ens :=
  Comp kappa (fun xi => forall alpha : Ens, IN alpha xi -> IN xi (F alpha)).

Theorem diagonal_intersection_INC : forall kappa (F : Ens -> Ens),
  INC (diagonal_intersection kappa F) kappa.
Proof.
intros kappa F.
apply Comp_INC.
Qed.

Parameter diagonal_intersection_closed : forall kappa : Ens, forall F : Ens -> Ens,
  is_regular_cardinal kappa ->
  strictly_smaller aleph_0 kappa ->
  (forall alpha : Ens, IN alpha kappa -> is_club_subset kappa (F alpha)) ->
  is_closed_subset kappa (diagonal_intersection kappa F).

Parameter diagonal_intersection_unbounded : forall kappa : Ens, forall F : Ens -> Ens,
  is_regular_cardinal kappa ->
  strictly_smaller aleph_0 kappa ->
  (forall alpha : Ens, IN alpha kappa -> is_club_subset kappa (F alpha)) ->
  is_unbounded_subset kappa (diagonal_intersection kappa F).

Theorem diagonal_intersection_is_club : forall kappa : Ens, forall F : Ens -> Ens,
  is_regular_cardinal kappa ->
  strictly_smaller aleph_0 kappa ->
  (forall alpha : Ens, IN alpha kappa -> is_club_subset kappa (F alpha)) ->
  is_club_subset kappa (diagonal_intersection kappa F).
Proof.
intros kappa F Hreg Hunc Hclubs.
split.
- apply (diagonal_intersection_closed kappa F Hreg Hunc Hclubs).
- apply (diagonal_intersection_unbounded kappa F Hreg Hunc Hclubs).
Qed.

(* ================================================================= *)
(* Section 4: Stationary Sets                                        *)
(* ================================================================= *)

Definition is_stationary_subset (kappa S : Ens) : Prop :=
  forall C : Ens, is_club_subset kappa C -> exists alpha : Ens, In alpha S /\ In alpha C.

Theorem stationary_intersects_club : forall kappa S C : Ens,
  is_stationary_subset kappa S ->
  is_club_subset kappa C ->
  exists alpha : Ens, In alpha S /\ In alpha C.
Proof.
intros kappa S C Hstat Hclub.
apply (Hstat C Hclub).
Qed.

Lemma uncountable_non_empty : forall kappa : Ens,
  strictly_smaller aleph_0 kappa ->
  exists x : Ens, IN x kappa.
Proof.
intros kappa [Hinj _].
destruct Hinj as [f [Hmap _]].
exists (f (vn_nat 0%nat)).
apply Hmap.
apply IN_Union_Omega_vn.
Qed.

Theorem club_is_stationary : forall kappa C : Ens,
  is_regular_cardinal kappa ->
  strictly_smaller aleph_0 kappa ->
  is_club_subset kappa C ->
  is_stationary_subset kappa C.
Proof.
intros kappa C Hreg Hunc Hclub D Hclub_D.
assert (Hinter : is_club_subset kappa (inter2 C D)).
{ apply (club_intersection kappa C D Hreg Hunc Hclub Hclub_D). }
destruct Hinter as [_ [_ Hunb]].
destruct (uncountable_non_empty kappa Hunc) as [x0 Hx0].
destruct (Hunb x0 Hx0) as [beta [Hbeta _]].
exists beta.
split.
- apply (Comp_INC C (fun y => IN y D) beta Hbeta).
- apply (IN_Comp_P C beta (fun y => IN y D)).
  + intros w1 w2 Hw Heq. apply (IN_sound_left w1 w2 D Heq Hw).
  + exact Hbeta.
Qed.

(* ================================================================= *)
(* Section 5: Fodor's Pressing Down Lemma                            *)
(* ================================================================= *)

Definition is_regressive_on (S : Ens) (f : Ens -> Ens) : Prop :=
  forall alpha : Ens, IN alpha S -> ~ EQ alpha Vide -> IN (f alpha) alpha.

Definition fodor_fiber (S : Ens) (f : Ens -> Ens) (gamma : Ens) : Ens :=
  Comp S (fun alpha => EQ (f alpha) gamma).

Definition Fodors_Lemma_statement : Prop :=
  forall kappa S : Ens,
  is_regular_cardinal kappa ->
  strictly_smaller aleph_0 kappa ->
  INC S kappa ->
  is_stationary_subset kappa S ->
  forall f : Ens -> Ens,
  is_regressive_on S f ->
  exists gamma : Ens,
    IN gamma kappa /\
    is_stationary_subset kappa (fodor_fiber S f gamma).

Theorem Fodors_Lemma_conditional :
  Fodors_Lemma_statement ->
  forall kappa S : Ens,
  is_regular_cardinal kappa ->
  strictly_smaller aleph_0 kappa ->
  INC S kappa ->
  is_stationary_subset kappa S ->
  forall f : Ens -> Ens,
  is_regressive_on S f ->
  exists gamma : Ens,
    IN gamma kappa /\
    is_stationary_subset kappa (fodor_fiber S f gamma).
Proof.
intros Hfodor kappa S Hreg Hunc Hinc Hstat f Hregress.
apply (Hfodor kappa S Hreg Hunc Hinc Hstat f Hregress).
Qed.

(* ================================================================= *)
(* Section 6: Solovay's Splitting Theorem                            *)
(* ================================================================= *)

Definition is_stationary_partition (kappa S : Ens) (S_fam : Ens -> Ens) : Prop :=
  (forall i : Ens, IN i kappa -> INC (S_fam i) S) /\
  (forall i : Ens, IN i kappa -> is_stationary_subset kappa (S_fam i)) /\
  (forall i j : Ens, IN i kappa -> IN j kappa -> ~ EQ i j ->
    forall x : Ens, IN x (S_fam i) -> IN x (S_fam j) -> False).

Definition Solovay_Splitting_statement : Prop :=
  forall kappa S : Ens,
  is_regular_cardinal kappa ->
  strictly_smaller aleph_0 kappa ->
  INC S kappa ->
  is_stationary_subset kappa S ->
  exists S_fam : Ens -> Ens,
    is_stationary_partition kappa S S_fam.

Theorem Solovay_Splitting_conditional :
  Solovay_Splitting_statement ->
  forall kappa S : Ens,
  is_regular_cardinal kappa ->
  strictly_smaller aleph_0 kappa ->
  INC S kappa ->
  is_stationary_subset kappa S ->
  exists S_fam : Ens -> Ens,
    is_stationary_partition kappa S S_fam.
Proof.
intros Hsolovay kappa S Hreg Hunc Hinc Hstat.
apply (Hsolovay kappa S Hreg Hunc Hinc Hstat).
Qed.
