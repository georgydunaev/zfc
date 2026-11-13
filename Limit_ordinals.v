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

(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

Require Import Sets.
Require Import Axioms.
Require Import Omega.
Require Import Plump.
Require Import Ordinal_theory.

Definition is_limit_ord (L : Ens) : Prop :=
  Ord L /\ ~ EQ L Vide /\ (forall E : Ens, IN E L -> IN (Succ E) L).

Lemma Ord_Vide : Ord Vide.
Proof.
unfold Ord, Vide.
simpl.
split; intros [].
Qed.

Fixpoint vn_nat (n : nat) : Ens :=
  match n with
  | 0%nat => Vide
  | S p => Succ (vn_nat p)
  end.

Lemma vn_nat_Ord : forall n : nat, Ord (vn_nat n).
Proof.
induction n.
- simpl. apply Ord_Vide.
- simpl. apply Ord_Succ. exact IHn.
Qed.

Definition Omega_vn : Ens := sup nat vn_nat.

Lemma IN_Omega_vn : forall n : nat, IN (vn_nat n) Omega_vn.
Proof.
intros n.
simpl.
exists n.
apply EQ_refl.
Qed.

Lemma Ord_Union_Omega_vn : Ord (Union Omega_vn).
Proof.
apply Union_Ord.
intros E' InE.
simpl in InE.
destruct InE as [n Hn].
apply Ord_sound with (vn_nat n).
- apply EQ_sym. exact Hn.
- apply vn_nat_Ord.
Qed.

Lemma IN_Union_Omega_vn : forall n : nat, IN (vn_nat n) (Union Omega_vn).
Proof.
intros n.
apply IN_Union with (vn_nat (S n)).
- apply IN_Omega_vn.
- simpl. apply Succ_incr. apply vn_nat_Ord.
Qed.

Lemma not_EQ_Union_Omega_vn_Vide : ~ EQ (Union Omega_vn) Vide.
Proof.
intro H.
assert (H0 : IN Vide (Union Omega_vn)).
{
  apply IN_sound_left with (vn_nat 0%nat).
  - simpl. split; intros [].
  - apply IN_Union_Omega_vn.
}
assert (Hvide : IN Vide Vide).
{
  apply IN_sound_right with (Union Omega_vn); assumption.
}
elim (Vide_est_vide Vide Hvide).
Qed.

Lemma Union_INC_Ord :
  forall L : Ens, Ord L -> INC (Union L) L.
Proof.
intros L OL.
unfold INC.
intros x Hx.
elim (Union_IN L x Hx).
intros E [H1 H2].
apply (Ord_trans L OL E H1 x H2).
Qed.

Lemma Limit_Union_EQ :
  forall L : Ens,
  Ord L ->
  (forall E : Ens, IN E L -> IN (Succ E) L) ->
  EQ (Union L) L.
Proof.
intros L OL Hsucc.
apply INC_EQ.
- apply (Union_INC_Ord L OL).
- unfold INC.
  intros E InL.
  apply IN_Union with (Succ E).
  + apply Hsucc. exact InL.
  + apply Succ_incr.
    apply (IN_Ord_Ord L E OL InL).
Qed.

Hint Resolve Ord_Vide vn_nat_Ord IN_Omega_vn Ord_Union_Omega_vn IN_Union_Omega_vn not_EQ_Union_Omega_vn_Vide : zfc.
