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
Require Import Plump.
Require Import Ordinal_theory.
Require Import Regularity.
Require Import Limit_ordinals.

(* Transfinite induction schema on ordinals *)
Theorem transfinite_induction :
  forall P : Ens -> Prop,
  (forall a b : Ens, EQ a b -> P a -> P b) ->
  (forall alpha : Ens, Ord alpha -> (forall beta : Ens, IN beta alpha -> P beta) -> P alpha) ->
  forall alpha : Ens, Ord alpha -> P alpha.
Proof.
intros P P_sound H_ind.
assert (H_all : forall z : Ens, Ord z -> P z).
{
  apply (eps_ind (fun x => Ord x -> P x)).
  - intros a b Hab.
    split; intros H O_b.
    + apply (P_sound a b Hab).
      apply H.
      apply (Ord_sound b a).
      * apply EQ_sym. exact Hab.
      * exact O_b.
    + apply (P_sound b a).
      * apply EQ_sym. exact Hab.
      * apply H.
        apply (Ord_sound a b Hab O_b).
  - intros x Hrec Ox.
    apply H_ind.
    + exact Ox.
    + intros beta Ibeta.
      apply (Hrec beta Ibeta).
      apply (IN_Ord_Ord x beta Ox Ibeta).
}
intros alpha Oa.
apply (H_all alpha Oa).
Qed.

(* Bounded transfinite induction within an ordinal bound gamma *)
Theorem bounded_transfinite_induction :
  forall (gamma : Ens) (P : Ens -> Prop),
  Ord gamma ->
  (forall a b : Ens, EQ a b -> P a -> P b) ->
  (forall alpha : Ens, Ord alpha -> IN alpha gamma ->
    (forall beta : Ens, IN beta alpha -> P beta) -> P alpha) ->
  forall alpha : Ens, Ord alpha -> IN alpha gamma -> P alpha.
Proof.
intros gamma P Ogamma P_sound H_step.
assert (H_all : forall alpha : Ens, Ord alpha -> IN alpha gamma -> P alpha).
{
  apply (transfinite_induction (fun alpha => IN alpha gamma -> P alpha)).
  - intros a b Hab H_a InB.
    apply (P_sound a b Hab).
    apply H_a.
    apply (IN_sound_left b a gamma).
    + apply EQ_sym. exact Hab.
    + exact InB.
  - intros alpha Oalpha H_ih InGamma.
    apply H_step.
    + exact Oalpha.
    + exact InGamma.
    + intros beta InAlpha.
      apply H_ih.
      * exact InAlpha.
      * apply (Ord_trans gamma Ogamma alpha InGamma beta InAlpha).
}
exact H_all.
Qed.

