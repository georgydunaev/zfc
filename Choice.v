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

(* Contribution to the Coq Library                                    *)

Require Import Sets.
Require Import Axioms.
Require Import Cartesian.
Require Import Replacement.

(* Set-theoretic non-emptiness predicate *)
Definition non_empty (E : Ens) : Prop :=
  EXType Ens (fun x => IN x E).

(* Functional choice formulation on a family E *)
Definition is_choice_function (f : Ens -> Ens) (E : Ens) : Prop :=
  forall x : Ens, IN x E -> IN (f x) x.

(* The Axiom of Choice (functional version) *)
Definition Axiom_of_Choice_fun : Prop :=
  forall E : Ens,
  (forall x : Ens, IN x E -> non_empty x) ->
  EXType (Ens -> Ens) (fun f => is_choice_function f E).

(* Graph of choice function restricted to an indexing set *)
Definition is_choice_graph (G : Ens) (E : Ens) : Prop :=
  forall x : Ens, IN x E -> EXType Ens (fun y => IN y x /\ IN (Couple x y) G).

(* Constructive derivation: Type-theoretic choice produces a choice graph *)
Theorem type_choice_graph :
  choice ->
  forall (A : Type) (f : A -> Ens),
  (forall a : A, non_empty (f a)) ->
  EXType Ens (fun G =>
    forall a : A, EXType Ens (fun y => IN y (f a) /\ IN (Couple (f a) y) G)).
Proof.
intros Hch A f Hne.
unfold non_empty in Hne.
destruct (Hch A Ens (fun a y => IN y (f a)) Hne) as [ch Hch_prop].
exists (sup A (fun a => Couple (f a) (ch a))).
intros a.
exists (ch a).
split.
- apply Hch_prop.
- exists a. apply EQ_refl.
Qed.

(* Well-ordering structure on a set E *)
Definition is_well_order (E : Ens) (R : Ens -> Ens -> Prop) : Prop :=
  (* Irreflexive *)
  (forall x : Ens, IN x E -> R x x -> False) /\
  (* Transitive *)
  (forall x y z : Ens, IN x E -> IN y E -> IN z E -> R x y -> R y z -> R x z) /\
  (* Connected (trichotomy) *)
  (forall x y : Ens, IN x E -> IN y E -> R x y \/ EQ x y \/ R y x) /\
  (* Well-founded: every non-empty subset has a minimal element *)
  (forall S : Ens, INC S E -> non_empty S ->
    EXType Ens (fun m => IN m S /\ forall y : Ens, IN y S -> R y m -> False)).

(* Zermelo Well-Ordering Theorem statement *)
Definition Well_Ordering_Theorem : Prop :=
  forall E : Ens, EXType (Ens -> Ens -> Prop) (fun R => is_well_order E R).
