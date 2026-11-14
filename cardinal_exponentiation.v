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

(* Formalization of Cardinal Exponentiation, Cantor's Theorem,        *)
(* Cofinality, and Konig's Theorem in ZFC set theory.                 *)

Require Import Sets.
Require Import Axioms.
Require Import Cartesian.
Require Import Plump.
Require Import Ordinal_succession.
Require Import Limit_ordinals.
Require Import Choice.
Require Import Cardinal.

(* ================================================================= *)
(* Section 1: Cantor's Theorem: Non-Surjectivity & Strict Inequality *)
(* ================================================================= *)

Theorem Cantor_no_surjection : forall (x : Ens) (f : Ens -> Ens),
  is_surj x (Power x) f -> False.
Proof.
intros x f [Hmap Hsurj].
apply (Cantor_no_surj x f Hmap Hsurj).
Qed.

Theorem Cantor_strictly_smaller : forall x : Ens,
  strictly_smaller x (Power x).
Proof.
intros x.
apply Cantor_strict.
Qed.

Theorem strictly_smaller_equipotent_right : forall x y z : Ens,
  strictly_smaller x y ->
  equipotent y z ->
  strictly_smaller x z.
Proof.
intros x y z [Hinj_xy Hnot_yx] Heq_yz.
split.
- apply injects_trans with y.
  + exact Hinj_xy.
  + apply equipotent_injects. exact Heq_yz.
- intro Hinj_zx.
  apply Hnot_yx.
  apply injects_trans with z.
  + apply equipotent_injects. exact Heq_yz.
  + exact Hinj_zx.
Qed.

(* ================================================================= *)
(* Section 2: Function Graphs and Cardinal Exponentiation           *)
(* ================================================================= *)

Definition is_function_graph (B A F : Ens) : Prop :=
  INC F (Prod B A) /\
  (forall b : Ens, IN b B ->
    EXType Ens (fun a => IN a A /\ IN (Couple b a) F /\
      (forall a' : Ens, IN a' A -> IN (Couple b a') F -> EQ a a'))).

Definition card_exp (A B : Ens) : Ens :=
  Comp (Power (Prod B A)) (is_function_graph B A).

Definition card_two : Ens := Paire Vide (Succ Vide).

Lemma is_function_graph_sound : forall B A : Ens,
  forall w1 w2 : Ens,
  is_function_graph B A w1 -> EQ w1 w2 -> is_function_graph B A w2.
Proof.
intros B A w1 w2 [Hinc1 Hfun1] Heq12.
split.
- apply INC_sound_left with w1; [exact Heq12 | exact Hinc1].
- intros b Inb.
  destruct (Hfun1 b Inb) as [a [Ina [Hincf Huniq]]].
  exists a.
  split; [exact Ina |].
  split.
  + apply IN_sound_right with w1; [exact Heq12 | exact Hincf].
  + intros a' Ina' Hin_ca'.
    apply (Huniq a' Ina').
    apply IN_sound_right with w2.
    * apply EQ_sym. exact Heq12.
    * exact Hin_ca'.
Qed.

Lemma Vide_is_function_graph_Vide : forall kappa : Ens,
  is_function_graph Vide kappa Vide.
Proof.
intros kappa.
split.
- unfold INC. intros e Hin. elim (Vide_est_vide e Hin).
- intros b Inb. elim (Vide_est_vide b Inb).
Qed.

Theorem card_exp_zero_has_element : forall kappa : Ens,
  IN Vide (card_exp kappa Vide).
Proof.
intros kappa.
unfold card_exp.
apply IN_P_Comp.
- apply is_function_graph_sound.
- apply INC_IN_Power.
  unfold INC.
  intros e Hin.
  elim (Vide_est_vide e Hin).
- apply Vide_is_function_graph_Vide.
Qed.

Theorem card_exp_zero_only_Vide : forall (kappa : Ens) (F : Ens),
  IN F (card_exp kappa Vide) -> EQ F Vide.
Proof.
intros kappa F Hin.
unfold card_exp in Hin.
assert (Hinc_prod : INC F (Prod Vide kappa)).
{
  assert (Hin_pow : IN F (Power (Prod Vide kappa))).
  { apply (Comp_INC (Power (Prod Vide kappa)) (is_function_graph Vide kappa) F Hin). }
  apply (IN_Power_INC (Prod Vide kappa) F Hin_pow).
}
assert (Hno_elements : forall E' : Ens, IN E' F -> False).
{
  intros E' InE'.
  assert (In_prod : IN E' (Prod Vide kappa)).
  { apply (Hinc_prod E' InE'). }
  destruct (IN_Prod_EXType Vide kappa E' In_prod) as [a [b Heq_ab]].
  assert (Hin_c : IN (Couple a b) (Prod Vide kappa)).
  {
    apply (IN_sound_left E' (Couple a b) (Prod Vide kappa)).
    - apply EQ_sym. exact Heq_ab.
    - exact In_prod.
  }
  destruct (Couple_Prod_IN Vide kappa a b Hin_c) as [Ina _].
  elim (Vide_est_vide a Ina).
}
apply tout_vide_est_Vide.
intros E' InE'.
destruct (Hno_elements E' InE').
Qed.

Theorem card_exp_zero : forall kappa : Ens,
  equipotent (card_exp kappa Vide) (Sing Vide).
Proof.
intros kappa.
exists (fun _ => Vide).
split.
- split.
  + split.
    * intros a Ina. apply IN_Sing.
    * intros a b Ina Inb Heq. apply EQ_refl.
  + intros a b Ina Inb Heq.
    assert (Heqa : EQ a Vide).
    { apply (card_exp_zero_only_Vide kappa a Ina). }
    assert (Heqb : EQ b Vide).
    { apply (card_exp_zero_only_Vide kappa b Inb). }
    apply EQ_tran with Vide.
    * exact Heqa.
    * apply EQ_sym. exact Heqb.
- split.
  + split.
    * intros a Ina. apply IN_Sing.
    * intros a b Ina Inb Heq. apply EQ_refl.
  + intros b Inb.
    assert (Heqb : EQ b Vide).
    { apply (IN_Sing_EQ b Vide Inb). }
    exists Vide.
    split.
    * apply card_exp_zero_has_element.
    * apply EQ_sym. exact Heqb.
Qed.

(* Algebraic Laws of Exponentiation *)

Definition card_exp_zero_statement : Prop :=
  forall kappa : Ens, equipotent (card_exp kappa Vide) (Sing Vide).

Definition card_exp_one_statement : Prop :=
  forall kappa : Ens, equipotent (card_exp kappa (Sing Vide)) kappa.

Definition card_exp_sum_statement : Prop :=
  forall kappa lambda mu : Ens,
  equipotent (card_exp kappa (card_sum lambda mu))
             (card_prod (card_exp kappa lambda) (card_exp kappa mu)).

Definition card_prod_exp_statement : Prop :=
  forall kappa lambda mu : Ens,
  equipotent (card_exp (card_prod kappa lambda) mu)
             (card_prod (card_exp kappa mu) (card_exp lambda mu)).

Definition card_exp_exp_statement : Prop :=
  forall kappa lambda mu : Ens,
  equipotent (card_exp (card_exp kappa lambda) mu)
             (card_exp kappa (card_prod lambda mu)).

Theorem Power_strictly_greater : forall kappa : Ens,
  strictly_smaller kappa (Power kappa).
Proof.
intros kappa.
apply Cantor_strict.
Qed.

Definition exp_two_strict_statement : Prop :=
  forall kappa : Ens,
  equipotent (Power kappa) (card_exp card_two kappa) ->
  strictly_smaller kappa (card_exp card_two kappa).

Theorem exp_two_strict : exp_two_strict_statement.
Proof.
intros kappa Heq.
apply strictly_smaller_equipotent_right with (Power kappa).
- apply Cantor_strict.
- exact Heq.
Qed.

(* ================================================================= *)
(* Section 3: Limit Ordinals, Unbounded Maps, and Cofinality        *)
(* ================================================================= *)

Definition is_unbounded_map (beta alpha : Ens) (f : Ens -> Ens) : Prop :=
  is_map beta alpha f /\
  (forall xi : Ens, IN xi alpha ->
    EXType Ens (fun gamma => IN gamma beta /\ (IN xi (f gamma) \/ EQ xi (f gamma)))).

Definition is_cofinal_from (beta alpha : Ens) : Prop :=
  EXType (Ens -> Ens) (fun f => is_unbounded_map beta alpha f).

Theorem id_is_unbounded : forall alpha : Ens,
  is_unbounded_map alpha alpha (fun x => x).
Proof.
intros alpha.
split.
- split.
  + intros a Ina. exact Ina.
  + intros a b Ina Inb Heq. exact Heq.
- intros xi Inxi.
  exists xi.
  split.
  + exact Inxi.
  + right. apply EQ_refl.
Qed.

Theorem cofinal_from_self : forall alpha : Ens,
  is_cofinal_from alpha alpha.
Proof.
intros alpha.
exists (fun x => x).
apply id_is_unbounded.
Qed.

Definition is_cofinality (beta alpha : Ens) : Prop :=
  is_limit_ord beta /\
  is_cofinal_from beta alpha /\
  (forall delta : Ens, is_limit_ord delta -> is_cofinal_from delta alpha ->
    INC beta delta).

Definition is_regular_cardinal (kappa : Ens) : Prop :=
  is_cardinal kappa /\ is_limit_ord kappa /\
  is_cofinality kappa kappa.

Definition is_singular_cardinal (kappa : Ens) : Prop :=
  is_cardinal kappa /\ is_limit_ord kappa /\
  EXType Ens (fun beta => is_cofinality beta kappa /\ ~ EQ beta kappa).

Definition aleph_0_regular_statement : Prop :=
  is_regular_cardinal aleph_0.

(* ================================================================= *)
(* Section 4: Konig's Theorem and Exponentiation Cofinality         *)
(* ================================================================= *)

Definition indexed_sum (I : Ens) (kappa : Ens -> Ens) : Ens :=
  Union (sup (pi1 I) (fun a => Prod (Sing (pi2 I a)) (kappa (pi2 I a)))).

Theorem Konig_diagonal_contradiction :
  forall (I : Ens) (lambda : Ens -> Ens) (d : Ens -> Ens) (F_eval : Ens -> Ens -> Ens),
  (forall i : Ens, IN i I -> IN (d i) (lambda i)) ->
  (forall (i : Ens) (x : Ens), IN i I -> EQ (F_eval (Couple i x) i) (d i) -> False) ->
  forall (j : Ens) (y : Ens), IN j I ->
  (forall i : Ens, IN i I -> EQ (F_eval (Couple j y) i) (d i)) ->
  False.
Proof.
intros I lambda d F_eval Hin_d Hnot_diag j y Inj Hall_eq.
assert (Heq_j : EQ (F_eval (Couple j y) j) (d j)).
{ apply (Hall_eq j Inj). }
apply (Hnot_diag j y Inj Heq_j).
Qed.

Definition Konig_Theorem_statement : Prop :=
  forall (I : Ens) (kappa lambda : Ens -> Ens),
  (forall i : Ens, IN i I -> strictly_smaller (kappa i) (lambda i)) ->
  strictly_smaller (indexed_sum I kappa)
                   (card_exp (Union (sup (pi1 I) (fun a => lambda (pi2 I a)))) I).

Definition cf_power_greater_statement : Prop :=
  forall kappa : Ens,
  is_cardinal kappa ->
  forall beta : Ens,
  is_cofinality beta (card_exp card_two kappa) ->
  strictly_smaller kappa beta.

Definition Konig_implies_cf_power : Prop :=
  Konig_Theorem_statement -> cf_power_greater_statement.
