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

Definition Class_succ (E : Ens) := Union (Paire E (Sing E)).

Theorem IN_Class_succ : forall E : Ens, IN E (Class_succ E).
intros E; unfold Class_succ in |- *; unfold Sing in |- *;
 apply IN_Union with (Paire E E); auto with zfc.
Qed.

Theorem INC_Class_succ : forall E : Ens, INC E (Class_succ E).
unfold INC in |- *; unfold Class_succ in |- *.
intros.
apply IN_Union with E; auto with zfc.
Qed.

Theorem IN_Class_succ_or :
 forall E E' : Ens, IN E' (Class_succ E) -> EQ E E' \/ IN E' E.
intros E E' i.
unfold Class_succ in i.
elim (Union_IN (Paire E (Sing E)) E' i).
intros E1; simple induction 1; intros i1 i2.
elim (Paire_IN E (Sing E) E1 i1).
intros; right; apply IN_sound_right with E1; auto with zfc.
intros; left; cut (IN E' (Sing E)).
auto with zfc.
apply IN_sound_right with E1; auto with zfc.
Qed.

Theorem E_not_IN_E : forall E : Ens, IN E E -> F.
simple induction E; intros A f r i.
cut False.
simple induction 1.
elim (IN_EXType (sup A f) (sup A f) i); intros a e.
simpl in a.
change (EQ (sup A f) (f a)) in e.
elim (r a).
apply IN_sound_right with (sup A f); auto with zfc.
exists a; auto with zfc.
Qed.

Hint Resolve IN_Class_succ INC_Class_succ: zfc.
