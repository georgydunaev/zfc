(* This program is free software; you can redistribute it and/or
(* modify it under the terms of the GNU Lesser General Public License
(* as published by the Free Software Foundation; either version 2.1
(* of the License, or (at your option) any later version.
(*
(* This program is distributed in the hope that it will be useful,
(* but WITHOUT ANY WARRANTY; without even the implied warranty of
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
(* GNU General Public License for more details.
(*
(* You should have received a copy of the GNU Lesser General Public
(* License along with this program; if not, write to the Free
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA
(* 02110-1301 USA

(* Contribution to the Coq Library   V6.3 (July 1999)

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

Hint Resolve IN_Class_succ INC_Class_succ: zfc.
