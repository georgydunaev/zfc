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
Require Import Ordinal_theory.

Inductive Ord : Ens -> Prop := 
  Oo : (Ord Vide)
| So : (E:Ens)(Ord E)->(Ord (Class_succ E))
| Lo : (E:Ens)((e:Ens)(IN e E)->(Ord e))->(Ord (Union E))
| Eo : (E,E':Ens)(Ord E)->(EQ E E')->(Ord E').

Hints Resolve Oo So Lo : zfc.
