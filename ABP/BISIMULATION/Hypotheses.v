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
(****************************************************************************)
(*                 The Calculus of Inductive Constructions                  *)
(*                                                                          *)
(*                                Projet Coq                                *)
(*                                                                          *)
(*                     INRIA                        ENS-CNRS                *)
(*              Rocquencourt                        Lyon                    *)
(*                                                                          *)
(*                                Coq V6.1                                  *)
(*                                Jully 1996                                *)
(*                                                                          *)
(****************************************************************************)
(*                              Hypothesis.v                                *)
(****************************************************************************)
(*                                                                          *)
(*              A verification of the Alternating Bit Protocol              *)
(*                              using  CBS                                  *)
(*                                                                          *)
(*                           Eduardo Gimenez                                *)
(*                                                                          *)
(****************************************************************************)

Require Export abp.ABP.BISIMULATION.Protocol.

(****************************************************)
(* Correcteness of the protocol : general settings  *)
(****************************************************)


(* Notation for the actions *)

(*****
Token "!!".
Token "??".
******)

(* <Warning> : Grammar is replaced by Notation *)

(* <Warning> : Syntax is discontinued *)

(* <Warning> : Grammar is replaced by Notation *)

(* <Warning> : Syntax is discontinued *)


(* <Warning> : Grammar is replaced by Notation *)

(* <Warning> : Syntax is discontinued *)


(* Some notation for hidding general paramaters *)

Notation UTrans := (UnrelProcTrans Channel Act) (only parsing).
(* <Warning> : Syntax is discontinued *)


Notation STrans := (SafeProcTrans Channel Act del) (only parsing).
(* <Warning> : Syntax is discontinued *)



(* The transition relation : channel two is safe, channel one is not *)

Definition Trans (c : Channel) :=
  match c return (Process -> Action c -> Process -> Prop) with
  | lnk1 => UnrelProcTrans Channel Act lnk1
  | lnk2 => UnrelProcTrans Channel Act lnk2
  | del => SafeProcTrans Channel Act del
  end.

(* Decidability of Channels *)

Lemma compare : forall c1 c2 : Channel, {c1 = c2} + {c1 <> c2}.
simple destruct c1.
simple destruct c2.
left; try trivial.
right; red in |- *; intros H; discriminate H.
right; red in |- *; intros H; discriminate H.
simple destruct c2.
right; red in |- *; intros H; discriminate H.
left; trivial.
right; red in |- *; intros H; discriminate H.
simple destruct c2.
right; red in |- *; intros H; discriminate H.
right; red in |- *; intros H; discriminate H.
left; trivial.
Defined.


(* The silent transitions *)


Definition Silent (c : Channel) (w : Signal _ Act c) :=
  match c with
  | lnk1 => True
  | lnk2 => True
  | del => False
  end.


(* Notation for the weak equivalence between processes *)


(*****
Token "<=>".
******)

(* <Warning> : Grammar is replaced by Notation *)

(* <Warning> : Syntax is discontinued *)