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
(*                                Coq V6.1                                 *)
(*                               Jully 1996                                 *)
(*                                                                          *)
(****************************************************************************)
(*                               Correctness.v                              *)
(****************************************************************************)
(*                                                                          *)
(*              A verification of the Alternating Bit Protocol              *)
(*                              using  CBS                                  *)
(*                                                                          *)
(*                           Eduardo Gimenez                                *)
(*                                                                          *)
(****************************************************************************)

Require Import abp.ABP.TRACES.Hypotheses.
Require Import Evt.
Require Import Unique.

Lemma correctness_cycle :
 forall (b : bool) (s : Stream A) (p : Process) (d : Discourse Channel Act),
 p = SENDING b s || ACK b -> Equity p d -> InTrace (tl s) p d.
cofix.
intros b s p d H E.
unfold InTrace in |- *.
apply palways.
apply (Evt45 b s p).
assumption.
auto.
intros q ss1 H2.
apply (correctness_cycle (negb b) (tl s) q ss1).
apply (Unique45 b s p d q ss1).
assumption.
auto.
apply
 (StillHappens Channel Act Trans A OneDel
    (Evt Channel Act Trans Precondition) (hd (tl s)) p d q ss1).
assumption.
assumption.
Defined.


Theorem correctness :
 forall (b : bool) (s : Stream A) (p : Process) (d : Discourse Channel Act),
 p = ABP b s -> Equity p d -> InTrace s p d.
intros b s p d H E.
unfold InTrace in |- *.
apply palways.
apply (Evt1 b s p).
assumption.
auto.
intros q ss1 H2.
apply (correctness_cycle b s q ss1).
apply (Unique1 b s p d q ss1).
assumption.
auto.
apply
 (StillHappens Channel Act Trans A OneDel
    (Evt Channel Act Trans Precondition) (hd s) p d q ss1).
assumption.
assumption.
Defined.
