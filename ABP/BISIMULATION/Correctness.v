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
(*                                 Coq V6.1                                 *)
(*                                Jully 1996                                *)
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
(* Correctness : The protocol is (weakly) equivalent to the process REPEAT  *)
(****************************************************************************)

Require Import ABP.ABP.BISIMULATION.Protocol.
Require Import ABP.ABP.BISIMULATION.Hypotheses.
Require Import ABP.ABP.BISIMULATION.Lemmas.

(* The proof proceeds consists in a mutual co-recursive definitions of
   equivalence for each of the states of the protocol, i.e. 
    
Lemma cycle : 
   (b:bool)(s:(Stream A))
      ((SENDING b s) || (ACK b)) <=> (REPEAT (tl s)).

Cofix  state4 
with
 state2 : (b:bool)(s:(Stream A))
      ((SENDING b s) || (ACKING (negb b))) <=> (REPEAT s)

 state1 : (b:bool)(s:(Stream A))
      ((SEND b s) || (ACKING (negb b))) <=> (REPEAT s) 

 state3 : (b:bool)(s:(Stream A))  
      ((SENDING b s) || (OUT b (hd s))) <=>  (REPEAT s) 
 
 state5 : (b:bool)(s:(Stream A))
      ((SENDING b s) || (ACKING b)) <=> (REPEAT (tl s)).


   In this file we only prove the case corresponding to the 
   first state. The proofs for the other cases are very 
   similar, and we state them as axioms. *)


Axiom
  state1 :
    forall (b : bool) (s : Stream A),
    weak_eq Channel Act Trans Silent (SEND b s || ACKING (negb b)) (REPEAT s).

Axiom
  state2 :
    forall (b : bool) (s : Stream A),
    weak_eq Channel Act Trans Silent (SENDING b s || ACKING (negb b))
      (REPEAT s).

Axiom
  state3 :
    forall (b : bool) (s : Stream A),
    weak_eq Channel Act Trans Silent (SENDING b s || OUT b (hd s)) (REPEAT s).
 
Axiom
  state5 :
    forall (b : bool) (s : Stream A),
    weak_eq Channel Act Trans Silent (SENDING b s || ACKING b)
      (REPEAT (tl s)).

Lemma state4 :
 forall (b : bool) (s : Stream A),
 weak_eq Channel Act Trans Silent (SENDING b s || ACK b) (REPEAT (tl s)).

cofix.
(* State IV *)
intros.
apply w_eq.

(* 1. REPEAT can simulate state 4 *)



simple destruct c.

(* 1.1.1 The action is on channel one ==> state 4 evolves into itself or
         into state5.  *)
simpl in |- *.
intros.
inversion H using PAR_UinvT.

simpl in |- *.
intros p3 p5 v H2 H3.
inversion H2 using SENDING_UinvTC1 in H3.
inversion H3 using ACK_UinvR.
exists (REPEAT (tl s)).
split; [ apply eps | apply state4 ].
exact I.

intros.
inversion H1 using ACK_UinvTC1 in H0.

intros.
rewrite (SENDING_ULoosed b s p3 H0).
exists (REPEAT (tl s)).
split; [ apply eps | apply state4 ].
exact I.

intros.
rewrite (ACK_ULoosed b lnk1 p4 H0).
exists (REPEAT (tl s)).
split; [ apply eps | apply state5 ].
exact I.

(* 1.1.2 The action is on channel two ==> state4 evolves into state1 or
into itself, if the transmition is lost *)

simpl in |- *.
intros.
inversion H using PAR_UinvT.

intros p3 p5 v H0 H1.
inversion H0 using SENDING_UinvT2. (* SENDING does not talk on channel two *)

intros p3 p5 v H0 H1.
inversion H1 using ACK_UinvTC2 in H0. 
inversion H0 using SENDING_UinvR. 
exists (REPEAT (tl s)).
split.
apply eps.
exact I.
rewrite (eqb_reflx b).
pattern b at 2 in |- *.
rewrite (negb_intro b).
apply (state1 (negb b) (tl s)).

intros p3 H0.
inversion H0 using SENDING_UinvT2. (* SENDING does not talk on channel two *)

intros p3 H0.
rewrite (ACK_ULoosed b lnk2 p3).
exists (REPEAT (tl s)).
split; [ apply eps | apply state5 ].
exact I.
assumption.

(* Action is on the deliverative channel ==> absurd *)
simpl in |- *.
intros.
inversion H using PAR_SinvT.

intros p3 p5 v H2.
inversion H2 using SENDING_SinvT.

intros p3 p5 v H2 H3.
inversion H3 using ACK_SinvT.

(* 2. State 4 can simulate REPEAT *)

simple destruct c.
(* 2.1.1 The action is on channel one ==> absurd *)

simpl in |- *.
intros.
inversion H using REPEAT_UinvTC1.

(* 2.1.2 The action is on channel two ==> absurd *)

simpl in |- *.
intros.
inversion H using REPEAT_UinvTC2.

(* 2.1.3 The action is on the deliverative channel *)

simpl in |- *.
intros.
inversion H using REPEAT_SinvT.


exists (SENDING (negb b) (tl s) || ACK (negb b)).
split.
apply
 (w_tau_left Channel Act Trans Silent del lnk2 (Clear _ Act lnk2 b)
    (Clear _ Act del (hd (tl s))) (SENDING b s || ACK b)
    (SEND (negb b) (tl s) || ACKING b)).
exact I.
simpl in |- *.
apply utpar2.
rewrite unfold_SENDING.
cut
 (SEND (negb b) (tl s) = (if eqb b b then SEND (negb b) (tl s) else SEND b s)).
intro.
pattern (SEND (negb b) (tl s)) at 2 in |- *.
rewrite H0.
apply
 (uttalk2 Channel Act lnk2 lnk1 (b, hd s)
    (fun b1 : bool => if eqb b1 b then SEND (negb b) (tl s) else SEND b s)).
rewrite (eqb_reflx b).
trivial.
rewrite unfold_ACK.
apply uttalk1.
apply
 (w_tau_left Channel Act Trans Silent del lnk1
    (Clear _ Act lnk1 (negb b, hd (tl s))) (Clear _ Act del (hd (tl s)))
    (SEND (negb b) (tl s) || ACKING b)
    (SENDING (negb b) (tl s) || OUT (negb b) (hd (tl s)))).
apply I. 
simpl in |- *.
apply utpar1.
rewrite unfold_SEND.
apply uttalk1.
rewrite unfold_ACKING.
apply utlisten1.
rewrite (eqb_reflx (negb b)).
trivial.
apply w_single.
red in |- *; trivial.
simpl in |- *.
apply stpar2.
rewrite unfold_SENDING.
apply sttalk3.
discriminate.
rewrite unfold_OUT.
apply sttalk1.
apply state4.
Qed.