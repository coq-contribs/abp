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
(*                               July  1996                                 *)
(*                                                                          *)
(****************************************************************************)
(*                                 Unique.v                                 *)
(****************************************************************************)
(*                                                                          *)
(*              A verification of the Alternating Bit Protocol              *)
(*                              using  CBS                                  *)
(*                                                                          *)
(*                           Eduardo Gimenez                                *)
(*                                                                          *)
(****************************************************************************)

Require Import abp.ABP.TRACES.Lemmas.


Lemma Unique3 :
 forall (b : bool) (s : Stream A) (p : Process) (ss : Discourse Channel Act)
   (q : Process) (ss1 : Discourse Channel Act),
 Wittness Channel Act Trans A OneDel (hd s) q ss1 p ss ->
 p = SENDING b s || OUT b (hd s) -> q = SENDING b s || ACK b.
intros b s p ss q ss1 H.
elim H.

intros p0 ss0 c0 w0 q0 T H1 H2 HypInd whichisp0.
apply HypInd.
case (State3 b s c0 w0 q0).
rewrite whichisp0 in T; assumption.
intro state3; case state3; auto.      
intro state3; case state3; intros whichc whichq0.
unfold OneDel in H1.
absurd
 (existS (Signal Channel Act) c0 w0 =
  existS (Signal Channel Act) del (Clear Channel Act del (hd s))); 
 auto.

intros c0 w0 p0 T H1 whichisp0.
case (State3 b s c0 w0 q).
rewrite whichisp0 in T; assumption.
intro state3; case state3; intros whichc whichq0.
absurd (c0 = lnk1).
unfold OneDel in H1.
dependent rewrite H1.
discriminate.
assumption.
intro state3; case state3; auto.
Defined.


Lemma Unique2 :
 forall (b : bool) (s : Stream A) (p : Process) (ss : Discourse Channel Act)
   (q : Process) (ss1 : Discourse Channel Act),
 Wittness Channel Act Trans A OneDel (hd s) q ss1 p ss ->
 p = SENDING b s || ACKING (negb b) -> q = SENDING b s || ACK b.

intros b s p ss q ss1 H.
elim H.

intros p0 ss0 c0 w0 q0 T H1 H2 HypInd whichisp0.
case (State2 b s c0 w0 q0).
rewrite whichisp0 in T; assumption.
intro state; case state; intros whichc whichq0.
apply (Unique3 b s q0 ss0 q ss1).
assumption.
assumption.

intro state; case state; intros whichc whichq0.
apply HypInd.
assumption.

intros c0 w0 p0 T H1 whichisp0.
case (State2 b s c0 w0 q).
rewrite whichisp0 in T; assumption.
intro state; case state; intros whichc whichq0.
absurd (c0 = lnk1).
unfold OneDel in H1.
dependent rewrite H1.
discriminate.
assumption.

intro state; case state; intros whichc whichq0.
absurd (c0 = lnk1).
unfold OneDel in H1.
dependent rewrite H1.
discriminate.
dependent rewrite whichc.
trivial.
Defined.



Lemma Unique1 :
 forall (b : bool) (s : Stream A) (p : Process) (ss : Discourse Channel Act)
   (q : Process) (ss1 : Discourse Channel Act),
 Wittness Channel Act Trans A OneDel (hd s) q ss1 p ss ->
 p = SEND b s || ACKING (negb b) -> q = SENDING b s || ACK b.
intros b s p ss q ss1 H.
elim H.

intros p0 ss0 c0 w0 q0 T H1 H2 HypInd whichisp0.
case (State1 b s c0 w0 q0).
rewrite whichisp0 in T; assumption.
intro state; case state; intros whichc whichq0.
apply (Unique3 b s q0 ss0 q ss1).
assumption.
assumption.

intro state; case state; intros whichc whichq0.
apply (Unique2 b s q0 ss0 q ss1).
assumption.
assumption.

intros c0 w0 p0 T H1 whichisp0.
case (State1 b s c0 w0 q).
rewrite whichisp0 in T; assumption.
intro state; case state; intros whichc whichq0.
absurd (c0 = lnk1).
unfold OneDel in H1.
dependent rewrite H1.
discriminate.
assumption.

intro state; case state; intros whichc whichq0.
absurd (c0 = lnk1).
unfold OneDel in H1.
dependent rewrite H1.
discriminate.
dependent rewrite whichc.
trivial.
Defined.


Lemma Unique45 :
 forall (b : bool) (s : Stream A) (p : Process) (ss : Discourse Channel Act)
   (q : Process) (ss1 : Discourse Channel Act),
 Wittness Channel Act Trans A OneDel (hd (tl s)) q ss1 p ss ->
 p = SENDING b s || ACK b \/ p = SENDING b s || ACKING b ->
 q = SENDING (negb b) (tl s) || ACK (negb b).

intros b s p ss q ss1 H.
elim H.

intros p0 ss0 c0 w0 q0 T H1 H2 HypInd whichisp0.
case whichisp0; clear whichisp0; intro whichisp0.

case (State4 b s c0 w0 q0).
rewrite whichisp0 in T; assumption.
intro state; case state; intros whichc whichq0.
apply HypInd.
auto.

intro state.
case state.
intro statep1; case statep1; intros whichc whichq0.
apply (Unique1 (negb b) (tl s) q0 ss0 q ss1).
assumption.
rewrite negb_elim; assumption.

intro statep2; case statep2; intros whichc whichq0.
apply HypInd.
auto.

case (State5 b s c0 w0 q0).
rewrite whichisp0 in T; assumption.
intro state; case state; intros whichc whichq0.
apply HypInd.
auto.

intro state; case state; intros whichc whichq0.
apply HypInd.
auto.

intros c0 w0 p0 T H1 whichisp0.
case whichisp0; clear whichisp0; intro whichisp0.

case (State4 b s c0 w0 q).
rewrite whichisp0 in T; assumption.
intro state; case state; intros whichc whichq0.
absurd (c0 = lnk1).
unfold OneDel in H1.
dependent rewrite H1.
discriminate.
assumption.

intro statep1; case statep1.
intro state; case state; intros whichc whichq0.
absurd (c0 = lnk2).
unfold OneDel in H1.
dependent rewrite H1.
discriminate.
dependent rewrite whichc.
trivial.

intro state; case state; intros whichc whichq0.
absurd (c0 = lnk2).
unfold OneDel in H1.
dependent rewrite H1.
discriminate.
dependent rewrite whichc.
trivial.

case (State5 b s c0 w0 q).
rewrite whichisp0 in T; assumption.

intro state; case state; intros whichc whichq0.
absurd (c0 = lnk1).
unfold OneDel in H1.
dependent rewrite H1.
discriminate.
dependent rewrite whichc.
trivial.
intro state; case state; intros whichc whichq0.
absurd (c0 = lnk1).
unfold OneDel in H1.
dependent rewrite H1.
discriminate.
dependent rewrite whichc.
trivial.
Defined.



