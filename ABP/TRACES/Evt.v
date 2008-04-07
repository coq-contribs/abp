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
(*                             Eventually.v                                 *)
(****************************************************************************)
(*                                                                          *)
(*              A verification of the Alternating Bit Protocol              *)
(*                              using  CBS                                  *)
(*                                                                          *)
(*                           Eduardo Gimenez                                *)
(*                                                                          *)
(****************************************************************************)

Require Import ABP.ABP.TRACES.Lemmas.

Lemma Evt3 :
 forall (b : bool) (s : Stream A) (p : Process) (ss : Discourse Channel Act),
 Equity p ss ->
 p = SENDING b s || OUT b (hd s) ->
 Evt Channel Act Trans (OneDel (hd s)) p ss.

intros b s p ss H.
elim (Evt_from_Equity p ss H).
intros q c w ss0 p0 T H1 HypInd whichisp0.
apply (notyet _ _ Trans (OneDel (hd s)) q).
assumption.
 
intros q0 T0 H0.
rewrite whichisp0 in T0.
case (State3 b s c w q0).
assumption.
 
intros state3.
case state3.
intros whichisc whichisq0.
apply HypInd.
rewrite whichisp0; assumption.
unfold Precondition in |- *.
red in |- *.
intro.
apply H2.
rewrite whichisp0.
apply exep3.
assumption.
assumption.

intros state4.
case state4.
intros whichiscw whichisq0.
case H0.
unfold OneDel in |- *.
assumption.
Defined.


Lemma Evt2 :
 forall (b : bool) (s : Stream A) (p : Process) (ss : Discourse Channel Act),
 Equity p ss ->
 p = SENDING b s || ACKING (negb b) ->
 Evt Channel Act Trans (OneDel (hd s)) p ss.

intros b s p ss H.
generalize H.
elim (Evt_from_Equity p ss H).
intros q c w ss0 p0 T H1 HypInd EqH whichisp0.
apply (notyet _ _ Trans (OneDel (hd s)) q).
assumption.
 
intros q0 T0 H0.
rewrite whichisp0 in T0.
case (State2 b s c w q0).
assumption.
 
intro state2; case state2; intros whichiscw whichisq0.
apply (Evt3 b s q0 ss0).
apply
 (Always_stable Channel Act Trans (Evt Channel Act Trans Precondition) p0 ss0
    c w q0).
rewrite whichisp0; assumption.
assumption.
assumption.

intros state2.
case state2.
intros whichiscw whichisq0.
apply HypInd.
rewrite whichisp0; assumption.
unfold Precondition in |- *.
red in |- *.
intro.
apply H2.
rewrite whichisp0.
apply exep2.
assumption.
apply
 (Always_stable Channel Act Trans (Evt Channel Act Trans Precondition) p0 ss0
    c w q0).
rewrite whichisp0; assumption.
assumption.
assumption.
Defined.

Lemma Evt1 :
 forall (b : bool) (s : Stream A) (p : Process) (ss : Discourse Channel Act),
 Equity p ss ->
 p = SEND b s || ACKING (negb b) ->
 Evt Channel Act Trans (OneDel (hd s)) p ss.

intros b s p ss H.
generalize H.
elim (Evt_from_Equity p ss H).
intros q c w ss0 p0 T H1 HypInd EqH whichisp0.
apply (notyet _ _ Trans (OneDel (hd s)) q).
assumption.
 
intros q0 T0 H0.
rewrite whichisp0 in T0.
case (State1 b s c w q0).
assumption.
 
intro state1; case state1; intros whichisc whichisq0.
apply (Evt3 b s q0 ss0).
apply
 (Always_stable Channel Act Trans (Evt Channel Act Trans Precondition) p0 ss0
    c w q0).
rewrite whichisp0; assumption.
assumption.
assumption.

intros state2.
case state2.
intros whichiscw whichisq0.
apply (Evt2 b s q0 ss0).
apply
 (Always_stable Channel Act Trans (Evt Channel Act Trans Precondition) p0 ss0
    c w q0).
rewrite whichisp0; assumption.
assumption.
assumption.
Defined.



Theorem Evt45 :
 forall (b : bool) (s : Stream A) (p : Process) (ss : Discourse Channel Act),
 Equity p ss ->
 p = SENDING b s || ACK b \/ p = SENDING b s || ACKING b ->
 Evt Channel Act Trans (OneDel (hd (tl s))) p ss.

intros b s p ss H.
generalize H.
elim (Evt_from_Equity p ss H).
intros q c w ss0 p0 T H1 HypInd EqH whichisp0.
apply (notyet _ _ Trans (OneDel (hd (tl s))) q).
assumption.
 
intros q0 T0 H0.
case whichisp0; clear whichisp0; intro whichisp0.
rewrite whichisp0 in T0.
case (State4 b s c w q0).
assumption.
 
intros state4.
case state4.
intros whichisc whichisq0.
apply HypInd.
rewrite whichisp0; assumption.
unfold Precondition in |- *.
red in |- *.
intro.
apply H2.
rewrite whichisp0.
apply exep4.
assumption.
apply
 (Always_stable Channel Act Trans (Evt Channel Act Trans Precondition) p0 ss0
    c w q0).
rewrite whichisp0; assumption.
assumption.
auto.

intros state4.
case state4.
intro state4p; case state4p; intros whichisc whichisq0.
apply (Evt1 (negb b) (tl s) q0 ss0).
apply
 (Always_stable Channel Act Trans (Evt Channel Act Trans Precondition) p0 ss0
    c w q0).
rewrite whichisp0; assumption.
assumption.
rewrite negb_elim.
assumption.

intros state4p.
case state4p.
intros whichiswc whichisq0.
apply HypInd.
rewrite whichisp0; assumption.
unfold Precondition in |- *.
red in |- *.
intro.
apply H2.
rewrite whichisp0.
apply exep5.
assumption.
apply
 (Always_stable Channel Act Trans (Evt Channel Act Trans Precondition) p0 ss0
    c w q0).
rewrite whichisp0; assumption.
assumption.
auto.

(* State 5 *)

rewrite whichisp0 in T0.
case (State5 b s c w q0).
assumption.
 
intros state5; case state5; intros whichisc whichisq0.
apply HypInd.
rewrite whichisp0; assumption.
unfold Precondition in |- *.
red in |- *.
intro.
apply H2.
rewrite whichisp0.
apply exep6.
apply
 (Always_stable Channel Act Trans (Evt Channel Act Trans Precondition) p0 ss0
    c w q0).
rewrite whichisp0; assumption.
assumption.
auto.

intros state5; case state5; intros whichisc whichisq0.
apply HypInd.
rewrite whichisp0; assumption.
unfold Precondition in |- *.
red in |- *.
intro.
apply H2.
rewrite whichisp0.
apply exep6.
apply
 (Always_stable Channel Act Trans (Evt Channel Act Trans Precondition) p0 ss0
    c w q0).
rewrite whichisp0; assumption.
assumption.
auto.
Defined.
