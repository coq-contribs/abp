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
(*                                July 1996                                 *)
(*                                                                          *)
(****************************************************************************)
(*                              Hypotheses.v                                *)
(****************************************************************************)
(*                                                                          *)
(*              A verification of the Alternating Bit Protocol              *)
(*                              using  CBS                                  *)
(*                                                                          *)
(*                           Eduardo Gimenez                                *)
(*                                                                          *)
(****************************************************************************)

Require Export ABP.ABP.TRACES.Protocol.

(****************************************************)
(* Correcteness of the protocol : general settings  *)
(****************************************************)


(* Notation for the actions *)


(* Some notation for hidding general paramaters *)

(* <Warning> : Grammar is replaced by Notation *)

(* <Warning> : Syntax is discontinued *)


Notation UTrans := (UnrelProcTrans Channel Act) (only parsing).
(* <Warning> : Syntax is discontinued *)


Notation STrans := (SafeProcTrans Channel Act del) (only parsing).
(* <Warning> : Syntax is discontinued *)


(* <Warning> : Grammar is replaced by Notation *)
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
left; trivial.
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


Definition IsClear : Process -> Discourse Channel Act -> Prop.
intros p d.
case d.
intros c s d1.
exact (exists a : Act c, s = Clear _ Act c a).
Defined.


Definition Fairness :=
  Always Channel Act Trans (Evt Channel Act Trans IsClear).

Definition Rtalks : Process -> Discourse Channel Act -> Prop.
intros p d.
case d.
intros c s d1.
exact (c = lnk2 \/ c = del).
Defined.



Inductive Exceptions :
Process -> forall c : Channel, Signal _ Act c -> Prop :=
  | exep2 :
      forall (b : bool) (s : Stream A) (c : Channel) (w : Signal _ Act c),
      existS (Signal Channel Act) c w =
      existS (Signal Channel Act) lnk1 (Noise _ Act lnk1) ->
      Exceptions (SENDING b s || ACKING (negb b)) c w
  | exep3 :
      forall (b : bool) (s : Stream A) (c : Channel) (w : Signal _ Act c),
      c = lnk1 -> Exceptions (SENDING b s || OUT b (hd s)) c w
  | exep4 :
      forall (b : bool) (s : Stream A) (c : Channel) (w : Signal _ Act c),
      c = lnk1 -> Exceptions (SENDING b s || ACK b) c w
  | exep5 :
      forall (b : bool) (s : Stream A) (c : Channel) (w : Signal _ Act c),
      existS (Signal Channel Act) c w =
      existS (Signal Channel Act) lnk2 (Noise _ Act lnk2) ->
      Exceptions (SENDING b s || ACK b) c w
  | exep6 :
      forall (b : bool) (s : Stream A) (c : Channel) (w : Signal _ Act c),
      Exceptions (SENDING b s || ACKING b) c w.


Definition Precondition : Process -> Discourse Channel Act -> Prop.
intros p d.
case d.
intros c w d1.
exact (~ Exceptions p c w).
Defined.



Definition Equity :=
  Always Channel Act Trans (Evt Channel Act Trans Precondition).


(* Even more notation to forget general parameters *)

Definition OneDel (a : A) (p : Process) (d1 : Discourse Channel Act) :=
  let (c0, w0, _) := d1 in
  existS (Signal Channel Act) c0 w0 =
  existS (Signal Channel Act) del (Clear Channel Act del a).


Definition InTrace := PAlways Channel Act Trans A OneDel.

Lemma Evt_from_Equity :
 forall (p : Process) (d : Discourse _ Act),
 Equity p d -> Evt Channel Act Trans Precondition p d.
intros.
case H.
auto.
Defined.
