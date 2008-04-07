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
(*                                Jully 1996                                 *)
(*                                                                          *)
(****************************************************************************)
(*                                Lemmas.v                                  *)
(****************************************************************************)
(*                                                                          *)
(*              A verification of the Alternating Bit Protocol              *)
(*                              using  CBS                                  *)
(*                                                                          *)
(*                           Eduardo Gimenez                                *)
(*                                                                          *)
(****************************************************************************)
(*   The inversion lemmas for the transition relation and the lemmas for    *)
(*   unfolding the states of the protocol.                                  *)
(****************************************************************************)


Require Export ABP.ABP.TRACES.Hypotheses.

(*********************)
(* Unfolding  Lemmas *)
(*********************)

Lemma unfold_SEND :
 forall (b : bool) (s : Stream A),
 SEND b s =
 ACTALK Channel Act lnk1 (b, hd s) (SENDING b s) lnk2
   (fun _ : bool => SEND b s). 
intros.
apply (unfold_process Channel Act (SEND b s)).
Qed.


Lemma unfold_SENDING :
 forall (b : bool) (s : Stream A),
 SENDING b s =
 ACTALK Channel Act lnk1 (b, hd s) (SENDING b s) lnk2
   (fun b1 : bool => if eqb b1 b then SEND (negb b) (tl s) else SEND b s).
intros.
apply (unfold_process Channel Act (SENDING b s)).
Qed.

Lemma unfold_ACKING :
 forall b : bool,
 ACKING b =
 ACLISTEN Channel Act lnk1
   (fun ba : bool * A =>
    let (b1, a) := ba in if eqb b1 (negb b) then OUT (negb b) a else ACK b).
intros.
apply (unfold_process Channel Act (ACKING b)).
Qed.


Lemma unfold_ACK :
 forall b : bool,
 ACK b =
 ACTALK Channel Act lnk2 b (ACKING b) lnk1 (fun _ : bool * A => ACK b).
intros.
apply (unfold_process Channel Act (ACK b)).
Qed.

Lemma unfold_OUT :
 forall (b : bool) (a : A),
 OUT b a =
 ACTALK Channel Act del a (ACK b) lnk1 (fun _ : bool * A => OUT b a).
intros.
apply (unfold_process Channel Act (OUT b a)).
Qed.


(*************************)
(* Discrimination Lemmas *)
(*************************)

Definition select_fun : Process -> forall c1 : Channel, Act c1 -> Process. 
intros p.
case p.
intros c1 v p1 c2 f.
intros c.
case (compare c2 c).
intros H; case H.
exact f.
intros.
exact p.
intros c1 f.
intros c.
case (compare c1 c).
intros H; case H.
exact f.
intros.
exact p.
intros.
exact p.
Defined.

Lemma disc_fun :
 forall p1 p2 : Process,
 p1 = p2 -> forall c : Channel, select_fun p1 c = select_fun p2 c.
intros p1 p2 H.
rewrite H.
trivial.
Defined.

Lemma inj_Tfun :
 forall (c1 c2 : Channel) (v1 : Act c1) (v2 : Act c2) 
   (p1 p2 : Process) (c3 : Channel) (f1 f2 : Act c3 -> Process),
 ACTALK Channel Act c1 v1 p1 c3 f1 = ACTALK Channel Act c2 v2 p2 c3 f2 ->
 f1 = f2.
simple destruct c3.
intros f1 f2 H.
apply
 (disc_fun (ACTALK Channel Act c1 v1 p1 lnk1 f1)
    (ACTALK Channel Act c2 v2 p2 lnk1 f2) H lnk1).
intros f1 f2 H.
apply
 (disc_fun (ACTALK Channel Act c1 v1 p1 lnk2 f1)
    (ACTALK Channel Act c2 v2 p2 lnk2 f2) H lnk2).
intros f1 f2 H.
apply
 (disc_fun (ACTALK Channel Act c1 v1 p1 del f1)
    (ACTALK Channel Act c2 v2 p2 del f2) H del).
Defined.

Lemma inj_Lfun :
 forall (c3 : Channel) (f1 f2 : Act c3 -> Process),
 ACLISTEN Channel Act c3 f1 = ACLISTEN Channel Act c3 f2 -> f1 = f2.
simple destruct c3.
intros f1 f2 H.
apply
 (disc_fun (ACLISTEN Channel Act lnk1 f1) (ACLISTEN Channel Act lnk1 f2) H
    lnk1).
intros f1 f2 H.
apply
 (disc_fun (ACLISTEN Channel Act lnk2 f1) (ACLISTEN Channel Act lnk2 f2) H
    lnk2).
intros f1 f2 H.
apply
 (disc_fun (ACLISTEN Channel Act del f1) (ACLISTEN Channel Act del f2) H del).
Defined.


Definition select_mess : Process -> forall c : Channel, Act c -> Act c. 
intro p.
simple destruct c; simpl in |- *.
case p.
intros c1 v p1 c2 f.
case (compare c1 lnk1).
intros.
rewrite e in v.
exact v.
trivial.
trivial.
trivial.
case p.
intros c1 v p1 c2 f.
case (compare c1 lnk2).
intros.
rewrite e in v.
exact v.
trivial.
trivial.
trivial.
case p.
intros c1 v p1 c2 f.
case (compare c1 del).
intros.
rewrite e in v.
exact v.
trivial.
trivial.
trivial.
Defined.


Lemma disc_mess :
 forall p1 p2 : Process,
 p1 = p2 ->
 forall (c : Channel) (a : Act c), select_mess p1 c a = select_mess p2 c a.
intros p1 p2 H.
rewrite H.
trivial.
Defined.

Transparent sym_eq.

Lemma inj_Tmess :
 forall (c1 : Channel) (v1 v2 : Act c1) (p1 p2 : Process) 
   (c3 c4 : Channel) (f1 : Act c3 -> Process) (f2 : Act c4 -> Process),
 ACTALK Channel Act c1 v1 p1 c3 f1 = ACTALK Channel Act c1 v2 p2 c4 f2 ->
 v1 = v2.
simple destruct c1.
intros v1 v2 p1 p2 c3 c4 f1 f2 H.
apply
 (disc_mess (ACTALK Channel Act lnk1 v1 p1 c3 f1)
    (ACTALK Channel Act lnk1 v2 p2 c4 f2) H lnk1 v1).
intros v1 v2 p1 p2 c3 c4 f1 f2 H.
apply
 (disc_mess (ACTALK Channel Act lnk2 v1 p1 c3 f1)
    (ACTALK Channel Act lnk2 v2 p2 c4 f2) H lnk2 v1).
intros v1 v2 p1 p2 c3 c4 f1 f2 H.
apply
 (disc_mess (ACTALK Channel Act del v1 p1 c3 f1)
    (ACTALK Channel Act del v2 p2 c4 f2) H del v1).
Defined.


(*************************)
(* Transformation lemmas *)
(*************************)


(* Two process in parallel *)

Derive Inversion_clear PAR_Uinv with
 (forall (c : Channel) (w : Action c) (p1 p2 q : Process),
  UnrelProcTrans Channel Act c (p1 || p2) w q).


Derive Inversion_clear PAR_Sinv with
 (forall (w : Action del) (p1 p2 q : Process),
  SafeProcTrans Channel Act del (p1 || p2) w q).

Derive Inversion_clear PAR_UinvT with
 (forall (c : Channel) (w : Signal _ Act c) (p1 p2 q : Process),
  UnrelProcTrans Channel Act c (p1 || p2) (Transmit _ Act c w) q).


Derive Inversion_clear PAR_SinvT with
 (forall (w : Signal _ Act del) (p1 p2 q : Process),
  SafeProcTrans Channel Act del (p1 || p2) (Transmit _ Act del w) q).



Derive Inversion_clear PAR_UinvL with
 (forall (c : Channel) (p1 p2 q : Process),
  UnrelProcTrans Channel Act c (p1 || p2)
    (Transmit Channel Act c (Noise Channel Act c)) q).

Derive Inversion_clear PAR_SinvL with
 (forall (c : Channel) (p1 p2 q : Process),
  SafeProcTrans Channel Act del (p1 || p2)
    (Transmit Channel Act del (Noise Channel Act del)) q).


(* SENDING *)


Lemma SENDING_ULoosed :
 forall (b : bool) (s : Stream A) (p3 : Process),
 UnrelProcTrans Channel Act lnk1 (SENDING b s)
   (Transmit Channel Act lnk1 (Noise Channel Act lnk1)) p3 ->
 p3 = SENDING b s.
intros b s p3.
pattern (SENDING b s) at 1 in |- *; rewrite unfold_SENDING.
intro H.
inversion H.
trivial.
Defined.

Lemma SENDING_UinvT2 :
 forall (P : Prop) (w : Signal _ Act lnk2) (q : Process) 
   (b : bool) (s : Stream A),
 UnrelProcTrans Channel Act lnk2 (SENDING b s) (Transmit _ Act lnk2 w) q -> P.
intros P w q b s.
rewrite unfold_SENDING.
intros H2.
inversion H2.
Defined.

Lemma SENDING_SinvT :
 forall (P : Prop) (w : Signal _ Act del) (q : Process) 
   (b : bool) (s : Stream A),
 SafeProcTrans Channel Act del (SENDING b s) (Transmit _ Act del w) q -> P.
intros P w q b s.
rewrite unfold_SENDING.
intros H2.
inversion H2.
Defined.

Lemma SENDING_SinvR :
 forall (P : A -> Process -> bool -> Stream A -> Prop) 
   (v : A) (q : Process) (b : bool) (s : Stream A),
 P v (SENDING b s) b s ->
 SafeProcTrans Channel Act del (SENDING b s) (Receive Channel Act del v) q ->
 P v q b s.
intros P v q b s H.
rewrite unfold_SENDING.
intros H1.
simple inversion H1.
discriminate H2. 
discriminate H2. 
rewrite <- H4.
rewrite H2.
rewrite <- (unfold_SENDING b s).
auto. 
discriminate H2. 
discriminate H2. 
discriminate H3. 
discriminate H3.
discriminate H3.
Defined.

Lemma SENDING_UinvR :
 forall (P : bool -> Process -> bool -> Stream A -> Prop) 
   (b1 : bool) (q : Process) (b : bool) (s : Stream A),
 P b1 (if eqb b1 b then SEND (negb b) (tl s) else SEND b s) b s ->
 UnrelProcTrans Channel Act lnk2 (SENDING b s) (Receive _ Act lnk2 b1) q ->
 P b1 q b s.
intros P b1 q b s H.
rewrite unfold_SENDING.
intros H0.
simple inversion H0.
discriminate H2. 
rewrite <- H3.
rewrite
 (inj_Tfun c1 lnk1 v1 (b, hd s) p1 (SENDING b s) lnk2 f
    (fun b1 : bool =>
     match eqb b1 b return Process with
     | true => SEND (negb b) (tl s)
     | false => SEND b s
     end)).
injection H2.
intro.
rewrite H4.
assumption.
assumption.
intro.
absurd (c2 = lnk2).
assumption.
injection H2; trivial.
discriminate H2.
discriminate H2.
discriminate H2.
discriminate H3.
discriminate H3.
discriminate H3.
discriminate H3.
discriminate H3.
Defined.

Lemma SENDING_UinvTC1 :
 forall (P : bool * A -> Process -> bool -> Stream A -> Prop) 
   (v : bool * A) (q : Process) (b : bool) (s : Stream A),
 P (b, hd s) (SENDING b s) b s ->
 UnrelProcTrans Channel Act lnk1 (SENDING b s)
   (Transmit _ Act lnk1 (Clear _ Act lnk1 v)) q -> 
 P v q b s.
intros P v q b s H.
rewrite (unfold_SENDING b s).
intros H2.
simple inversion H2.
injection H1.
intro.
case H4.
rewrite
 (inj_Tmess lnk1 v0 (b, hd s) p (SENDING b s) c2 lnk2 f
    (fun b1 : bool =>
     match eqb b1 b return Process with
     | true => SEND (negb b) (tl s)
     | false => SEND b s
     end)).
rewrite <- H3.
injection H0.
intros.
rewrite H7.
assumption.
assumption.
discriminate H1.
discriminate H3.
discriminate H1. 
discriminate H3.
discriminate H1.
discriminate H3.
discriminate H3.
discriminate H3.
discriminate H3. 
discriminate H3.
Defined.


(* SEND *)

Lemma SEND_SinvT :
 forall (P : Prop) (w : Signal _ Act del) (q : Process) 
   (b : bool) (s : Stream A),
 SafeProcTrans Channel Act del (SEND b s) (Transmit _ Act del w) q -> P.
intros P w q b s.
rewrite unfold_SEND.
intro H1.
inversion H1.
Defined.

Lemma SEND_ULoosed :
 forall (b : bool) (s : Stream A) (p3 : Process),
 UnrelProcTrans Channel Act lnk1 (SEND b s)
   (Transmit Channel Act lnk1 (Noise Channel Act lnk1)) p3 ->
 p3 = SENDING b s.
intros b s p3.
pattern (SEND b s) at 1 in |- *; rewrite unfold_SEND.
intro H.
inversion H.
trivial.
Defined.

Lemma SEND_UinvTC1 :
 forall (P : bool * A -> Process -> bool -> Stream A -> Prop) 
   (v : bool * A) (q : Process) (b : bool) (s : Stream A),
 P (b, hd s) (SENDING b s) b s ->
 UnrelProcTrans Channel Act lnk1 (SEND b s)
   (Transmit _ Act lnk1 (Clear _ Act lnk1 v)) q -> 
 P v q b s.
intros P v q b s H.
rewrite (unfold_SEND b s).
intros H2.
simple inversion H2.
injection H1.
intro.
case H4.
rewrite
 (inj_Tmess lnk1 v0 (b, hd s) p (SENDING b s) c2 lnk2 f
    (fun b1 : bool => SEND b s)).
rewrite <- H3.
injection H0.
intros.
rewrite H7.
assumption.
assumption.
discriminate H1.
discriminate H3.
discriminate H1. 
discriminate H3.
discriminate H1.
discriminate H3.
discriminate H3.
discriminate H3.
discriminate H3. 
discriminate H3.
Defined.

Lemma SEND_UinvT2 :
 forall (P : Prop) (w : Signal _ Act lnk2) (q : Process) 
   (b : bool) (s : Stream A),
 UnrelProcTrans Channel Act lnk2 (SEND b s) (Transmit _ Act lnk2 w) q -> P.
intros P w q b s.
rewrite (unfold_SEND b s).
intros H.
inversion H.
Defined.

Lemma SEND_UinvR :
 forall (P : bool -> Process -> bool -> Stream A -> Prop) 
   (v : bool) (q : Process) (b : bool) (s : Stream A),
 P v (SEND b s) b s ->
 UnrelProcTrans Channel Act lnk2 (SEND b s) (Receive _ Act lnk2 v) q ->
 P v q b s.
intros P b1 q b s H.
rewrite unfold_SEND.
intros H0.
simple inversion H0.
discriminate H2. 
rewrite <- H3.
rewrite
 (inj_Tfun c1 lnk1 v1 (b, hd s) p1 (SENDING b s) lnk2 f
    (fun b1 : bool => SEND b s)).
assumption.
assumption.
intro.
absurd (c2 = lnk2).
assumption.
injection H2; trivial.
discriminate H2.
discriminate H2.
discriminate H2.
discriminate H3.
discriminate H3.
discriminate H3.
discriminate H3.
discriminate H3.
Defined.

(* ACKING *)

Lemma ACKING_UinvR :
 forall (P : bool * A -> Process -> bool -> Prop) (v : bool * A)
   (q : Process) (b : bool),
 P v (let (b1, a) := v in if eqb b1 (negb b) then OUT (negb b) a else ACK b)
   b ->
 UnrelProcTrans Channel Act lnk1 (ACKING b) (Receive _ Act lnk1 v) q ->
 P v q b.
intros P b1 q b H.
rewrite unfold_ACKING.
intros H0.
simple inversion H0.
discriminate H2. 
discriminate H1.
discriminate H2. 
discriminate H1.
rewrite <- H4.
rewrite
 (inj_Lfun lnk1 f
    (fun v : bool * A =>
     let (b1, a) := v in if eqb b1 (negb b) then OUT (negb b) a else ACK b))
 .
intro.
rewrite <- H1.
injection H3.
intro.
rewrite H5.
assumption.
assumption.
intro.
absurd (d = lnk1).
assumption.
injection H2; trivial.
discriminate H3.
discriminate H3.
discriminate H3.
discriminate H3.
discriminate H3.
Defined.


Lemma ACKING_UinvT :
 forall (P : Prop) (c : Channel) (w : Signal _ Act c) 
   (q : Process) (b : bool),
 UnrelProcTrans Channel Act c (ACKING b) (Transmit _ Act c w) q -> P.
intros P c w q b.
rewrite unfold_ACKING.
intros H1.
inversion H1.
Defined.

Lemma ACKING_SinvT :
 forall (P : Prop) (w : Signal _ Act del) (q : Process) (b : bool),
 SafeProcTrans Channel Act del (ACKING b) (Transmit _ Act del w) q -> P.
intros P w q b.
rewrite unfold_ACKING.
intros H1.
inversion H1.
Defined.

(* ACK *)

Lemma ACK_ULoosed :
 forall (b : bool) (c : Channel) (p3 : Process),
 UnrelProcTrans Channel Act c (ACK b)
   (Transmit Channel Act c (Noise Channel Act c)) p3 -> 
 p3 = ACKING b.
intros b c p3.
pattern (ACK b) at 1 in |- *; rewrite unfold_ACK.
intro H.
inversion H.
trivial.
Defined.

Lemma ACK_SinvT :
 forall (P : Prop) (w : Signal _ Act del) (q : Process) (b : bool),
 SafeProcTrans Channel Act del (ACK b) (Transmit _ Act del w) q -> P.
intros P w q b.
rewrite unfold_ACK.
intro H1.
inversion H1.
Defined.

Lemma ACK_UinvT1 :
 forall (P : Prop) (w : Signal _ Act lnk1) (q : Process) (b : bool),
 UnrelProcTrans Channel Act lnk1 (ACK b) (Transmit _ Act lnk1 w) q -> P.
intros P w q b.
rewrite unfold_ACK.
intro H1.
inversion H1.
Defined.

Lemma ACK_UinvTC2 :
 forall (P : bool -> Process -> bool -> Prop) (v : bool) 
   (q : Process) (b : bool),
 P b (ACKING b) b ->
 UnrelProcTrans Channel Act lnk2 (ACK b)
   (Transmit _ Act lnk2 (Clear _ Act lnk2 v)) q -> 
 P v q b.
intros P v q b H.
rewrite (unfold_ACK b).
intros H2.
simple inversion H2.
injection H1.
intro.
case H4.
rewrite
 (inj_Tmess lnk2 v0 b p (ACKING b) c2 lnk1 f (fun b1 : bool * A => ACK b))
 .
rewrite <- H3.
injection H0.
intros.
rewrite H7.
assumption.
assumption.
discriminate H1.
discriminate H3.
discriminate H1. 
discriminate H3.
discriminate H1.
discriminate H3.
discriminate H3.
discriminate H3.
discriminate H3. 
discriminate H3.
Defined.

Lemma ACK_UinvTC1 :
 forall (P : Prop) (v : bool * A) (q : Process) (b : bool),
 UnrelProcTrans Channel Act lnk1 (ACK b)
   (Transmit _ Act lnk1 (Clear _ Act lnk1 v)) q -> P.
intros P w q b.
rewrite unfold_ACK.
intro H1.
inversion H1.
Defined.

Lemma ACK_UinvR :
 forall (P : bool * A -> Process -> bool -> Prop) (v : bool * A)
   (q : Process) (b : bool),
 P v (ACK b) b ->
 UnrelProcTrans Channel Act lnk1 (ACK b) (Receive _ Act lnk1 v) q -> P v q b.
intros P v q b H.
rewrite unfold_ACK.
intros H0.
simple inversion H0.
discriminate H2. 
rewrite <- H3.
rewrite
 (inj_Tfun c1 lnk2 v1 b p1 (ACKING b) lnk1 f (fun _ : bool * A => ACK b))
 .
assumption.
assumption.
intro.
absurd (c2 = lnk1).
assumption.
injection H2; trivial.
discriminate H2.
discriminate H2.
discriminate H2.
discriminate H3.
discriminate H3.
discriminate H3.
discriminate H3.
discriminate H3.
Defined.


(* OUT *)

Lemma OUT_SinvT :
 forall (P : Signal _ Act del -> Process -> bool -> A -> Prop)
   (w : Signal _ Act del) (q : Process) (b : bool) 
   (a : A),
 P (Clear _ Act del a) (ACK b) b a ->
 SafeProcTrans Channel Act del (OUT b a) (Transmit _ Act del w) q ->
 P w q b a.
intros P w q b a H.
rewrite unfold_OUT.
intros H0.
simple inversion H0.
rewrite <- H3.
injection H2.
intros.
rewrite <- H4.
rewrite (inj_Tmess del v a p (ACK b) c2 lnk1 f (fun _ : bool * A => OUT b a)).
injection H1.
intros.
rewrite H7.
assumption.
assumption.
discriminate H3.
discriminate H3.
discriminate H3.
discriminate H3.
discriminate H3.
discriminate H3.
discriminate H3.
Defined.

Lemma OUT_UinvR :
 forall (P : bool * A -> Process -> bool -> A -> Prop) 
   (v : bool * A) (q : Process) (b : bool) (a : A),
 P v (OUT b a) b a ->
 UnrelProcTrans Channel Act lnk1 (OUT b a) (Receive _ Act lnk1 v) q ->
 P v q b a.
intros P v q b a H.
rewrite unfold_OUT.
intro H0.
simple inversion H0.
discriminate H2. 
rewrite <- H3.
rewrite
 (inj_Tfun c1 del v1 a p1 (ACK b) lnk1 f (fun _ : bool * A => OUT b a))
 .
assumption.
assumption.
intro.
absurd (c2 = lnk1).
assumption.
injection H2; trivial.
discriminate H2.
discriminate H2.
discriminate H2.
discriminate H3.
discriminate H3.
discriminate H3.
discriminate H3.
discriminate H3.
Defined.

Lemma OUT_UinvT1 :
 forall (P : Prop) (w : Signal _ Act lnk1) (q : Process) (b : bool) (a : A),
 UnrelProcTrans Channel Act lnk1 (OUT b a) (Transmit _ Act lnk1 w) q -> P.
intros P w q b a.
rewrite unfold_OUT.
intro H1.
inversion H1.
Defined.

Lemma OUT_UinvT2 :
 forall (P : Prop) (w : Signal _ Act lnk2) (q : Process) (b : bool) (a : A),
 UnrelProcTrans Channel Act lnk2 (OUT b a) (Transmit _ Act lnk2 w) q -> P.
intros P w q b a.
rewrite unfold_OUT.
intro H1.
inversion H1.
Defined.

Lemma State1 :
 forall (b : bool) (s : Stream A) (c : Channel) (w : Signal _ Act c)
   (q : Process),
 Trans c (SEND b s || ACKING (negb b)) (Transmit _ Act c w) q ->
 c = lnk1 /\ q = SENDING b s || OUT b (hd s) \/
 existS (Signal Channel Act) c w =
 existS (Signal Channel Act) lnk1 (Noise _ Act lnk1) /\
 q = SENDING b s || ACKING (negb b).

simple destruct c; simpl in |- *.
intros w q T.
 inversion T using PAR_UinvT.
   intros p3 p5 v UTL.                 (* SEND talks clear *)
   inversion UTL using SEND_UinvTC1.  
   intro UTR.
   inversion UTR using ACKING_UinvR. 
   rewrite (negb_elim b).
   rewrite (eqb_reflx b).
   auto. 

   intros p3 p5 v UTL UTR.             (* ACKING talks clear on lnk1 *)
   inversion UTR using ACKING_UinvT. 
  
   intros p3 UTL.                      (* SEND lost its message *)
   rewrite (SEND_ULoosed b s p3). 
   auto.
   assumption.

   intros p4 UTR.                      (* ACKING lost its message on lnk1 *)
   inversion UTR using ACKING_UinvT.  

intros w q T.
inversion T using PAR_UinvT.
   intros p3 p5 v UTL.                 (* SEND talks clear on lnk2 *)
   inversion UTL using SEND_UinvT2.  
   
   intros p3 p5 v UTL UTR.             (* ACKING talks clear on lnk2 *)
   inversion UTR using ACKING_UinvT. 
   
   intros p3 UTL.                      (* SEND losts ists message on lnk2 *)
   inversion UTL using SEND_UinvT2.   
   auto.

   intros p3 UTR.                      (* ACKING losts ists message on lnk2 *)
   inversion UTR using ACKING_UinvT. 

intros w q T.
inversion T using PAR_SinvT.
   intros p3 p5 v UTL.                 (* SEND talks clear on del *)
   inversion UTL using SEND_SinvT.  

   intros p3 p5 v UTL UTR.             (* ACKING talks clear on del *)
   inversion UTR using ACKING_SinvT. 
Defined.

Lemma State2 :
 forall (b : bool) (s : Stream A) (c : Channel) (w : Signal _ Act c)
   (q : Process),
 Trans c (SENDING b s || ACKING (negb b)) (Transmit _ Act c w) q ->
 c = lnk1 /\ q = SENDING b s || OUT b (hd s) \/
 existS (Signal Channel Act) c w =
 existS (Signal Channel Act) lnk1 (Noise _ Act lnk1) /\
 q = SENDING b s || ACKING (negb b).

simple destruct c; simpl in |- *.
intros w q T.
 inversion T using PAR_UinvT.
   intros p3 p5 v UTL.                 (* SENDING talks clear *)
   inversion UTL using SENDING_UinvTC1.  
   intro UTR.
   inversion UTR using ACKING_UinvR. 
   rewrite (negb_elim b).
   rewrite (eqb_reflx b).
   auto. 

   intros p3 p5 v UTL UTR.             (* ACKING talks clear on lnk1 *)
   inversion UTR using ACKING_UinvT. 
  
   intros p3 UTL.                      (* SENDING lost its message *)
   rewrite (SENDING_ULoosed b s p3). 
   auto.
   assumption.

   intros p4 UTR.                      (* ACKING lost its message on lnk1 *)
   inversion UTR using ACKING_UinvT.  

intros w q T.
inversion T using PAR_UinvT.
   intros p3 p5 v UTL.                 (* SENDING talks clear on lnk2 *)
   inversion UTL using SENDING_UinvT2.  
   
   intros p3 p5 v UTL UTR.             (* ACKING talks clear on lnk2 *)
   inversion UTR using ACKING_UinvT. 
   
   intros p3 UTL.                      (* SENDING losts ists message on lnk2 *)
   inversion UTL using SENDING_UinvT2.  

   intros p3 UTR.                      (* ACKING losts ists message on lnk2 *)
   inversion UTR using ACKING_UinvT. 

intros w q T.
inversion T using PAR_SinvT.
   intros p3 p5 v UTL.                 (* SENDING talks clear on del *)
   inversion UTL using SENDING_SinvT.  

   intros p3 p5 v UTL UTR.             (* ACKING talks clear on del *)
   inversion UTR using ACKING_SinvT. 
Defined.

Lemma State3 :
 forall (b : bool) (s : Stream A) (c : Channel) (w : Signal _ Act c)
   (q : Process),
 Trans c (SENDING b s || OUT b (hd s)) (Transmit _ Act c w) q ->
 c = lnk1 /\ q = SENDING b s || OUT b (hd s) \/
 existS (Signal Channel Act) c w =
 existS (Signal Channel Act) del (Clear _ Act del (hd s)) /\
 q = SENDING b s || ACK b.
simple destruct c; simpl in |- *.
intros w q T.
 inversion T using PAR_UinvT.
   intros p3 p5 v UTL.                 (* SENDING talks clear *)
   inversion UTL using SENDING_UinvTC1.  
   intro UTR.
   inversion UTR using OUT_UinvR. 
   auto. 

   intros p3 p5 v UTL UTR.             (* OUT talks clear on lnk1 *)
   inversion UTR using OUT_UinvT1. 
  
   intros p3 UTL.                      (* SENDING lost its message *)
   rewrite (SENDING_ULoosed b s p3). 
   auto.
   assumption.

   intros p4 UTR.                      (* OUT lost its message on lnk1 *)
   inversion UTR using OUT_UinvT1.  

intros w q T.
inversion T using PAR_UinvT.
   intros p3 p5 v UTL.                 (* SENDING talks clear on lnk2 *)
   inversion UTL using SENDING_UinvT2.  
   
   intros p3 p5 v UTL UTR.             (* OUT talks clear on lnk2 *)
   inversion UTR using OUT_UinvT2. 

   intros p3 UTL.                      (* SENDING losts ists message on lnk2 *)
   inversion UTL using SENDING_UinvT2.  

   intros p4 UTR.                     (* OUT losts ists message on lnk2 *)
   inversion UTR using OUT_UinvT2. 

intros w q T.
inversion T using PAR_SinvT.
   intros p3 p5 v UTL.                 (* SENDING talks clear on del *)
   inversion UTL using SENDING_SinvT.  

   intros p3 p5 v UTL UTR.             (* OUT talks clear on del *)
   inversion UTR using OUT_SinvT in UTL. 
   inversion UTL using SENDING_SinvR. 
   auto.   
Defined.


Lemma State4 :
 forall (b : bool) (s : Stream A) (c : Channel) (w : Signal _ Act c)
   (q : Process),
 Trans c (SENDING b s || ACK b) (Transmit _ Act c w) q ->
 c = lnk1 /\ q = SENDING b s || ACK b \/
 c = lnk2 /\ q = SEND (negb b) (tl s) || ACKING b \/
 existS (Signal Channel Act) c w =
 existS (Signal Channel Act) lnk2 (Noise _ Act lnk2) /\
 q = SENDING b s || ACKING b.

simple destruct c; simpl in |- *.
intros w q T.
 inversion T using PAR_UinvT.
   intros p3 p5 v UTL.                 (* SENDING talks clear *)
   inversion UTL using SENDING_UinvTC1.  
   intro UTR.
   inversion UTR using ACK_UinvR. 
   auto. 

   intros p3 p5 v UTL UTR.             (* ACK talks clear on lnk1 *)
   inversion UTR using ACK_UinvTC1. 
  
   intros p3 UTL.                      (* SENDING lost its message *)
   rewrite (SENDING_ULoosed b s p3). 
   auto.
   assumption.

   intros p4 UTR.                      (* ACK lost its message on lnk1 *)
   inversion UTR using ACK_UinvT1.  

intros w q T.
inversion T using PAR_UinvT.
   intros p3 p5 v UTL.                 (* SENDING talks clear on lnk2 *)
   inversion UTL using SENDING_UinvT2.  
   
   intros p3 p5 v UTL UTR.             (* ACK talks clear on lnk2 *)
   inversion UTR using ACK_UinvTC2 in UTL. 
   inversion UTL using SENDING_UinvR.  
   rewrite (eqb_reflx b).
   auto. 

   intros p3 UTL.                 (* SENDING losts ists message on lnk2 *)
   inversion UTL using SENDING_UinvT2.  

   intros p4 UTR.                      (* ACK lost its message on lnk2 *)
   rewrite (ACK_ULoosed b lnk2 p4).
   auto. 
   assumption.

intros w q T.
inversion T using PAR_SinvT.
   intros p3 p5 v UTL.                 (* SENDING talks clear on del *)
   inversion UTL using SENDING_SinvT.  

   intros p3 p5 v UTL UTR.             (* ACK talks clear on del *)
   inversion UTR using ACK_SinvT. 
Defined.


Lemma State5 :
 forall (b : bool) (s : Stream A) (c : Channel) (w : Signal _ Act c)
   (q : Process),
 Trans c (SENDING b s || ACKING b) (Transmit _ Act c w) q ->
 c = lnk1 /\ q = SENDING b s || ACK b \/
 existS (Signal Channel Act) c w =
 existS (Signal Channel Act) lnk1 (Noise _ Act lnk1) /\
 q = SENDING b s || ACKING b.

simple destruct c; simpl in |- *.
intros w q T.
 inversion T using PAR_UinvT.
   intros p3 p5 v UTL.                 (* SENDING talks clear *)
   inversion UTL using SENDING_UinvTC1.  
   intro UTR.
   inversion UTR using ACKING_UinvR. 
   rewrite (eqb_negb2 b). 
   auto. 

   intros p3 p5 v UTL UTR.             (* ACKING talks  *)
   inversion UTR using ACKING_UinvT. 
  
   intros p3 UTL.                      (* SENDING losts its message *)
   rewrite (SENDING_ULoosed b s p3). 
   auto.
   assumption.

   intros p4 UTR.                      (* ACKING  losts its  *)
   inversion UTR using ACKING_UinvT.  

intros w q T.
inversion T using PAR_UinvT.
   intros p3 p5 v UTL.                 (* SENDING talks clear on lnk2 *)
   inversion UTL using SENDING_UinvT2.  
   
   intros p3 p5 v UTL UTR.             (* ACKING talks  *)
   inversion UTR using ACKING_UinvT. 
  
   intros p3 UTL.                 (* SENDING losts ists message on lnk2 *)
   inversion UTL using SENDING_UinvT2.  

   intros p4 UTR.                      (* ACKING losts its message on lnk2 *)

   inversion UTR using ACKING_UinvT. 
   intros w q T.
   inversion T using PAR_SinvT.
   intros p3 p5 v UTL.                 (* SENDING talks clear on del *)
   inversion UTL using SENDING_SinvT.  

   intros p3 p5 v UTL UTR.             (* ACKING talks  *)
   inversion UTR using ACKING_SinvT. 
Defined.


