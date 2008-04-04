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
(*                              Processwc.v                                 *)
(****************************************************************************)
(*                                                                          *)
(*              A verification of the Alternating Bit Protocol              *)
(*                              using  CBS                                  *)
(*                                                                          *)
(*                           Eduardo Gimenez                                *)
(*                                                                          *)
(****************************************************************************)

Require Import Streams.

(********************)
  Section Processes.
(********************)


Variable Chnl : Set.
Variable A : Chnl -> Set.

CoInductive ACProcess : Set :=
  | ACTALK :
      forall c1 : Chnl,
      A c1 -> ACProcess -> forall c2 : Chnl, (A c2 -> ACProcess) -> ACProcess
  | ACLISTEN : forall c : Chnl, (A c -> ACProcess) -> ACProcess
  | ACPAR : ACProcess -> ACProcess -> ACProcess.


Lemma unfold_process :
 forall x : ACProcess,
 x =
 match x with
 | ACTALK x x0 x1 x2 x3 => ((((ACTALK x) x0) x1) x2) x3
 | ACLISTEN x x0 => (ACLISTEN x) x0
 | ACPAR x x0 => (ACPAR x) x0
 end.
simple destruct x.
trivial.
trivial.
trivial.
Defined.

(*********************************)
  Section Semantics_of_ACProcesses.
(*********************************)

Variable c : Chnl.

Inductive Signal : Set :=
  | Noise : Signal
  | Clear : A c -> Signal.


Inductive ACAction : Set :=
  | Transmit : Signal -> ACAction
  | Receive : A c -> ACAction.


(* Coercion Transmit : Signal>-> ACAction *)

 Inductive SafeProcTrans : ACProcess -> ACAction -> ACProcess -> Prop :=
   | sttalk1 :
       forall (v : A c) (c2 : Chnl) (f : A c2 -> ACProcess) (p : ACProcess),
       SafeProcTrans (ACTALK c v p c2 f) (Transmit (Clear v)) p
   | sttalk2 :
       forall (c1 : Chnl) (v1 : A c1) (f : A c -> ACProcess)
         (p1 p2 : ACProcess) (v : A c),
       f v = p2 -> SafeProcTrans (ACTALK c1 v1 p1 c f) (Receive v) p2
   | sttalk3 :
       forall (c1 c2 : Chnl) (v1 : A c1) (f : A c2 -> ACProcess)
         (p : ACProcess) (v2 : A c),
       c2 <> c ->
       SafeProcTrans (ACTALK c1 v1 p c2 f) (Receive v2) (ACTALK c1 v1 p c2 f)
   | stlisten1 :
       forall (f : A c -> ACProcess) (v : A c) (p1 p2 : ACProcess),
       f v = p2 -> SafeProcTrans (ACLISTEN c f) (Receive v) p2
   | stlisten2 :
       forall (d : Chnl) (f : A d -> ACProcess) (v : A c),
       d <> c -> SafeProcTrans (ACLISTEN d f) (Receive v) (ACLISTEN d f)
   | stpar1 :
       forall (p1 p2 p3 p4 : ACProcess) (v : A c),
       SafeProcTrans p1 (Transmit (Clear v)) p2 ->
       SafeProcTrans p3 (Receive v) p4 ->
       SafeProcTrans (ACPAR p1 p3) (Transmit (Clear v)) (ACPAR p2 p4)
   | stpar2 :
       forall (p1 p2 p3 p4 : ACProcess) (v : A c),
       SafeProcTrans p1 (Receive v) p2 ->
       SafeProcTrans p3 (Transmit (Clear v)) p4 ->
       SafeProcTrans (ACPAR p1 p3) (Transmit (Clear v)) (ACPAR p2 p4)
   | stpar3 :
       forall (p1 p2 p3 p4 : ACProcess) (v : A c),
       SafeProcTrans p1 (Receive v) p2 ->
       SafeProcTrans p3 (Receive v) p4 ->
       SafeProcTrans (ACPAR p1 p3) (Receive v) (ACPAR p2 p4).

 
 Inductive UnrelProcTrans : ACProcess -> ACAction -> ACProcess -> Prop :=
   | uttalk1 :
       forall (v : A c) (c2 : Chnl) (f : A c2 -> ACProcess) (p : ACProcess),
       UnrelProcTrans (ACTALK c v p c2 f) (Transmit (Clear v)) p
   | uttalk2 :
       forall (c1 : Chnl) (v1 : A c1) (f : A c -> ACProcess) 
         (p1 : ACProcess) (v : A c),
       UnrelProcTrans (ACTALK c1 v1 p1 c f) (Receive v) (f v)
   | uttalk3 :
       forall (c1 : Chnl) (v1 : A c1) (c2 : Chnl) (f : A c2 -> ACProcess)
         (p : ACProcess) (v2 : A c),
       c2 <> c ->
       UnrelProcTrans (ACTALK c1 v1 p c2 f) (Receive v2)
         (ACTALK c1 v1 p c2 f)
   | uttalk4 :
       forall (v : A c) (c2 : Chnl) (f : A c2 -> ACProcess) (p : ACProcess),
       UnrelProcTrans (ACTALK c v p c2 f) (Transmit Noise) p
   | utlisten1 :
       forall (f : A c -> ACProcess) (v : A c) (p : ACProcess),
       f v = p -> UnrelProcTrans (ACLISTEN c f) (Receive v) p
   | utlisten2 :
       forall (d : Chnl) (f : A d -> ACProcess) (v : A c),
       d <> c -> UnrelProcTrans (ACLISTEN d f) (Receive v) (ACLISTEN d f)
   | utpar1 :
       forall (p1 p2 p3 p4 : ACProcess) (v : A c),
       UnrelProcTrans p1 (Transmit (Clear v)) p2 ->
       UnrelProcTrans p3 (Receive v) p4 ->
       UnrelProcTrans (ACPAR p1 p3) (Transmit (Clear v)) (ACPAR p2 p4)
   | utpar2 :
       forall (p1 p2 p3 p4 : ACProcess) (v : A c),
       UnrelProcTrans p1 (Receive v) p2 ->
       UnrelProcTrans p3 (Transmit (Clear v)) p4 ->
       UnrelProcTrans (ACPAR p1 p3) (Transmit (Clear v)) (ACPAR p2 p4)
   | utpar3 :
       forall (p1 p2 p3 p4 : ACProcess) (v : A c),
       UnrelProcTrans p1 (Receive v) p2 ->
       UnrelProcTrans p3 (Receive v) p4 ->
       UnrelProcTrans (ACPAR p1 p3) (Receive v) (ACPAR p2 p4)
   | utpar4 :
       forall p1 p2 p3 : ACProcess,
       UnrelProcTrans p1 (Transmit Noise) p2 ->
       UnrelProcTrans (ACPAR p1 p3) (Transmit Noise) (ACPAR p2 p3)
   | utpar5 :
       forall p1 p2 p3 : ACProcess,
       UnrelProcTrans p2 (Transmit Noise) p3 ->
       UnrelProcTrans (ACPAR p1 p2) (Transmit Noise) (ACPAR p1 p3).

End Semantics_of_ACProcesses.


Section Properties_of_Processes.

 
Variable
  Trans : forall c : Chnl, ACProcess -> ACAction c -> ACProcess -> Prop.

CoInductive Discourse : Set :=
    Disc : forall c : Chnl, Signal c -> Discourse -> Discourse.

Section Basics.

Variable P : ACProcess -> Discourse -> Prop. 

Inductive Evt : ACProcess -> Discourse -> Prop :=
    notyet :
      forall (q : ACProcess) (c : Chnl) (w : Signal c) 
        (s : Discourse) (p : ACProcess),
      Trans c p (Transmit c w) q ->
      (forall q : ACProcess,
       Trans c p (Transmit c w) q -> ~ P p (Disc c w s) -> Evt q s) ->
      Evt p (Disc c w s). 

Theorem Evt_stable :
 forall (p : ACProcess) (ss : Discourse) (c : Chnl) 
   (w : Signal c) (q : ACProcess),
 Trans c p (Transmit c w) q ->
 ~ P p (Disc c w ss) -> Evt p (Disc c w ss) -> Evt q ss.
intros.
inversion H1.
apply H7.
change
  ((fun cw1 : sigS Signal =>
    let (c, w1) return Prop := cw1 in Trans c p (Transmit c w1) q)
     (existS _ c w1)) in |- *.
dependent rewrite H3.
assumption.
simpl in H0.
change
  ((fun cw1 : sigS Signal =>
    let (c, w1) return Prop := cw1 in ~ P p (Disc c w1 ss)) 
     (existS _ c w1)) in |- *.
dependent rewrite H3.
assumption.
Qed.

CoInductive Always : ACProcess -> Discourse -> Prop :=
    always :
      forall (c : Chnl) (w : Signal c) (s : Discourse) (p : ACProcess),
      P p (Disc c w s) ->
      (forall q : ACProcess, Trans c p (Transmit c w) q -> Always q s) ->
      Always p (Disc c w s). 

Theorem Always_stable :
 forall (p : ACProcess) (ss : Discourse) (c : Chnl) 
   (w : Signal c) (q : ACProcess),
 Trans c p (Transmit c w) q -> Always p (Disc c w ss) -> Always q ss.

intros.
inversion H0.
apply H6.
change
  ((fun cw1 : sigS Signal =>
    let (c, w1) return Prop := cw1 in Trans c p (Transmit c w1) q)
     (existS _ c w1)) in |- *.
dependent rewrite H2.
assumption.
Defined.


End Basics.

Section Parametric_Always.

Variable B : Set.
Variable Q : B -> ACProcess -> Discourse -> Prop. 


Inductive Wittness (a : B) (pn : ACProcess) (rs : Discourse) :
ACProcess -> Discourse -> Prop :=
  | goback :
      forall (p : ACProcess) (ss : Discourse) (c : Chnl) 
        (w : Signal c) (q : ACProcess),
      Trans c p (Transmit c w) q ->
      ~ Q a pn (Disc c w ss) ->
      Wittness a pn rs q ss -> Wittness a pn rs p (Disc c w ss)
  | start :
      forall (cn : Chnl) (wn : Signal cn) (p : ACProcess),
      Trans cn p (Transmit cn wn) pn ->
      Q a pn (Disc cn wn rs) -> Wittness a pn rs p (Disc cn wn rs).


CoInductive PAlways : Stream B -> ACProcess -> Discourse -> Prop :=
    palways :
      forall (s : Stream B) (ss : Discourse) (p : ACProcess),
      Evt (Q (hd s)) p ss ->
      (forall (q : ACProcess) (ss1 : Discourse),
       Wittness (hd s) q ss1 p ss -> PAlways (tl s) q ss1) -> 
      PAlways s p ss. 


Variable P : ACProcess -> Discourse -> Prop. 

Theorem StillHappens :
 forall (a : B) (p : ACProcess) (ss : Discourse) (q : ACProcess)
   (ss1 : Discourse),
 Wittness a q ss1 p ss -> Always P p ss -> Always P q ss1.
intros a p ss q ss1 H; elim H.
intros.
apply H3.
apply (Always_stable P p0 ss0 c w q0).
assumption.
assumption.
intros.
apply (Always_stable P p0 ss1 cn wn q).
assumption. 
assumption.
Qed.

End Parametric_Always.


End Properties_of_Processes.
  
End Processes.

