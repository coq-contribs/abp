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
Require Import abp.INTERPRETER.Processes.


Section Lists.
Variable A : Set.
CoInductive List : Set :=
  | NIL : List
  | CONS : A -> List -> List.
End Lists.

Section Interpreter.

Variable Chnl : Set.
Variable compare : forall c1 c2 : Chnl, {c1 = c2} + {c1 <> c2}.

Variable A : Chnl -> Set.


Inductive Pointer : Set :=
  | Succ : Pointer
  | Fail : Pointer
  | Left : Pointer -> Pointer
  | Right : Pointer -> Pointer. 



Inductive Wright : Process Chnl A -> Pointer -> Prop :=
  | wright_s :
      forall (c1 : Chnl) (v : A c1) (c2 : Chnl) (f : A c2 -> Guarded Chnl A)
        (p : Guarded Chnl A), Wright (TALK Chnl A c1 v p c2 f) Succ
  | wright_f :
      forall (c1 : Chnl) (v : A c1) (c2 : Chnl) (f : A c2 -> Guarded Chnl A)
        (p : Guarded Chnl A), Wright (TALK Chnl A c1 v p c2 f) Fail
  | wright_r :
      forall (p1 p2 : Process Chnl A) (o : Pointer),
      Wright p2 o -> Wright (PAR Chnl A p1 p2) (Right o)
  | wright_l :
      forall (p1 p2 : Process Chnl A) (o : Pointer),
      Wright p1 o -> Wright (PAR Chnl A p1 p2) (Left o). 



Inductive Result (o : Pointer) (p : Process Chnl A) : Set :=
  | Tuple :
      forall (c : Chnl) (w : Signal Chnl A c) (q : Process Chnl A),
      UnrelProcTrans Chnl A c p w q -> Result o p
  | Error : ~ Wright p o -> Result o p.


CoInductive Trace : List Pointer -> Process Chnl A -> Set :=
  | Stop : forall p : Process Chnl A, Trace (NIL Pointer) p
  | Evolve :
      forall (o : Pointer) (x : List Pointer) (c : Chnl)
        (p q : Process Chnl A) (w : Signal Chnl A c),
      UnrelProcTrans Chnl A c p w q -> Trace x q -> Trace (CONS _ o x) p
  | Refuse :
      forall (o : Pointer) (x : List Pointer) (p : Process Chnl A),
      ~ Wright p o -> Trace x p -> Trace (CONS _ o x) p.



Lemma listen :
 forall (p : Process Chnl A) (c : Chnl) (v : A c),
 {q : Process Chnl A | UnrelProcTrans Chnl A c p (Receive _ _ c v) q}.
fix 1.
simple destruct p.
simple destruct g.
(* It's a TALK process *) 
intros c1 a0 p0 c2 f c0.
case (compare c2 c0).
intros H.
pattern c0 in |- *.
case H.
intros.
exists (INJ Chnl A (f v)).
apply uttalk2.
trivial.
intros.
exists (INJ Chnl A (TALK Chnl A c1 a0 p0 c2 f)).
apply uttalk3.
assumption.
(* It's a LISTEN process *)
intros c p0 c0.
case (compare c c0).
intros H.
pattern c0 in |- *.
case H.
intros.
exists (INJ Chnl A (p0 v)).
apply utlisten1.
trivial.
intros.
exists (INJ Chnl A (LISTEN Chnl A c p0)).
apply utlisten2.
assumption.
(* It's a PAR process *)
intros.
case (listen p0 c v).
intros.
case (listen p1 c v).
intros.
exists (PAR Chnl A x x0).
apply utpar3.
assumption. 
assumption.
Defined.
 


Lemma say : forall (o : Pointer) (p : Process Chnl A), Result o p.   
fix 1.
simple destruct p.
simple destruct g.
case o.

intros c1 a0 p0 c2 p1.
apply (Tuple Succ (TALK Chnl A c1 a0 p0 c2 p1) c1 (Noise Chnl A c1) p0).
apply uttalk4.


intros c1 a0 p0 c2 p1.
apply (Tuple Fail (TALK Chnl A c1 a0 p0 c2 p1) c1 (Clear Chnl A c1 a0) p0).
apply uttalk1.

intros.
apply Error.
red in |- *.
intro.
inversion_clear H.

intros.
apply Error.
red in |- *.
intro.
inversion_clear H.
 
intros.
apply Error.
red in |- *.
intro.
inversion_clear H.

case o.

intros.
apply Error.
red in |- *.
intro.
inversion_clear H.

intros.
apply Error.
red in |- *.
intro.
inversion_clear H.

(* The left one listens *)
intros ol p0 p1.
case (say ol p0).
simple destruct w.
(* It's Noise *)
intros q H0.
apply
 (Tuple (Left ol) (PAR Chnl A p0 p1) c (Noise Chnl A c) (PAR Chnl A q p1)).
apply utpar4. 
assumption.
(* It's Clear v *) 
intros a q H0.
case (listen p1 c a).
intros.
apply
 (Tuple (Left ol) (PAR Chnl A p0 p1) c (Clear Chnl A c a) (PAR Chnl A q x)).
apply utpar1.
assumption.
assumption.
(* It was a bad pointer *)
intros.
apply Error.
red in |- *.
intro H.
inversion_clear H.
absurd (Wright p0 ol).
assumption.
assumption.
(* The right one listens *)
intros or p0 p1.
case (say or p1).
simple destruct w.
(* It's Noise *)
intros.
apply
 (Tuple (Right or) (PAR Chnl A p0 p1) c (Noise Chnl A c) (PAR Chnl A p0 q)).
apply utpar5.
assumption.
(* It's Clear v *) 
intros a q H0.
case (listen p0 c a).
intros.
apply
 (Tuple (Right or) (PAR Chnl A p0 p1) c (Clear Chnl A c a) (PAR Chnl A x q)).
apply utpar2.
assumption.
assumption.
(* It was a bad pointer *)
intros.
apply Error.
red in |- *.
intro H.
inversion_clear H.
absurd (Wright p1 or).
assumption.
assumption.
Defined.


Theorem simulator : forall (x : List Pointer) (p : Process Chnl A), Trace x p.
cofix.
intros x p.
case x.
apply Stop.
intros o y.
case (say o p).
intros c w q H0.
apply (Evolve o y c p q w).
assumption.
apply simulator.
intros H.
apply (Refuse o y p).
assumption.
apply simulator.
Defined.

End Interpreter.

(*
Require Extraction.
Write Gofer File "raugh" [simulator].
*)
