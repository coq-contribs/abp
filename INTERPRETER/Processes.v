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
Section Processes.

Variable Chnl : Set.
Variable A : Chnl -> Set.

CoInductive Guarded : Set :=
  | TALK :
      forall c1 : Chnl,
      A c1 -> Guarded -> forall c2 : Chnl, (A c2 -> Guarded) -> Guarded
  | LISTEN : forall c : Chnl, (A c -> Guarded) -> Guarded.               

Inductive Process : Set :=
  | INJ : Guarded -> Process
  | PAR : Process -> Process -> Process.

Coercion INJ : Guarded >-> Process.


(* Semantics of processes *)

Section Semantics.

Variable c : Chnl.

Inductive Signal : Set :=
  | Noise : Signal
  | Clear : A c -> Signal.


Inductive Action : Set :=
  | Transmit : Signal -> Action
  | Receive : A c -> Action.


Coercion Transmit : Signal >-> Action.

 Inductive SafeProcTrans : Process -> Action -> Process -> Prop :=
   | sttalk1 :
       forall (v : A c) (c2 : Chnl) (f : A c2 -> Guarded) (p : Guarded),
       SafeProcTrans (TALK c v p c2 f) (Clear v) p
   | sttalk2 :
       forall (c1 : Chnl) (v1 : A c1) (f : A c -> Guarded) 
         (p1 p2 : Guarded) (v : A c),
       f v = p2 -> SafeProcTrans (TALK c1 v1 p1 c f) (Receive v) p2
   | sttalk3 :
       forall (c1 c2 : Chnl) (v1 : A c1) (f : A c2 -> Guarded) 
         (p : Guarded) (v2 : A c),
       c2 <> c ->
       SafeProcTrans (TALK c1 v1 p c2 f) (Receive v2) (TALK c1 v1 p c2 f)
   | stlisten1 :
       forall (f : A c -> Guarded) (v : A c) (p1 p2 : Guarded),
       f v = p2 -> SafeProcTrans (LISTEN c f) (Receive v) p2
   | stlisten2 :
       forall (d : Chnl) (f : A d -> Guarded) (v : A c),
       d <> c -> SafeProcTrans (LISTEN d f) (Receive v) (LISTEN d f)
   | stpar1 :
       forall (p1 p2 p3 p4 : Process) (v : A c),
       SafeProcTrans p1 (Transmit (Clear v)) p2 ->
       SafeProcTrans p3 (Receive v) p4 ->
       SafeProcTrans (PAR p1 p3) (Clear v) (PAR p2 p4)
   | stpar2 :
       forall (p1 p2 p3 p4 : Process) (v : A c),
       SafeProcTrans p1 (Receive v) p2 ->
       SafeProcTrans p3 (Clear v) p4 ->
       SafeProcTrans (PAR p1 p3) (Clear v) (PAR p2 p4)
   | stpar3 :
       forall (p1 p2 p3 p4 : Process) (v : A c),
       SafeProcTrans p1 (Receive v) p2 ->
       SafeProcTrans p3 (Receive v) p4 ->
       SafeProcTrans (PAR p1 p3) (Receive v) (PAR p2 p4).

 
 Inductive UnrelProcTrans : Process -> Action -> Process -> Prop :=
   | uttalk1 :
       forall (v : A c) (c2 : Chnl) (f : A c2 -> Guarded) (p : Guarded),
       UnrelProcTrans (TALK c v p c2 f) (Clear v) p
   | uttalk2 :
       forall (c1 : Chnl) (v1 : A c1) (f : A c -> Guarded) 
         (p1 p2 : Guarded) (v : A c),
       f v = p2 -> UnrelProcTrans (TALK c1 v1 p1 c f) (Receive v) p2
   | uttalk3 :
       forall (c1 : Chnl) (v1 : A c1) (c2 : Chnl) (f : A c2 -> Guarded)
         (p : Guarded) (v2 : A c),
       c2 <> c ->
       UnrelProcTrans (TALK c1 v1 p c2 f) (Receive v2) (TALK c1 v1 p c2 f)
   | uttalk4 :
       forall (v : A c) (c2 : Chnl) (f : A c2 -> Guarded) (p : Guarded),
       UnrelProcTrans (TALK c v p c2 f) Noise p
   | utlisten1 :
       forall (f : A c -> Guarded) (v : A c) (p : Guarded),
       f v = p -> UnrelProcTrans (LISTEN c f) (Receive v) p
   | utlisten2 :
       forall (d : Chnl) (f : A d -> Guarded) (v : A c),
       d <> c -> UnrelProcTrans (LISTEN d f) (Receive v) (LISTEN d f)
   | utpar1 :
       forall (p1 p2 p3 p4 : Process) (v : A c),
       UnrelProcTrans p1 (Clear v) p2 ->
       UnrelProcTrans p3 (Receive v) p4 ->
       UnrelProcTrans (PAR p1 p3) (Clear v) (PAR p2 p4)
   | utpar2 :
       forall (p1 p2 p3 p4 : Process) (v : A c),
       UnrelProcTrans p1 (Receive v) p2 ->
       UnrelProcTrans p3 (Clear v) p4 ->
       UnrelProcTrans (PAR p1 p3) (Clear v) (PAR p2 p4)
   | utpar3 :
       forall (p1 p2 p3 p4 : Process) (v : A c),
       UnrelProcTrans p1 (Receive v) p2 ->
       UnrelProcTrans p3 (Receive v) p4 ->
       UnrelProcTrans (PAR p1 p3) (Receive v) (PAR p2 p4)
   | utpar4 :
       forall p1 p2 p3 p4 : Process,
       UnrelProcTrans p1 Noise p2 ->
       UnrelProcTrans (PAR p1 p3) Noise (PAR p2 p4)
   | utpar5 :
       forall p1 p2 p3 p4 : Process,
       UnrelProcTrans p3 Noise p4 ->
       UnrelProcTrans (PAR p1 p3) Noise (PAR p2 p4).


End Semantics.

End Processes.


