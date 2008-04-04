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
(*        Description of the prtocol and its specification                  *)
(****************************************************************************)

Require Export Bool.
Require Export Streams.
Require Export abp.ABP.BISIMULATION.Processes.

Parameter A : Set.

Inductive Channel : Set :=
  | lnk1 : Channel
  | lnk2 : Channel
  | del : Channel.

Definition Act (c : Channel) :=
  match c with
  | lnk1 => (bool * A)%type
  | lnk2 => bool
  | del => A
  end.


(* Notation to forget general parameters. *)

Definition Process := ACProcess Channel Act.
(* <Warning> : Syntax is discontinued *)

Notation TALK := (ACTALK Channel Act) (only parsing).
(* <Warning> : Syntax is discontinued *)

Notation LISTEN := (ACLISTEN Channel Act) (only parsing).
(* <Warning> : Syntax is discontinued *)

Notation "c1 || c2" := (ACPAR Channel Act c1 c2).

Notation Action := (ACAction Channel Act).


CoFixpoint REPEAT  : Stream A -> Process :=
  fun s : Stream A =>
  ACTALK Channel Act del (hd s) (REPEAT (tl s)) del (fun _ : A => REPEAT s). 


CoFixpoint SEND  : bool -> Stream A -> Process :=
  fun (b : bool) (s : Stream A) =>
  ACTALK Channel Act lnk1 (b, hd s) (SENDING b s) lnk2
    (fun _ : bool => SEND b s)
 with SENDING  : bool -> Stream A -> Process :=
  fun (b : bool) (s : Stream A) =>
  ACTALK Channel Act lnk1 (b, hd s) (SENDING b s) lnk2
    (fun b1 : bool => if eqb b1 b then SEND (negb b) (tl s) else SEND b s).


CoFixpoint ACKING  : bool -> Process :=
  fun b : bool =>
  ACLISTEN Channel Act lnk1
    (fun ba : bool * A =>
     let (b1, a) := ba in if eqb b1 (negb b) then OUT (negb b) a else ACK b)
 with OUT  : bool -> A -> Process :=
  fun (b1 : bool) (a : A) =>
  ACTALK Channel Act del a (ACK b1) lnk1 (fun _ : bool * A => OUT b1 a)
 with ACK  : bool -> Process :=
  fun b : bool =>
  ACTALK Channel Act lnk2 b (ACKING b) lnk1 (fun _ : bool * A => ACK b).


Definition ABP (b : bool) (s : Stream A) := SEND b s || ACKING (negb b).