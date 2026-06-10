(************************************************************************)
(* Test suite for the [#[params="N"]] attribute.                        *)
(*                                                                      *)
(* CONVENTION: every behavioural assertion is currently wrapped in      *)
(* [Fail], so this whole file compiles today against the SCAFFOLD       *)
(* (where [#[params]] is a no-op and nothing is recorded).  Each        *)
(* assertion is annotated:                                              *)
(*                                                                      *)
(*   (P) positive: should SUCCEED once implemented                      *)
(*       -> when we implement, drop the [Fail].                         *)
(*   (N) negative: should STAY failing even after implementation        *)
(*       -> keep the [Fail].                                            *)
(*                                                                      *)
(* Observable: [ParamsCheck c n] succeeds iff constant [c] is recorded  *)
(* with Params arity [n] (and errors otherwise).  The intended          *)
(* implementation records the arity AND registers it as a hint that is  *)
(* #[local] inside a section (hence does not persist verbatim), while a *)
(* corrected GLOBAL registration is installed at section close.         *)
(************************************************************************)

Require Import ParamsAttr.ParamsAttr.

(*======================================================================*)
(* A. Outside any section: arity is recorded verbatim and persists.     *)
(*======================================================================*)

#[params="3"] Definition idnat (x : nat) : nat := x.

Fail ParamsCheck idnat 3.   (* (P) arity 3 recorded globally *)
Fail ParamsCheck idnat 7.   (* (N) wrong arity *)

(*======================================================================*)
(* B. Section; definition uses BOTH implicit section variables and      *)
(*    leaves one section variable UNUSED.                               *)
(*    -> at End Section the arity is bumped by the number of section    *)
(*       variables ACTUALLY USED (2), not by all section variables (3). *)
(*======================================================================*)

Section Sec1.
  Context {A : Type}.        (* implicit section variable, used *)
  Context {B : Type}.        (* implicit section variable, used *)
  Variable unused : nat.     (* section variable NOT used by pairAB *)

  #[params="3"] Definition pairAB (x : A) (y : B) : A * B := (x, y).

  (* Inside the section the recorded arity is the literal 3. *)
  Fail ParamsCheck pairAB 3.   (* (P) in-section arity is 3 *)
End Sec1.

(* After cooking: pairAB : forall (A B : Type), A -> B -> A * B.
   It depends on A and B (2 variables); [unused] is not used. *)
Fail ParamsCheck pairAB 5.     (* (P) 3 + 2 used section vars = 5 *)
Fail ParamsCheck pairAB 3.     (* (N) the in-section (arity 3) registration was a
                                  #[local] hint and must NOT persist *)
Fail ParamsCheck pairAB 6.     (* (N) would be 6 only if the UNUSED section
                                  variable were (wrongly) counted *)

(*======================================================================*)
(* C. Section; definition uses only ONE of two section variables.       *)
(*======================================================================*)

Section Sec2.
  Context {A : Type}.
  Context {B : Type}.

  #[params="3"] Definition useA (x : A) : A := x.   (* uses A only, not B *)

  Fail ParamsCheck useA 3.   (* (P) in-section arity is 3 *)
End Sec2.

(* useA : forall (A : Type), A -> A. Depends on A only. *)
Fail ParamsCheck useA 4.   (* (P) 3 + 1 used section var = 4 *)
Fail ParamsCheck useA 5.   (* (N) B is unused, so not +2 *)
Fail ParamsCheck useA 3.   (* (N) in-section registration does not persist *)

(*======================================================================*)
(* D. Section; definition uses NO section variables (bump 0).           *)
(*    The global registration installed at section close keeps arity 3. *)
(*======================================================================*)

Section Sec3.
  Context {A : Type}.

  #[params="3"] Definition noDeps (x : nat) : nat := x.   (* no section vars used *)

  Fail ParamsCheck noDeps 3.   (* (P) in-section arity is 3 *)
End Sec3.

Fail ParamsCheck noDeps 3.   (* (P) persists with arity 3 (0 section vars used) *)

(*======================================================================*)
(* E. Locality: a registration made inside a section does not leak out  *)
(*    while the section is still open elsewhere.  Here we check that     *)
(*    after closing Sec1/Sec2 above, the old in-section arities are gone *)
(*    (covered by the (N) lines in B and C), and that re-opening a       *)
(*    section does not see stale entries.                                *)
(*======================================================================*)

Section Sec4.
  Context {A : Type}.

  (* Nothing recorded for [pairAB] at its OLD in-section arity should be
     visible here either. *)
  Fail ParamsCheck pairAB 3.   (* (N) never persists at arity 3 *)

  #[params="2"] Definition local_in_sec (x : A) : A := x.
  Fail ParamsCheck local_in_sec 2.   (* (P) visible inside its own section *)
End Sec4.

(* local_in_sec : forall A, A -> A; uses A (1 var) => 2 + 1 = 3 after close. *)
Fail ParamsCheck local_in_sec 3.   (* (P) persisted, bumped to 3 *)
Fail ParamsCheck local_in_sec 2.   (* (N) in-section arity 2 does not persist *)
