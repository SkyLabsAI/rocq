(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Avoid deep borrow-chain call stacks in the untrusted integer frontend. *)
val pred_double : Micromega.positive -> Micromega.positive
val sub : Micromega.z -> Micromega.z -> Micromega.z

(** Same normalization and CNF as [Micromega.cnfZ], using stack-safe
    subtraction. The certificate format and verified checker are unchanged. *)
val cnf : Micromega.kind ->
  (Micromega.z Micromega.formula, 'a, 'b, 'c) Micromega.tFormula ->
  (Micromega.z Micromega.nFormula, 'a) Micromega.cnf * 'a Micromega.trace
