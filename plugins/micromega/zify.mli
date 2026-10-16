(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

module Reify : sig
  (** Declare a hardcoded input head of an arithmetic reifier, returning its lazy
      reference and making it traversable by zify's discovery passes. Dump-only
      references must not be registered. *)
  val register : string -> EConstr.t Lazy.t

  (** Fold over registered references whose defining libraries are loaded. *)
  val fold : (EConstr.t -> 'a -> 'a) -> 'a -> 'a
end

val zify_register_locality : Hints.hint_locality Attributes.attribute

module type S = sig
  val register : Hints.hint_locality -> Libnames.qualid -> unit
  val print : unit -> unit
end

module InjTable : S
module UnOp : S
module BinOp : S
module CstOp : S
module BinRel : S
module PropBinOp : S
module PropUnOp : S
module BinOpSpec : S
module UnOpSpec : S
module Saturate : S

val zify_tac : unit Proofview.tactic
val saturate : unit Proofview.tactic
val iter_specs : unit Proofview.tactic
val iter_let : Ltac_plugin.Tacinterp.Value.t -> unit Proofview.tactic
val elim_let : unit Proofview.tactic
