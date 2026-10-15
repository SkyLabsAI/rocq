(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Declare a hardcoded input head of an arithmetic reifier, returning its lazy
    reference and making it traversable by zify's discovery passes. Dump-only
    references must not be registered. *)
val register : string -> EConstr.t Lazy.t

(** Fold over registered references whose defining libraries are loaded. *)
val fold : (EConstr.t -> 'a -> 'a) -> 'a -> 'a
