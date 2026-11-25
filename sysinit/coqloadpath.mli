(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Initial load paths for Rocq runtime libraries and loose theories from
    [ROCQPATH] and [XDG_DIRS]. Findlib packages are added separately. *)
val init_load_path
  : coqenv:Boot.Env.t
  -> CUnix.physical_path list * Loadpath.vo_path list
