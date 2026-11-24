(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Rocq runtime enviroment API.

This module provides functions for manipulation of Rocq's runtime
enviroment, including the standard directories and support files.

This API is similar in spirit to findlib's or dune-sites API,
see their documentation for more information:

- http://projects.camlcity.org/projects/dl/findlib-1.9.1/doc/ref-html/lib/index.html
- https://dune.readthedocs.io/en/stable/sites.html#sites

It is important that this library has a minimal dependency set.

The Rocq runtime enviroment needs to be properly initialized before use;
we detail the rules below. It is recommended that applications requiring
multiple accesses to the environment, do initialize it once and keep a ref
to it. We don't forbid yet double initialization, (second time is a noop)
but we may do so in the future. Rules for "coqlib" are:

- the [ROCQLIB] env variable will be used if set
- both findlib-style roots containing [rocq.d/Init/Prelude.vo] and legacy
  roots containing [theories/Init/Prelude.vo] are accepted
- if [ROCQLIB] is not set, the findlib-style [rocq-core] package is preferred,
  followed by the configured legacy locations
- if none of the above succeeds, the initialization will fail

- The [ROCQRUNTIMELIB] env variable is also used if set. Otherwise, the
  [rocq-runtime] package is assumed to be next to the selected library root,
  except if [ROCQLIB/plugins] exists as in some developer layouts, in which
  case [ROCQRUNTIMELIB:=ROCQLIB].

Note that [set_coqlib] is used by some commands to process the [-coqlib] option,
as of now this sets both [coqlib] and [coqcorelib]; this part of the initialization
will be eventually moved here.

The error handling policy of this module is simple for now: failing to
initialize Rocq's env will produce a fatal error, and the application will exit with
code 1. No error handling is thus required on the client yet.

*)

module Path : sig

  (** This API is loosely inspired by [Stdune.Path], for now we keep
     it minimal, but at some point we may extend it. *)

  (** Paths are private, and owned by the functions below *)
  type t

  (** [relative path string] build a path relative to an existing one *)
  val relative : t -> string -> t

  (** We should gradually add some more functions to handle common dirs
      here such the theories directories or share files. Abstracting it
      hereere does allow to use system-specific functionalities *)

  (** [exists file] checks if [file] exists *)
  val exists : t -> bool

  (** String representation *)
  val to_string : t -> string

end

(** A physical standard-library root and its Rocq logical path. *)
type standard_library =
  { physical_path : Path.t
  ; logical_path : string
  }

(** Rocq runtime enviroment, including location of Rocq's Corelib *)
type t

type maybe_env =
  | Env of t
  | Boot

(** Returns [None] if the environment has not been initialized. *)
val initialized : unit -> maybe_env option

(** Init, possibly with a user provided coqlib *)
val init_with : coqlib:string option -> t

(** Init if boot:false, possibly with a user provided coqlib.
    Incompatible arguments run [warn_ignored_coqlib] (ie with boot:true and coqlib:Some) *)
val maybe_init : warn_ignored_coqlib:(unit -> unit) ->
  boot:bool -> coqlib:string option -> maybe_env

(** Usual messsage used for warn_ignored_coqlib *)
val ignored_coqlib_msg : string

(** If the query list is empty, behave as [maybe_init].
    Otherwise, print the queries.

    If the [usage] argument is [None], the queries must not be PrintHelp.

    If a query needs an environment, [boot] must not be [true].
    If there are queries and none need an environment,
    returns [Ok Boot] even if [boot] was [false].
*)
val print_queries_maybe_init : warn_ignored_coqlib:(unit -> unit) ->
  boot:bool -> coqlib:string option ->
  Usage.specific_usage option -> Usage.query list -> (maybe_env, string) result

(** [Corelib directory] *)
val corelib : t -> Path.t

(** [plugins directory] *)
val plugins : t -> Path.t

(** [user contrib directory] *)
val user_contrib : t -> Path.t

(** Standard-library roots that are available without [-package]. *)
val standard_libraries : t -> standard_library list

(** [tool-specific directory] *)
val tool : t -> string -> Path.t

(** .cmi files needed for native compilation *)
val native_cmi : t -> string -> Path.t

(** The location of the revision file *)
val revision : t -> Path.t

(** rocq-runtime/lib directory, not sure if to keep this *)
val runtimelib : t -> Path.t

(** Selected Rocq library root. This is [lib/rocq-core] for a findlib-style
    installation and [lib/coq] for a legacy installation. *)
val coqlib : t -> Path.t

(** [camlfind ()] is the path to the ocamlfind binary. *)
val ocamlfind : unit -> string

val print_config : ?prefix_var_name:string -> t -> out_channel -> unit

val relocate : Coq_config.relocatable_path -> string

val rocqbin : string
