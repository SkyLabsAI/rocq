(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Static ML declarations, not proof-state registrations: entries must survive
   backtracking past the first load of the arithmetic plugin. *)
let heads = ref []

let register key =
  let head = lazy (
    EConstr.of_constr
      (UnivGen.constr_of_monomorphic_global (Global.env ()) (Rocqlib.lib_ref key)))
  in
  heads := (key, head) :: !heads;
  head

let fold f init =
  List.fold_left
    (fun acc (key, head) ->
      (* Do not force missing optional references: lazy values memoize failures,
         but a later import may make this reference available. *)
      if Rocqlib.has_ref key then f (Lazy.force head) acc else acc)
    init !heads
