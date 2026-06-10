(************************************************************************)
(* Standalone plugin: a programmable [#[params="N"]] attribute.         *)
(*                                                                      *)
(* Intended semantics (NOT yet implemented — see the test suite):       *)
(*                                                                      *)
(*   #[params="N"] Definition c ... .                                   *)
(*                                                                      *)
(* records that constant [c] has [Params] arity [N] and registers the   *)
(* corresponding [Params c N] as a hint.                                *)
(*                                                                      *)
(*   - Outside a section: registered globally with arity [N].           *)
(*   - Inside a section:  registered as a #[local] hint (does NOT        *)
(*     persist past [End Section]); when the section closes and [c] is   *)
(*     cooked, a fresh GLOBAL registration is installed for the cooked   *)
(*     constant with arity [N + k], where [k] is the number of section   *)
(*     variables actually used by [c] (= [Array.length                  *)
(*     (Global.section_instance c)]).                                    *)
(*                                                                      *)
(* THIS FILE IS CURRENTLY A SCAFFOLD/STUB:                              *)
(*   - the [params_table] below is the source of truth for the recorded *)
(*     arity, queried by the [ParamsCheck] command (test observable);   *)
(*   - the [#[params="N"]] attribute is a NO-OP (it parses and is        *)
(*     accepted so that definitions compile, but records nothing).      *)
(* The actual registration + section-discharge logic will be filled in  *)
(* once the test suite is confirmed.                                    *)
(************************************************************************)

(* Source of truth for recorded [Params] arities (test observable). *)
let params_table : int Names.GlobRef.Map.t ref =
  Summary.ref ~name:"params-attr-table" Names.GlobRef.Map.empty

(* Test-only query command: [ParamsCheck r n] succeeds iff the recorded
   arity for [r] equals [n], and errors otherwise (including when nothing is
   recorded for [r]).  Used by the test suite to assert behaviour. *)
let check_arity (r : Libnames.qualid) (n : int) : unit =
  let gr = Smartlocate.global_with_alias r in
  match Names.GlobRef.Map.find_opt gr !params_table with
  | Some m when Int.equal m n ->
    Feedback.msg_notice
      Pp.(str "Params " ++ Names.GlobRef.print gr ++ str " " ++ int n)
  | Some m ->
    CErrors.user_err
      Pp.(str "Params arity for " ++ Names.GlobRef.print gr ++ str " is "
          ++ int m ++ str ", expected " ++ int n ++ str ".")
  | None ->
    CErrors.user_err
      Pp.(str "No Params arity recorded for " ++ Names.GlobRef.print gr ++ str ".")

(* The [#[params="N"]] attribute — currently a NO-OP that just consumes the
   "params" key so that annotated definitions still compile. *)
let params_attribute : Declare.Hook.t list Attributes.attribute =
  let open Attributes in
  let parser ?loc:_ _prev _v = () in
  Notations.map (fun _ -> []) (attribute_of_list ["params", parser])

let params_token =
  Vernacentries.DefAttributes.Observer.register
    ~name:"params-attribute" params_attribute

let () = Vernacentries.DefAttributes.Observer.activate params_token
