open Names

(* The [#[size=N]] hook records the parsed integer to a file so the test
   harness can diff it against a checked-in reference (see misc/attributes.sh).
   This mirrors the [tc_declaration_observer] test: writing to a file rather
   than [Feedback.msg_info] keeps the compared output free of banners and
   location-dependent noise. The file is (re)created when the plugin loads. *)
let size_oc = open_out "size.out"

let print_hook =
  let attr : Declare.Hook.t list Attributes.attribute =
    let hook = Declare.Hook.make @@ fun data ->
      Feedback.msg_info Pp.(str "generated " ++ GlobRef.print data.dref ++ str "\n")
    in
    let open Attributes in
    let open Attributes.Notations in
    map (Option.default []) @@ attribute_of_list [("print", fun ?loc _ _ -> [hook])]
  in
  Vernacentries.DefAttributes.Observer.register ~name:"print-afterwards" attr


let error_hook =
  let attr : Declare.Hook.t list Attributes.attribute =
    let hook loc = Declare.Hook.make @@ fun data ->
      Feedback.msg_info Pp.(str "failing attribute") ;
      CErrors.user_err ?loc Pp.(str "attribute error!")
    in
    let open Attributes in
    let open Attributes.Notations in
    map (Option.default []) @@ attribute_of_list [("error", fun ?loc _ _ -> [hook loc])]
  in
  Vernacentries.DefAttributes.Observer.register ~name:"error" attr

(* Exercises the integer attribute parser ([Attributes.int_attribute] /
   [int_parser]): [#[size=N]] parses [N] as an [int] and prints it once the
   definition completes. *)
let size_hook =
  let attr : Declare.Hook.t list Attributes.attribute =
    let open Attributes in
    let open Attributes.Notations in
    int_attribute ~name:"size" >>= function
    | None -> return []
    | Some n ->
      let hook = Declare.Hook.make @@ fun _data ->
        Printf.fprintf size_oc "size = %d\n" n;
        flush size_oc
      in
      return [hook]
  in
  Vernacentries.DefAttributes.Observer.register ~name:"size" attr

let () =
  Mltop.(declare_cache_obj_full @@ interp_only_obj @@ fun () ->
         Vernacentries.DefAttributes.Observer.activate print_hook;
         Vernacentries.DefAttributes.Observer.activate error_hook;
         Vernacentries.DefAttributes.Observer.activate size_hook)
    "rocq-test-suite.attribute"
