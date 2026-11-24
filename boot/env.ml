(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

module Path = struct

  type t = string

  let relative = Filename.concat
  let to_string x = x
  let exists x = Sys.file_exists x

end

type standard_library =
  { physical_path : Path.t
  ; logical_path : string
  }

type library_layout =
  { coqlib : Path.t
  ; corelib : Path.t
  ; user_contrib : Path.t
  ; standard_libraries : standard_library list
  }

type t =
  { runtimelib : Path.t
  ; library_layout : library_layout
  }

(* This code needs to be refactored, for now it is just what used to be in envvars  *)

let use_suffix prefix suffix =
  if Filename.is_relative suffix
  then Filename.concat prefix suffix
  else suffix

let canonical_path_name p =
  let current = Sys.getcwd () in
  try
    Sys.chdir p;
    let p' = Sys.getcwd () in
    Sys.chdir current;
    p'
  with Sys_error _ ->
    (* We give up to find a canonical name and just simplify it... *)
    Filename.concat current p

let theories_dir = "theories"
let package_data_dir = "rocq.d"
let plugins_dir = "plugins"
let prelude = "Init/Prelude.vo"

let find_in_PATH f =
  match Sys.getenv_opt "PATH" with
  | None -> None
  | Some paths ->
    let sep = if Coq_config.arch_is_win32 then ';' else ':' in
    let paths = String.split_on_char sep paths in
    paths |> List.find_opt (fun path ->
        Sys.file_exists (if path = "" then f else Filename.concat path f))

let rocqbin =
  (* avoid following symlinks if possible (Sys.executable_name followed symlinks) *)
  if Filename.basename Sys.argv.(0) <> Sys.argv.(0) then
    (* explicit directory (maybe relative to current dir) *)
    canonical_path_name (Filename.dirname Sys.argv.(0))
  else match find_in_PATH Sys.argv.(0) with
    | Some p -> p
    | None -> canonical_path_name (Filename.dirname Sys.executable_name)

(** Locate the dune workspace root containing the given path, if any. *)
let dune_workspace_root : string -> string option = fun path ->
  let rec workspace_root path =
    let parent = Filename.dirname path in
    if parent = path then
      None
    else if Filename.basename path = "_build" then
      Some parent
    else
      workspace_root parent
  in
  match workspace_root path with
  | None -> None
  | Some root ->
      (* Check that this indeed looks like a dune workspace. *)
      let ok =
        let has file = Sys.file_exists (Filename.concat root file) in
        List.exists has ["dune-project"; "dune-workspace"]
      in
      if ok then Some root else None

(** Locate the installation root relative to the executable, or use the
    workspace installation root when running from Dune's build tree. *)
let rocqroot =
  let rec installed_root = function
    | [] -> None
    | path :: rest ->
      if Sys.file_exists (Filename.concat path "bin") then Some path
      else installed_root rest
  in
  (* We can be [bin/rocq] or [lib/rocq-runtime/rocqworker], so [rocqbin]
     can be [bin/] or [lib/rocq-runtime/]. Prefer this relocatable layout
     over the Dune workspace fallback. In particular, Dune package scopes
     have their own [bin/] and [lib/] directories below [_build/_private]. *)
  let dirname = Filename.dirname in
  match installed_root [ dirname rocqbin; dirname @@ dirname rocqbin ] with
  | Some root -> root
  | None ->
    (match dune_workspace_root rocqbin with
     | Some dir ->
       let dir = Filename.concat dir "_build" in
       let dir = Filename.concat dir "install" in
       Filename.concat dir "default"
     | None ->
       (* Couldn't recognize the layout, guess the executable is one
          directory below the root (for example [mybin/rocq]). *)
       Filename.dirname rocqbin)

let relocate = function
  | Coq_config.NotRelocatable p -> p
  | Coq_config.Relocatable p -> Filename.concat rocqroot p

let core_standard_library physical_path =
  { physical_path; logical_path = "Corelib" }

let legacy_layout coqlib =
  let corelib = Path.relative coqlib theories_dir in
  { coqlib
  ; corelib
  ; user_contrib = Path.relative coqlib "user-contrib"
  ; standard_libraries = [core_standard_library corelib]
  }

let findlib_layout coqlib =
  let corelib = Path.relative coqlib package_data_dir in
  (* Ltac2 is part of the standard distribution and remains available
     without an explicit [-package rocq-core.ltac2]. *)
  let ltac2 =
    Path.(relative (relative coqlib "ltac2") package_data_dir)
  in
  let standard_libraries =
    let corelib = core_standard_library corelib in
    if Path.exists ltac2 then
      [corelib; { physical_path = ltac2; logical_path = "Ltac2" }]
    else
      [corelib]
  in
  let libdir = Filename.dirname coqlib in
  (* Keep loading legacy user-contrib packages when they coexist with the
     findlib-style Corelib. *)
  { coqlib
  ; corelib
  ; user_contrib = Path.(relative (relative libdir "coq") "user-contrib")
  ; standard_libraries
  }

let valid_layout { corelib; _ } =
  Path.exists (Path.relative corelib prelude)

let existing_layout coqlib =
  let findlib = findlib_layout coqlib in
  if valid_layout findlib then
    Some findlib
  else
    let legacy = legacy_layout coqlib in
    if valid_layout legacy then Some legacy else None

let layout_for_coqlib coqlib =
  match existing_layout coqlib with
  | Some layout -> layout
  | None -> legacy_layout coqlib

let findlib_coqlib_suffix =
  Filename.concat (Filename.dirname Coq_config.coqlibsuffix) "rocq-core"

let guess_layout () =
  match Util.getenv_rocq "LIB" with
  | Some coqlib -> layout_for_coqlib coqlib
  | None ->
    let findlib_coqlib = use_suffix rocqroot findlib_coqlib_suffix in
    match existing_layout findlib_coqlib with
    | Some layout -> layout
    | None ->
      let legacy_coqlib = use_suffix rocqroot Coq_config.coqlibsuffix in
      match existing_layout legacy_coqlib with
      | Some layout -> layout
      | None -> layout_for_coqlib (relocate Coq_config.coqlib)

(* Build layout uses coqlib = coqcorelib
   XXX we should be using -boot in build layout so is that dead code? *)
let guess_coqcorelib lib =
  match Util.getenv_rocq_gen ~rocq:"ROCQRUNTIMELIB" ~coq:"COQCORELIB" with
  | Some v -> v
  | None ->
    if Sys.file_exists (Path.relative lib plugins_dir)
    then lib
    else Path.relative lib "../rocq-runtime"

let fail_lib lib =
  let open Printf in
  eprintf "File not found: %s\n" lib;
  eprintf "The path for Rocq libraries is wrong.\n";
  eprintf "Rocq prelude is shipped in the rocq-core package.\n";
  eprintf "Please check the ROCQLIB env variable or the -coqlib option.\n";
  exit 1

let fail_core plugin =
  let open Printf in
  eprintf "File not found: %s\n" plugin;
  eprintf "The path for Rocq plugins is wrong.\n";
  eprintf "Rocq plugins are shipped in the rocq-runtime package.\n";
  eprintf "Please check the ROCQRUNTIMELIB env variable.\n";
  exit 1

let validate_env
    ({ runtimelib; library_layout = { corelib; _ } } as env) =
  let prelude = Filename.concat corelib prelude in
  if not (Sys.file_exists prelude) then fail_lib prelude;
  let plugin = Filename.concat runtimelib plugins_dir in
  if not (Sys.file_exists plugin) then fail_core plugin;
  env

type maybe_env =
  | Env of t
  | Boot

let env_ref = ref None

(* Should we fail on double initialization? That seems a way to avoid
   mis-use for example when we pass command line arguments *)
let init_with ~coqlib =
  let library_layout =
    match coqlib with
    | None -> guess_layout ()
    | Some coqlib -> layout_for_coqlib coqlib
  in
  let env =
    { runtimelib = guess_coqcorelib library_layout.coqlib
    ; library_layout
    }
    |> validate_env
  in
  env_ref := Some (Env env);
  env

let initialized () = !env_ref

let ignored_coqlib_msg = "Command line options -boot and -coqlib are incompatible, ignored -coqlib."

let maybe_init ~warn_ignored_coqlib ~boot ~coqlib =
  match boot, coqlib with
  | true, None -> Boot
  | false, (None | Some _ as coqlib) ->
    (Env (init_with ~coqlib))
  | true, Some _ ->
    warn_ignored_coqlib ();
    Boot

let coqlib { library_layout = { coqlib; _ }; _ } = coqlib
let runtimelib { runtimelib; _ } = runtimelib
let plugins { runtimelib; _ } = Path.relative runtimelib plugins_dir
let corelib { library_layout = { corelib; _ }; _ } = corelib
let user_contrib { library_layout = { user_contrib; _ }; _ } = user_contrib
let standard_libraries { library_layout = { standard_libraries; _ }; _ } =
  standard_libraries
let tool { runtimelib; _ } tool = Path.(relative (relative runtimelib "tools") tool)
let revision { runtimelib; _ } = Path.relative runtimelib "revision"

let native_cmi { runtimelib; _ } lib =
  let install_path = Path.relative runtimelib lib in
  if Sys.file_exists install_path then
    install_path
  else
    (* Dune build layout, we need to improve this *)
    let obj_dir = Format.asprintf ".%s.objs" lib in
    Filename.(concat (concat (concat runtimelib lib) obj_dir) "byte")

(** {2 Caml paths} *)

let ocamlfind () = match Util.getenv_opt "OCAMLFIND" with
  | None -> Coq_config.ocamlfind
  | Some v -> v

let docdir () =
  (* This assumes implicitly that the suffix is non-trivial *)
  let path = use_suffix rocqroot Coq_config.docdirsuffix in
  if Sys.file_exists path then path else relocate Coq_config.docdir

(* Print the configuration information *)

let print_config ?(prefix_var_name="") env f =
  let coqlib = coqlib env |> Path.to_string in
  let runtimelib = runtimelib env |> Path.to_string in
  let open Printf in
  fprintf f "%sCOQLIB=%s/\n" prefix_var_name coqlib;
  fprintf f "%sCOQCORELIB=%s/\n" prefix_var_name runtimelib;
  fprintf f "%sDOCDIR=%s/\n" prefix_var_name (docdir ());
  fprintf f "%sOCAMLFIND=%s\n" prefix_var_name (ocamlfind ());
  fprintf f "%sCAMLFLAGS=%s\n" prefix_var_name Coq_config.caml_flags;
  fprintf f "%sWARN=%s\n" prefix_var_name "-warn-error +a-3";
  fprintf f "%sHASNATDYNLINK=%s\n" prefix_var_name
    (if Coq_config.has_natdynlink then "true" else "false");
  fprintf f "%sCOQ_SRC_SUBDIRS=%s\n" prefix_var_name (String.concat " " Coq_config.all_src_dirs);
  fprintf f "%sCOQ_NATIVE_COMPILER_DEFAULT=%s\n" prefix_var_name
    (match Coq_config.native_compiler with
     | Coq_config.NativeOn {ondemand=false} -> "yes"
     | Coq_config.NativeOff -> "no"
     | Coq_config.NativeOn {ondemand=true} -> "ondemand")

let query_getenv = function
  | Boot -> assert false
  | Env v -> v

let print_query envopt usage : Usage.query -> unit = function
  | PrintVersion -> Usage.version ()
  | PrintMachineReadableVersion -> Usage.machine_readable_version ()
  | PrintWhere ->
    let env = query_getenv envopt in
    let coqlib = coqlib env |> Path.to_string in
    print_endline coqlib
  | PrintHelp -> begin match usage with
      | Some usage -> Usage.print_usage stderr usage
      | None -> assert false
    end
  | PrintConfig ->
    let env = query_getenv envopt in
    print_config env stdout

let query_needs_env : Usage.query -> string option = function
  | PrintVersion | PrintMachineReadableVersion | PrintHelp -> None
  | PrintWhere -> Some "-where"
  | PrintConfig -> Some "-config"

let print_queries_maybe_init ~warn_ignored_coqlib ~boot ~coqlib usage = function
  | [] -> Ok (maybe_init ~warn_ignored_coqlib ~boot ~coqlib)
  | _ :: _ as qs ->
    let needs_env = CList.find_map query_needs_env qs in
    let res = match boot, needs_env with
    | true, Some q -> Error ("Command line option -boot is not compatible with " ^ q ^ ".")
    | true, None ->
      (* warn_ignored_coqlib if coqlib and boot used together *)
      Ok (maybe_init ~warn_ignored_coqlib ~boot ~coqlib)
    | false, None -> Ok Boot
    | false, Some _ -> Ok (Env (init_with ~coqlib))
    in
    let () = match res with
      | Error _ -> ()
      | Ok envopt -> List.iter (print_query envopt usage) qs
    in
    res
