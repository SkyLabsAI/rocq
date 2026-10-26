(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

module Mc = Micromega

(* Stack-safe arithmetic for the untrusted integer frontend. The extracted
   routines recurse once per binary digit and allocate while unwinding. On
   large constants, minor collections repeatedly scan that whole call stack.
   Keep the extracted code unchanged and use explicit accumulators here. *)

let pred_double p =
  let rec finish count p =
    if count = 0 then p else finish (count - 1) (Mc.XI p)
  in
  let rec descend count = function
    | Mc.XO p -> descend (count + 1) p
    | Mc.XI p -> finish count (Mc.XI (Mc.XO p))
    | Mc.XH -> finish count Mc.XH
  in
  descend 0 p

type step = Double | SuccDouble | PredDouble

let succ_double = function
  | Mc.Z0 -> Mc.Zpos Mc.XH
  | Mc.Zpos p -> Mc.Zpos (Mc.XI p)
  | Mc.Zneg p -> Mc.Zneg (pred_double p)

let zpred_double = function
  | Mc.Z0 -> Mc.Zneg Mc.XH
  | Mc.Zpos p -> Mc.Zpos (pred_double p)
  | Mc.Zneg p -> Mc.Zneg (Mc.XI p)

let pos_sub x y =
  (* Defunctionalize the continuations of [Mc.Z.pos_sub]. Compress equal
     consecutive steps: powers of two otherwise need one pending step per bit. *)
  let push step = function
    | (old, count) :: rest when step = old && count < max_int ->
      (step, count + 1) :: rest
    | rest -> (step, 1) :: rest
  in
  let rec repeat step count z =
    if count = 0 then z
    else
      let z = match step with
        | Double -> Mc.Z.double z
        | SuccDouble -> succ_double z
        | PredDouble -> zpred_double z
      in
      repeat step (count - 1) z
  in
  let rec finish steps z = match steps with
    | [] -> z
    | (step, count) :: rest -> finish rest (repeat step count z)
  in
  let rec descend steps x y = match x, y with
    | Mc.XI p, Mc.XI q -> descend (push Double steps) p q
    | Mc.XI p, Mc.XO q -> descend (push SuccDouble steps) p q
    | Mc.XI p, Mc.XH -> finish steps (Mc.Zpos (Mc.XO p))
    | Mc.XO p, Mc.XI q -> descend (push PredDouble steps) p q
    | Mc.XO p, Mc.XO q -> descend (push Double steps) p q
    | Mc.XO p, Mc.XH -> finish steps (Mc.Zpos (pred_double p))
    | Mc.XH, Mc.XI q -> finish steps (Mc.Zneg (Mc.XO q))
    | Mc.XH, Mc.XO q -> finish steps (Mc.Zneg (pred_double q))
    | Mc.XH, Mc.XH -> finish steps Mc.Z0
  in
  descend [] x y

(* Opposite signs require addition, for which we retain the extracted routine. *)
let sub x y = match x, y with
  | Mc.Z0, y -> Mc.Z.opp y
  | x, Mc.Z0 -> x
  | Mc.Zpos p, Mc.Zpos q -> pos_sub p q
  | Mc.Zneg p, Mc.Zneg q -> pos_sub q p
  | Mc.Zpos p, Mc.Zneg q -> Mc.Zpos (Mc.Coq_Pos.add p q)
  | Mc.Zneg p, Mc.Zpos q -> Mc.Zneg (Mc.Coq_Pos.add p q)

let one = Mc.Zpos Mc.XH
let minus_one = Mc.Zneg Mc.XH
let norm = Mc.norm Mc.Z0 one Mc.Z.add Mc.Z.mul sub Mc.Z.opp Mc.Z.eqb
let psub = Mc.psub0 Mc.Z0 Mc.Z.add sub Mc.Z.opp Mc.Z.eqb

(* Preserve the signs, ordering and clause construction of the extracted
   [xnnormalise], [xnormalise0] and [xnegate0]. Only the implementation of
   integer subtraction differs; certificates still use the existing checker. *)
let xnnormalise t =
  let lhs = norm t.Mc.flhs and rhs = norm t.Mc.frhs in
  match t.Mc.fop with
  | Mc.OpEq -> psub rhs lhs, Mc.Equal
  | Mc.OpNEq -> psub rhs lhs, Mc.NonEqual
  | Mc.OpLe -> psub rhs lhs, Mc.NonStrict
  | Mc.OpGe -> psub lhs rhs, Mc.NonStrict
  | Mc.OpLt -> psub rhs lhs, Mc.Strict
  | Mc.OpGt -> psub lhs rhs, Mc.Strict

let xnormalise = function
  | e, Mc.Equal ->
    [psub e (Mc.Pc one), Mc.NonStrict;
     psub (Mc.Pc minus_one) e, Mc.NonStrict]
  | e, Mc.NonEqual -> [e, Mc.Equal]
  | e, Mc.Strict -> [psub (Mc.Pc Mc.Z0) e, Mc.NonStrict]
  | e, Mc.NonStrict -> [psub (Mc.Pc minus_one) e, Mc.NonStrict]

let xnegate = function
  | e, Mc.NonEqual ->
    [psub e (Mc.Pc one), Mc.NonStrict;
     psub (Mc.Pc minus_one) e, Mc.NonStrict]
  | e, Mc.Strict -> [psub e (Mc.Pc one), Mc.NonStrict]
  | e, op -> [e, op]

let normalise formula tag =
  let f = xnnormalise formula in
  if Mc.zunsat f then Mc.cnf_ff else Mc.cnf_of_list0 tag (xnormalise f)

let negate formula tag =
  let f = xnnormalise formula in
  if Mc.zunsat f then Mc.cnf_tt else Mc.cnf_of_list0 tag (xnegate f)

let cnf kind formula =
  Mc.rxcnf Mc.zunsat Mc.zdeduce normalise negate true kind formula
