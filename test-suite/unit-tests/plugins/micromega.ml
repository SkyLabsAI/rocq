open Utest

module Mc = Micromega_core_plugin.Micromega
module Conv = Micromega_core_plugin.Mutils.CamlToCoq
module Arith = Micromega_plugin.Lia_arith

let log_out_ch = open_log_out_ch __FILE__

let subtraction_small =
  let ok = ref true in
  for x = -100 to 100 do
    for y = -100 to 100 do
      let x = Conv.z x and y = Conv.z y in
      ok := !ok && Mc.Z.eqb (Arith.sub x y) (Mc.Z.sub x y)
    done
  done;
  !ok

let pred_double_small =
  let ok = ref true in
  for n = 1 to 10000 do
    let p = Conv.positive n in
    ok := !ok && Mc.Z.eqb
      (Mc.Zpos (Arith.pred_double p))
      (Mc.Zpos (Mc.Coq_Pos.pred_double p))
  done;
  !ok

let state = Random.State.make [|20657|]

let random_positive bits =
  let rec build bits p =
    if bits = 0 then p
    else build (bits - 1)
      (if Random.State.bool state then Mc.XI p else Mc.XO p)
  in
  build bits Mc.XH

let random_z () =
  let p = random_positive (Random.State.int state 512) in
  if Random.State.bool state then Mc.Zpos p else Mc.Zneg p

let subtraction_random =
  let ok = ref true in
  for _ = 1 to 2000 do
    let x = random_z () and y = random_z () in
    ok := !ok && Mc.Z.eqb (Arith.sub x y) (Mc.Z.sub x y)
  done;
  !ok

let large_subtraction =
  let rec bits constructor n p =
    if n = 0 then p else bits constructor (n - 1) (constructor p)
  in
  let n = 262144 in
  let power = Mc.Zpos (bits (fun p -> Mc.XO p) n Mc.XH) in
  let below = Mc.Zpos (bits (fun p -> Mc.XI p) (n - 1) Mc.XH) in
  let one = Conv.z 1 in
  Mc.Z.eqb (Arith.sub power one) below &&
  Mc.Z.eqb (Arith.sub power below) one &&
  Mc.Z.eqb (Arith.sub below power) (Conv.z (-1)) &&
  Mc.Z.eqb (Arith.sub power power) Mc.Z0

let rec expression depth =
  if depth = 0 then
    if Random.State.bool state then Mc.PEc (Conv.z (Random.State.int state 33 - 16))
    else Mc.PEX (Conv.positive (1 + Random.State.int state 3))
  else
    match Random.State.int state 5 with
    | 0 -> Mc.PEadd (expression (depth - 1), expression (depth - 1))
    | 1 -> Mc.PEsub (expression (depth - 1), expression (depth - 1))
    | 2 -> Mc.PEmul (expression (depth - 1), expression (depth - 1))
    | 3 -> Mc.PEopp (expression (depth - 1))
    | _ -> Mc.PEpow (expression (depth - 1), Conv.n (Random.State.int state 3))

let cnf_equivalence =
  let operators = [Mc.OpEq; Mc.OpNEq; Mc.OpLe; Mc.OpGe; Mc.OpLt; Mc.OpGt] in
  let ok = ref true in
  for _ = 1 to 100 do
    let lhs = expression 2 and rhs = expression 2 in
    List.iter (fun kind ->
      List.iter (fun op ->
        let atom = Mc.A (kind, {Mc.flhs = lhs; Mc.fop = op; Mc.frhs = rhs}, 0) in
        let other = Mc.A (kind, {Mc.flhs = rhs; Mc.fop = op; Mc.frhs = lhs}, 1) in
        let forms = [atom; Mc.NOT (kind, atom); Mc.AND (kind, atom, other);
                     Mc.OR (kind, atom, other); Mc.IMPL (kind, atom, None, other)] in
        List.iter (fun f -> ok := !ok && Arith.cnf kind f = Mc.cnfZ kind f) forms)
        operators)
      [Mc.IsProp; Mc.IsBool]
  done;
  !ok

let tests =
  [ mk_bool_test "micromega-sub-small" "subtraction agrees on small integers" subtraction_small
  ; mk_bool_test "micromega-pred-double" "pred_double agrees on small positives" pred_double_small
  ; mk_bool_test "micromega-sub-random" "subtraction agrees on random large integers" subtraction_random
  ; mk_bool_test "micromega-sub-large" "large borrow chains are stack-safe" large_subtraction
  ; mk_bool_test "micromega-cnf" "integer CNF agrees with the extracted implementation" cnf_equivalence
  ]

let () = run_tests __FILE__ log_out_ch tests
