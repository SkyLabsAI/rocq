From Stdlib Require Import ZArith Lia.
From Stdlib.micromega Require Import EnvRing RingMicromega.

Unset Lia Cache.

(* Constant powers should reach the reflective checker as constants, rather
   than making both the OCaml and Rocq polynomial normalizers recompute them.
   Check the reified expression as well as the running time below. *)
Goal (2 ^ 10 = 1024)%Z.
Proof.
  Zify.zify.
  xlia ltac:(
    lazymatch goal with
    | |- let _ := _ in let _ := _ in let _ := ?ff in _ =>
      lazymatch ff with
      | Tauto.A _ {| RingMicromega.Flhs := EnvRing.PEc _;
                     RingMicromega.Fop := _;
                     RingMicromega.Frhs := _ |} _ => idtac
      | _ => fail "constant power was not folded"
      end
    end;
    zchecker).
Qed.

Goal (2 ^ 10000 - 1 <= 2 ^ 10000)%positive.
Proof. Timeout 5 lia. Qed.

Goal (2 ^ 10000 - 1 <= 2 ^ 10000)%N.
Proof. Timeout 5 lia. Qed.

Goal (2 ^ 10000 - 1 <= 2 ^ 10000)%Z.
Proof. Timeout 5 lia. Qed.

(* Constant expressions as bases, and powers occurring in exponents. *)
Goal ((1 + 1) ^ 10 = 1024)%Z.
Proof. lia. Qed.

Goal ((2 ^ 3) ^ 4 = 4096)%Z.
Proof. lia. Qed.

Goal (2 ^ (2 ^ 3) = 256)%Z.
Proof. lia. Qed.

(* Preserve the conventions for zero, negative bases and negative exponents. *)
Goal (0 ^ 0 = 1)%Z.
Proof. lia. Qed.

Goal (0 ^ 10 = 0)%Z.
Proof. lia. Qed.

Goal ((-2) ^ 11 = -2048)%Z.
Proof. lia. Qed.

Goal ((-2) ^ 10 = 1024)%Z.
Proof. lia. Qed.

Goal (2 ^ (-1) = 0)%Z.
Proof. lia. Qed.

(* The reifier must not evaluate a base that the outer exponent discards.
   Exercise it directly, without Zify visiting the discarded subterms. *)
Goal ((2 ^ 4294967295) ^ 0 = 1)%Z.
Proof. Timeout 5 xlia zchecker. Qed.

Goal ((2 ^ 4294967295) ^ (-1) = 0)%Z.
Proof. Timeout 5 xlia zchecker. Qed.

(* Nonconstant bases and exponents still use the existing reification. *)
Goal forall x : Z, (x ^ 2 = x * x)%Z.
Proof. intros. lia. Qed.

Goal forall n : Z, (2 ^ n - 1 <= 2 ^ n)%Z.
Proof. intros. lia. Qed.

Goal forall x : Z, (x + 2 ^ 10000 - 1 <= x + 2 ^ 10000)%Z.
Proof. intros. Timeout 5 lia. Qed.
