From Stdlib Require Import ZArith QArith Lia.
From Stdlib.micromega Require Import EnvRing RingMicromega Tauto QMicromega.

Unset Lia Cache.

(* The coefficient stays an integer constant in the reified language, but
   its Rocq term is compact rather than a long chain of binary constructors. *)
Goal (2 ^ 256 = 2 ^ 256)%Z.
Proof.
  Zify.zify.
  xlia ltac:(
    lazymatch goal with
    | |- let _ := _ in let _ := _ in let _ := ?ff in _ =>
      lazymatch ff with
      | A _ {| Flhs := PEc (Z.pow 2 _); Fop := _; Frhs := _ |} _ => idtac
      | _ => fail "power-of-two coefficient was expanded"
      end
    end;
    zchecker).
Qed.

Goal (2 ^ 65536 - 1 <= 2 ^ 65536)%Z.
Proof. Timeout 5 lia. Qed.

Goal (2 ^ 65536 - 1 <= 2 ^ 65536)%N.
Proof. Timeout 5 lia. Qed.

Goal (2 ^ 65536 - 1 <= 2 ^ 65536)%positive.
Proof. Timeout 5 lia. Qed.

Goal ((-2) ^ 257 + 2 ^ 257 = 0)%Z.
Proof. lia. Qed.

Goal forall x : Z, (x * x + 2 ^ 256 > x * x)%Z.
Proof. intros. nia. Qed.

(* Compact constants must also be accepted when an explicitly reified
   formula is passed to a witness tactic, without reducing its coefficients. *)
Goal True.
Proof.
  pose (ff := A isProp
    {| Flhs := PEc (2 ^ 256)%Z; Fop := OpLe; Frhs := PEc (2 ^ 256)%Z |} tt
    : BFormula (Formula Z) isProp).
  let ff' := eval unfold ff in ff in wlia wit ff'.
  let ff' := eval unfold ff in ff in wnia wit' ff'.
  exact I.
Qed.

Goal True.
Proof.
  pose (ff := A isProp
    {| Flhs := PEc (- (2 ^ 256))%Z; Fop := OpLe;
       Frhs := PEc (- (2 ^ 256))%Z |} tt
    : BFormula (Formula Z) isProp).
  let ff' := eval unfold ff in ff in wlia wit ff'.
  exact I.
Qed.

Goal True.
Proof.
  pose (ff := A isProp
    {| Flhs := PEc (Qmake (2 ^ 256)%Z 1%positive); Fop := OpLe;
       Frhs := PEc (Qmake (2 ^ 256)%Z 1%positive) |} tt
    : BFormula (Formula Q) isProp).
  let ff' := eval unfold ff in ff in wlra_Q wit ff'.
  exact I.
Qed.

(* The optimized producer must still reject false arithmetic statements. *)
Goal (2 ^ 256 = 0)%Z.
Proof. Fail lia. Abort.

Goal (2 ^ 256 - 1 >= 2 ^ 256)%Z.
Proof. Fail lia. Abort.
