From Corelib Require Import PrimString ssreflect.
Set Default Timeout 3.
Set Primitive Projections.

Class Methods (tag : PrimString.string) := {
  classify : bool -> bool;
  attribute : bool -> bool
}.
Arguments classify _ {_} _ : simpl never.
Arguments attribute _ {_} _ : simpl never.

#[global] Instance methods : Methods "tag" := {|
  classify := fun b => if b then true else false;
  attribute := fun _ => true
|}.
Definition attr tag `{Methods tag} (n : bool) := attribute tag n.

(* The unfolding matcher tests a non-convertible candidate that applies the
   primitive string parameter to a bound variable. Literal WHD must return
   the original literal head, not the application assembled while inspecting
   its update stack; that [FApp] violates conversion's WHNF invariant. *)
Goal forall n, classify "tag" (attr "tag" n) = true.
Proof.
  intros n.
  rewrite /(classify "tag").
  reflexivity.
Qed.
