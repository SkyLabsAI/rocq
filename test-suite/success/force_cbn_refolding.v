From Corelib Require Import Force.

Set Universe Polymorphism.

Definition force_type@{u u1}
    (X : Blocked@{Type;u1} Type@{u}) : Type@{u} :=
  __run Type@{u} Type@{u} X (fun T => T).

Definition block_type@{u u1}
    (X : Type@{u}) : Blocked@{Type;u1} Type@{u} :=
  __block@{Type;u1} Type@{u} X.

(* The argument introduced by [__run] must not be refolded as an extra
   parameter of [force_type]. Previously [cbn] produced the ill-typed
   binder domain [force_type (block_type nat) nat]. *)
Goal forall x : force_type (block_type nat), nat.
Proof.
  cbn.
  intro x.
  exact x.
Qed.

Definition run_plus (n : nat) :=
  __run nat nat (__block nat n) (fun x => x + 1).

Goal forall n, run_plus n = n + 1.
Proof.
  intro n.
  cbn.
  reflexivity.
Qed.

(* The original application stack is retained after the synthetic argument
   has been consumed, including for a continuation that returns a function. *)
Definition run_apply (n : nat) :=
  __run nat (nat -> nat) (__block nat n) (fun x y => x + y).

Goal forall n m, run_apply n m = n + m.
Proof.
  intros n m.
  cbn.
  reflexivity.
Qed.
