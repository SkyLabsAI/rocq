From Coq.Force Require Import Force.
Inductive typ (u : unit) := val (x : typ u).

Definition f (x : typ tt) :=
  (fun x => x)
    (
      match x with
      | val _ x => block True
      end
    ).

Axiom base : typ tt.

Axiom H'' : unblock ((fun k => k (val tt base)) f).
Succeed Definition bla : True := H''.
Definition bla : True := let n := 0 in H''.
