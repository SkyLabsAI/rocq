From Coq.Force Require Import Force.

Module BlockedTelescopes.
  Inductive tele := tO | tS {X : Blocked Type} (F : unblock X -> tele) : tele.

  Fixpoint tele_fun (t : tele) Y : Type :=
    match t with
    | tO => Y
    | @tS X t => forall x : unblock X, tele_fun (t x) Y
    end.

  Fixpoint tele_arg (t : tele) : Type :=
    match t with
    | tO => unit : Type
    | @tS X t => { x : unblock X & tele_arg (t x) }
    end.

  Fixpoint tele_app {Y} {t : tele} : forall (f : tele_fun t Y) (args : tele_arg t), Y :=
    match t as t return tele_fun t Y -> tele_arg t -> Y with
    | tO => fun y _ => y
    | tS _ => fun f '(existT _ x args) => tele_app (f x) args
    end.

  Fixpoint tele_bind {Y} {t : tele} : (forall (args : tele_arg t), Y) -> tele_fun t Y :=
    match t as t return (tele_arg t -> Y) -> tele_fun t Y with
    | tO => fun f => f tt
    | tS t => fun f x => tele_bind (t:=t x) (fun args => f (existT _ x args))
    end.

  Fixpoint tele_snoc (t : tele) : forall (T : tele_fun t (Blocked Type)), tele :=
    match t as t return tele_fun t (Blocked Type) -> tele with
    | tO => fun f : Blocked Type => tS (X:=f) (fun _ => t)
    | tS t =>
        fun f =>
          tS (fun x => tele_snoc (t x) (f x))
    end.

  Fixpoint tele_snoc_args {t : tele} :
    forall {T : tele_fun t (Blocked Type)} (args : tele_arg t) (arg : unblock (tele_app T args)), tele_arg (tele_snoc t T) :=
    match t as t return
          forall {T : tele_fun t (Blocked Type)} (args : tele_arg t) (arg : unblock (tele_app T args)), tele_arg (tele_snoc t T)
    with
    | tO => fun _ args x => existT _ x args
    | tS _ => fun _ '(existT _ y args) x => existT _ y (tele_snoc_args args x)
    end.

  Notation "t -t> Y" := (tele_fun t Y) (at level 11).
End BlockedTelescopes.

Import BlockedTelescopes.

Inductive prop (t : tele) :=
  | true  : prop t
  | ex    : prop (tele_snoc t (tele_bind (fun _ => block (nat:Type)))) -> prop t.

Set Asymmetric Patterns.

Arguments true {_} &.
Arguments ex [_] &.

Definition reflect_aux (reflect : forall t, prop t -> t -t> Blocked Prop) {t} (p : prop t) :=
  match p with
  | ex p     =>
      tele_bind
        (fun args =>
            block (exists (x : unblock (tele_app _ args)),
                  let p := unblock (tele_app (reflect _ p) (tele_snoc_args args x))
                  in True
              )
        )
  | _      => tele_bind (fun _ => block True)
  end.

Fixpoint reflect' {t} (p : prop t) : t -t> Blocked Prop :=
    @reflect_aux (@reflect') t p.

Definition reflect := fun p : prop tO =>
match p with
| true => block True
| ex p0 => block (exists x : nat, let p1 := unblock (reflect' p0 x) in True)
end.
Lemma H' : unblock ((fun k => k (true (t:=tO))) reflect).
(* Lemma H' : unblock ((reflect (true (t:=tO)))). *)
Admitted.
(* Succeed Definition bla : True := H'. *)
(* Eval lazywhnf in unblock ((fun k => k (true (t:=tO))) reflect). *)
Set Debug "backtrace".
Definition bla : True := let n := 0 in H'.
