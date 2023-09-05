Require Import Setoid.
Require Import Ltac2.Ltac2.
Import Constr Constr.Unsafe Printf.

Ltac2 red_flags_all : Std.red_flags := {
  Std.rBeta  := true;
  Std.rDelta := true;
  Std.rMatch := true;
  Std.rFix   := true;
  Std.rCofix := true;
  Std.rZeta  := true;
  Std.rConst := []
}.

Ltac2 red_flags_none : Std.red_flags := {
  Std.rBeta  := false;
  Std.rDelta := false;
  Std.rMatch := false;
  Std.rFix   := false;
  Std.rCofix := false;
  Std.rZeta  := false;
  Std.rConst := []
}.

Ltac2 red_flags_all_except : Std.reference list -> Std.red_flags := fun rs =>
  {red_flags_all with Std.rConst := rs}.

Ltac2 rec pp_stk (_ : unit) (stk : constr list) : message :=
  match stk with
  | []      => fprintf "[]"
  | t :: stk => fprintf "%t :: %a" t pp_stk stk
  end.

Module Logic.
  Set Default Proof Mode "Classic".

  Lemma iff_trivial (P : Prop) : P <-> P.
  Proof. split; intros H; exact H. Qed.

  Lemma and_comm (P1 P2 : Prop) : P1 /\ P2 <-> P2 /\ P1.
  Proof.
    split.
    - intros [H1 H2]; split; [exact H2 | exact H1].
    - intros [H2 H1]; split; [exact H1 | exact H2].
  Qed.

  Lemma and_true (P : Prop) : P /\ True <-> P.
  Proof.
    split.
    - intros [HP _]. exact HP.
    - intros HP. split; [exact HP| exact I].
  Qed.

  Lemma true_and (P : Prop) : True /\ P <-> P.
  Proof. rewrite and_comm. rewrite and_true. apply iff_trivial. Qed.

  Lemma and_false (P : Prop) : P /\ False <-> False.
  Proof.
    split.
    - intros [_ HF]. exact HF.
    - intros HF. exfalso. exact HF.
  Qed.

  Lemma false_and (P : Prop) : False /\ P <-> False.
  Proof. rewrite and_comm. rewrite and_false. apply iff_trivial. Qed.
End Logic.

Module Simpl.
  Set Default Proof Mode "Classic".
  Import Logic.

  Inductive prop :=
    | conj  : prop -> prop -> prop
    | true  : prop
    | false : prop
    | inj   : Prop -> prop.

  Ltac2 rec reify (p : constr) : constr :=
    lazy_match! p with
    | ?p1 /\ ?p2 => let p1 := reify p1 in
                    let p2 := reify p2 in
                    '(conj $p1 $p2)
    | True       => '(true)
    | False      => '(false)
    | ?p         => '(inj $p)
    end.

  Fixpoint reflect (p : prop) : Prop :=
    match p with
    | conj p1 p2 => reflect p1 /\ reflect p2
    | true       => True
    | false      => False
    | inj P      => P
    end.

  Fixpoint simplify (p : prop) : prop :=
    match p with
    | conj p1 p2 =>
        match simplify p1 with
        | true  => simplify p2
        | false => false
        | p1    =>
            match simplify p2 with
            | true  => p1
            | false => false
            | p2    => conj p1 p2
            end
        end
    | _ => p
    end.

  Lemma simplify_ok (p : prop) :
    reflect (simplify p) <-> reflect p.
  Proof.
    induction p; simpl.
    - rewrite <-IHp1; clear IHp1.
      rewrite <-IHp2; clear IHp2.
      destruct (simplify p1).
      + destruct (simplify p2); simpl.
        * apply iff_trivial.
        * rewrite and_true. apply iff_trivial.
        * rewrite and_false. apply iff_trivial.
        * apply iff_trivial.
      + simpl. rewrite true_and. apply iff_trivial.
      + simpl. rewrite false_and. apply iff_trivial.
      + destruct (simplify p2); simpl.
        * apply iff_trivial.
        * rewrite and_true. apply iff_trivial.
        * rewrite and_false. apply iff_trivial.
        * apply iff_trivial.
    - apply iff_trivial.
    - apply iff_trivial.
    - apply iff_trivial.
  Qed.

  Lemma simplify_ok1 (p : prop) :
    reflect (simplify p) -> reflect p.
  Proof. apply simplify_ok. Qed.

  Ltac2 truely_simplify (p : constr) : unit :=
    let reified := reify p in
    let simplified := '(reflect (simplify $reified)) in
    let simplified := Std.eval_lazy red_flags_all simplified in
    let subgoal := Std.eval_hnf (open_constr:(_ : $simplified)) in
    apply (simplify_ok1 $reified $subgoal).

  Ltac truely_simplify :=
    let truely_simplify :=
      ltac2:(p |- truely_simplify (Option.get (Ltac1.to_constr p)))
    in
    lazymatch goal with |- ?p => unshelve (truely_simplify p) end.

  Goal True /\ (True /\ 1 + 1 = 2) /\ (True /\ True).
  Proof.
    truely_simplify.
    reflexivity.
  Qed.
End Simpl.

Module Telescopes.
  Inductive tele := tO | tS {X} (F : X -> tele) : tele.

  Fixpoint tele_fun (t : tele) Y : Type :=
    match t with
    | tO => Y
    | @tS X t => forall x : X, tele_fun (t x) Y
    end.

  Fixpoint tele_arg (t : tele) : Type :=
    match t with
    | tO => unit : Type
    | @tS X t => { x : X & tele_arg (t x) }
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

  Fixpoint tele_snoc (t : tele) : forall (T : tele_fun t Type), tele :=
    match t as t return tele_fun t Type -> tele with
    | tO => fun f => tS (fun _ : f => t)
    | tS t =>
        fun f =>
          tS (fun x => tele_snoc (t x) (f x))
    end.

  Fixpoint tele_snoc_args {t : tele} :
    forall {T : tele_fun t Type} (args : tele_arg t) (arg : tele_app T args), tele_arg (tele_snoc t T) :=
    match t as t return
          forall {T : tele_fun t Type} (args : tele_arg t) (arg : tele_app T args), tele_arg (tele_snoc t T)
    with
    | tO => fun _ args x => existT _ x args
    | tS _ => fun _ '(existT _ y args) x => existT _ y (tele_snoc_args args x)
    end.

  Notation "t -t> Y" := (tele_fun t Y) (at level 11).
End Telescopes.

Module WithTele.
  Import Telescopes.

  Inductive prop (t : tele) :=
    | conj  : prop t -> prop t -> prop t
    | true  : prop t
    | false : prop t
    | inj   : (t -t> Prop) -> prop t
    | ex (T : t -t> Type) : prop (tele_snoc t T) -> prop t.

  Set Asymmetric Patterns.

  Arguments conj [_].
  Arguments true {_}.
  Arguments false {_}.
  Arguments inj [_].
  Arguments ex [_].

  Import Constr.Unsafe.

  Ltac2 rec to_lambdas (t : constr) (body : constr) :=
    let t := Std.eval_hnf t in
    lazy_match! t with
    | tO        => body
    | @tS ?x ?f =>
        let f := Std.eval_hnf f in
        let (b, fbody) :=
          match kind f with
          | Lambda b f => (b, f)
          | _ => Control.zero (Invalid_argument None)
          end
        in
        let body := to_lambdas fbody body in
        Constr.Unsafe.make (Constr.Unsafe.Lambda b body)
    end.

  Import Ltac2.Printf.
  Ltac2 rec tele_snoc (t : constr) (b : ident option) (ty : constr) :=
    (*printf "telesnoc %t" t;*)
    lazy_match! t with
    | tO         =>
        let f := make (Lambda (Constr.Binder.make b ty) constr:(tO)) in
        make (App constr:(@tS) (Array.of_list [ty; f]))
    | @tS ?ty ?f =>
        let (b', f) :=
          match kind f with
          | Lambda b' f => (b', f)
          | _ => Control.zero (Invalid_argument None)
          end
        in
        let f := make (Lambda b' (tele_snoc f b ty)) in
        make (App constr:(@tS) (Array.of_list [ty; f]))
    end.

  (* TODO: fixme *)
  Ltac2 rec reify (t : constr) (p : constr) : constr :=
    (*printf "reify (%t) (%t)" t p;*)
    lazy_match! p with
    | ?p1 /\ ?p2          =>
        let p1 := reify t p1 in
        let p2 := reify t p2 in
        '(@conj $t $p1 $p2)
    | @Logic.ex ?ty ?p =>
        let i :=
          match kind p with
          | Lambda b _ => Constr.Binder.name b
          | _ => Control.zero (Invalid_argument None)
          end
        in
        let t' := tele_snoc t i ty in
        let ty := to_lambdas t ty in
        let p :=
          let arg := Constr.Unsafe.make (Constr.Unsafe.Rel 1) in
          let p := Constr.Unsafe.liftn 1 1 p in
          Constr.Unsafe.make (Constr.Unsafe.App p (Array.of_list [arg]))
        in
        let p := Std.eval_hnf p in
        let p := reify t' p in
        '(@ex $t $ty $p)
    | True                => '(@true $t)
    | False               => '(@false $t)
    | ?p                  =>
        let p := to_lambdas t p in
        '(@inj $t $p)
    end.

  Ltac2 Eval reify 'tO '(True /\ exists n, (exists m, n = m) /\ n = 0).

  Fixpoint reflect {t} (p : prop t) : t -t> Prop :=
    match p with
    | conj p1 p2 => tele_bind (fun args => tele_app (reflect p1) args /\ tele_app (reflect p2) args)
    | true       => tele_bind (fun _ => True)
    | false      => tele_bind (fun _ => False)
    | inj P      => P
    | ex T p     => tele_bind (fun args => exists (x : tele_app T args), tele_app (reflect p) (tele_snoc_args args x))
    end.

  Fixpoint simplify {t} (p : prop t) : prop t :=
    match p with
    | conj p1 p2 =>
        match simplify p1 with
        | true  => simplify p2
        | false => false
        | p1    =>
            match simplify p2 with
            | true  => p1
            | false => false
            | p2    => conj p1 p2
            end
        end
    | ex _ p =>
        ex _ (simplify p)
    | _ => p
    end.

  Lemma simplify_ok {t} (p : prop t) :
    forall args, tele_app (reflect (simplify p)) args <-> tele_app (reflect p) args.
  Proof.
  Admitted.

  Lemma simplify_ok1 {t} (p : prop t) :
    forall args, tele_app (reflect (simplify p)) args -> tele_app (reflect p) args.
  Proof. apply simplify_ok. Qed.

  Ltac2 truely_simplify (p : constr) : unit :=
    let reified := reify 'tO p in
    let simplified := '(reflect (simplify $reified)) in
    let simplified := Std.eval_lazy red_flags_all simplified in
    let subgoal := Std.eval_hnf (open_constr:(_ : $simplified)) in
    apply (@simplify_ok1 tO $reified tt $subgoal).

  Ltac truely_simplify :=
    let truely_simplify :=
      ltac2:(p |- truely_simplify (Option.get (Ltac1.to_constr p)))
    in
    lazymatch goal with |- ?p => unshelve (truely_simplify p) end.

  Set Default Proof Mode "Classic".

  Goal True /\ (True /\ exists n, True /\ n = 1 + 1) /\ (True /\ True).
  Proof.
    truely_simplify.
    exists 2. reflexivity.
  Qed.
End WithTele.

(* Section Block. *)
(*   Record Blocked {T} := block { unblock : T }. *)
(*   #[global] Arguments Blocked : clear implicits. *)
(*   #[global] Arguments block [_]. *)
(*   #[global] Arguments unblock [_] : simpl never. *)

(*   Definition run {T Y} : Blocked T -> (T -> Y) -> Y := fun b f => f (unblock b). *)
(*   #[global] Arguments run [_ _] : simpl never. *)
(* End Block. *)

(* Add Printing Constructor Blocked. *)

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


Module WithTeleAndBlock.
  Import BlockedTelescopes.

  Inductive prop (t : tele) :=
    | conj  : prop t -> prop t -> prop t
    | true  : prop t
    | false : prop t
    | inj   : (t -t> Blocked Prop) -> prop t
    | ex    (T : t -t> Blocked Type) : prop (tele_snoc t T) -> prop t.

  Set Asymmetric Patterns.

  Arguments conj [_] &.
  Arguments true {_} &.
  Arguments false {_} &.
  Arguments inj [_] &.
  Arguments ex [_] &.

  (* TODO: fixme *)
  Ltac2 rec reify (t : constr) (p : constr) : constr :=
    lazy_match! p with
    | ?p1 /\ ?p2 => let p1 := reify t p1 in
                    let p2 := reify t p2 in
                    '(conj $t $p1 $p2)
    | True       => '(true $t)
    | False      => '(false $t)
    | ?p         => '(inj $t $p)
    end.

  Fixpoint simplify {t} (p : prop t) : prop t :=
    match p with
    | conj p1 p2 =>
        match simplify p1 with
        | true  => simplify p2
        | false => false
        | p1    =>
            match simplify p2 with
            | true  => p1
            | false => false
            | p2    => conj p1 p2
            end
        end
    | ex ty p => ex ty (simplify p)
    | _ => p
    end.


  Fixpoint reflect {t} (p : prop t) : t -t> Blocked Prop :=
    match p with
    | conj p1 p2 => tele_bind (fun args => block (unblock (tele_app (reflect p1) args) /\ unblock (tele_app (reflect p2) args)))
    | true       => tele_bind (fun _ => block True)
    | false      => tele_bind (fun _ => block False)
    | inj P      => tele_bind (fun args => tele_app P args)
    | ex T p     => tele_bind (fun args => block (exists (x : unblock (tele_app T args)), unblock (tele_app (reflect p) (tele_snoc_args args x))))
    end.

  Ltac2 Type reduction := [ Id | Flags (Std.red_flags) ].
  Ltac2 flags_of (r : reduction) :=
    match r with
    | Flags flags => flags
    | Id => red_flags_none
    end.

  Import Constr Constr.Unsafe Printf.

  Ltac2 decompose_app (c : constr) :=
    match kind c with
    | App h args => (h, args)
    | _ => (c, Array.empty ())
    end.

  (* Ltac2 inductive_of_val (v : constr) := *)
  (*   let t := Constr.type v in *)
  (*   let t := Std.eval_hnf t in  (* probably unnecessary *) *)
  (*   printf "type: %t" t; *)
  (*   let (h, _) := decompose_app t in *)
  (*   match kind h with *)
  (*   | Ind ind _u => ind *)
  (*   | _ => Control.throw (Invalid_argument None) *)
  (*   end. *)

  Ltac2 inductive_of_return_type (ret : constr) :=
    let rec go (n_indices : int) t :=
      let t := Std.eval_hnf t in
      (* printf "return type: %t" t; *)
      match kind t with
      | Lambda b t =>
          (* Only the last lambda has the inductive type we are looking for *)
          match kind t with
          | Lambda _ _ => go (Int.add 1 n_indices) t
          | _ =>
            let (h, args) := decompose_app (Constr.Binder.type b) in
            match kind h with
            | Ind ind _u =>
                let n_params := Int.sub (Array.length args) n_indices in
                (ind, n_params)
            | _ => Control.throw (Invalid_argument None)
          end
        end
      | _ => Control.throw (Invalid_argument None)
      end
    in go 0 ret.

  Ltac2 int_of_constructor (ind : inductive) (c : constructor) : int :=
    let rec go i :=
      if Constructor.equal (Constr.Unsafe.constructor ind i) c then i else go (Int.add i 1)
    in
    go 0.


  Ltac2 rec struct_arg (f : constr) : int :=
    match Constr.Unsafe.kind f with
    | Constr.Unsafe.Fix structs which _ _ => Array.get structs which
    | Constr.Unsafe.Lambda _ body => Int.add 1 (struct_arg body)
    | _ => Control.throw (Invalid_argument (Some (fprintf "not a fixpoint")))
    end.

  Import Ltac2.Bool.

  (* [with_2_args args stk go err] retrieves two arguments from
     [args ++ stk] if possible and
     - runs [go arg1 arg2 new_args stk'] on success
       where [new_args] are new arguments that need to be added to [stk']
       and [stk'] is the remainder of [stk]
     - or [err ()] on failure
   *)
  Ltac2 with_2_args (args : constr list) (stk : constr list)
    (go : constr -> constr -> constr list -> constr list -> 'a) (err : unit -> 'a) :=
    match (args, stk) with
    | (ty :: (b :: args), _) => go ty b args stk
    | ([ty],     b :: stk) => go ty b [] stk
    | ([], ty :: (b :: stk)) => go ty b [] stk
    | (args, _) => err ()
    end.

  Ltac2 with_4_args (args : constr list) (stk : constr list)
    (go : constr -> constr -> constr -> constr -> constr list -> constr list -> 'a) (err : unit -> 'a) :=
    match (args, stk) with
    | (ty :: (ty' :: (b :: (f :: args))), _) => go ty ty' b f args stk
    | ([ty;ty';b],  f :: stk) => go ty ty' b f [] stk
    | ([ty;ty'],    b:: (f :: stk)) => go ty ty' b f [] stk
    | ([ty],   ty' :: (b:: (f :: stk))) => go ty ty' b f [] stk
    | ([],  ty :: (ty' :: (b:: (f :: stk)))) => go ty ty' b f [] stk
    | (args, _) => err ()
    end.

  Module Red.
    Ltac2 Type reach := [Head | Full].
    Ltac2 Type t := { reach : reach; flags : Std.red_flags }.
    Ltac2 id := { reach := Full; flags := red_flags_none }.
    Ltac2 full_whd := { reach := Head; flags := red_flags_all }.
    Ltac2 full := { reach := Full; flags := red_flags_all }.
    Ltac2 is_full r := match r.(reach) with Full => true | Head => false end.
  End Red.

  Ltac2 reduce (msp : bool) (debug : bool) (r : Red.t) (t : constr) : constr :=
    let rec go_stack r t stk :=
      (if debug then printf "%t @ %a" t pp_stk stk else ());
      let go r t :=
        let (t, stk) := go_stack r t [] in
        make (App t (Array.of_list stk))
      in
      let go_args := if Red.is_full r then go r else fun x => x in
      let go_args_binder b :=
        let name := Constr.Binder.name b in
        let ty := go_args (Constr.Binder.type b) in
        Constr.Binder.unsafe_make name Constr.Binder.Relevant ty
      in
      match (kind t, stk) with
      | ((Rel _ | Var _ | Meta _ | Evar _ _), _) => (t, stk)
      | ((Sort _ | Float _ | Uint63 _), []) => (t, [])
      | ((Constructor _ _ | Ind _ _), _) => (t, stk)
      | (Array a b c d, []) => (make (Array a (Array.map go_args b) (go_args c) (go_args d)), [])
      | (Proj _ _, stk) => (t, stk)           (* Not supported *)
      | (Cast b c t, stk) => (* b : t *)
          if r.(Red.flags).(Std.rBeta) then
            go_stack r b stk
          else
            (* TODO: reduce [b] in weak head reduction even when the cast does not reduce? *)
            (make (Cast (go_args b) c (go_args t)), stk)
      | (Prod b t, []) =>
          let b := go_args_binder b in
          (make (Prod b (go_args t)), [])
      | (Lambda b t, []) =>
          let b := go_args_binder b in
          (make (Lambda b (go_args t)), [])
      | (Lambda b t, x::stk') =>
          if r.(Red.flags).(Std.rBeta) then
            let h := substnl [x] 0 t in
            go_stack r h stk'
          else
            let b := go_args_binder b in
            (make (Lambda b (go_args t)), stk)
      | (LetIn b e t, _) =>
          if r.(Red.flags).(Std.rZeta) then
            let e := go_args e in
            let t := substnl [e] 0 t in
            go_stack r t stk
          else
            let e := go_args e in
            let b := go_args_binder b in
            let t := go_args t in
            (make (LetIn b e t), stk)
      | (Fix a b c d, []) =>
          let d := Array.map go_args d in
          make (Fix a b c d), stk
      | (Fix a b c d, _) =>
          (* TODO: broken?? *)
          let struct_arg_ind := struct_arg t in
          if r.(Red.flags).(Std.rFix) && Int.le struct_arg_ind (List.length stk) then
            let struct_arg := List.nth stk (struct_arg t) in
            (* If [struct_arg] was added to the stack in [Head] mode we need to reduce it again.
               We cannot tell if that is the case so we reduce it either way.
               We only need weak head reduction here.
             *)
            let struct_arg := go {r with Red.reach := Red.Head} struct_arg in
            let (struct_arg, struct_arg_args) := decompose_app struct_arg in
            match kind struct_arg with
            | Constructor _ _ =>
                let body := Array.get d b in
                let body := substnl [t] 0 body in
                go_stack r body stk
            | _ =>
                let d := Array.map go_args d in
                (make (Fix a b c d), stk)
            end
          else
            let d := Array.map go_args d in
            (make (Fix a b c d), stk)
      | (CoFix a b c, _) => (t, stk)
      | (Case a b c d e, _) =>
          let d := go r d in      (* value *)
          let (dh, dargs) := decompose_app d in
          match r.(Red.flags).(Std.rMatch), kind dh with
          | true, Constructor c _ =>
              let (ind, n_params) := inductive_of_return_type b in
              let i := int_of_constructor ind c in
              let dargs := Array.sub dargs n_params (Int.sub (Array.length dargs) n_params) in
              let stk := List.append (Array.to_list (Array.map go_args dargs)) stk in
              go_stack r (Array.get e i) stk
          | _, _ =>
              let b := go_args b in      (* return type *)
              let e := Array.map go_args e in
              (make (Case a b c d e), stk)
          end
      | (Constant _c _u, _) =>
          (* TODO: handle [rConst] *)
          if r.(Red.flags).(Std.rDelta) then
            (* Best way to unfold a constant just once? *)
            let t' := constr:(ltac:(let t := constr:($t) in first [ let t := eval red in t in exact t | exact t])) in
            if Constr.equal t' t then (t, stk)
            else go_stack r t' stk
          else
            (t, stk)
      | (App h args, _) =>
          if msp then
            lazy_match! h with
            | @block =>
                match stk, Array.length args with
                | ([], 2) =>
                    let args := Array.map (fun t => go Red.id t) args in
                    (make (App h args), [])
                | ([], 1) =>
                    (make (App h args), [])
                | (_, _) =>
                    Control.throw (Invalid_argument (Some (fprintf "@block is applied to more than two arguments")))
                end
            | @unblock =>
                let aux (ty : constr) (b : constr) new_args (stk : constr list) :=
                  (* TODO: reduce [ty]? *)
                  let stk := List.append (List.map go_args new_args) stk in
                  (* TODO: [Red.full] or [orig_r with reach := Full]? *)
                  let b := go Red.full b in
                  let (bh, bargs) := decompose_app b in
                  lazy_match! bh with
                  | @block =>
                      (* Reducing [Array.get bargs 1] is wasteful if the current
                        reduction is [Id]. This is always the case inside a
                        [block] but not when we find an [unblock] outside of
                        [block]. *)
                      go_stack r (Array.get bargs 1) stk
                  | _ => (h, ty :: b :: stk)
                  end
                in
                let args := Array.to_list args in
                with_2_args args stk aux (fun () => (h, List.append (List.map go_args args) stk))
            | @run =>
                let aux (ty : constr) (ty' : constr) (b : constr) (f : constr) new_args (stk : constr list) :=
                  (* TODO: reduce [ty]? *)
                  let stk := List.append (List.map go_args new_args) stk in
                  let b := go Red.full b in
                  let (bh, bargs) := decompose_app b in
                  lazy_match! bh with
                  | @block =>
                      go_stack r f (Array.get bargs 1::stk)
                  | _ => (h, ty :: ty' :: b :: f :: stk)
                  end
                in
                let args := Array.to_list args in
                with_4_args args stk aux (fun () => (h, List.append (List.map go_args args) stk))
            | _ =>
                let stk := List.append (Array.to_list (Array.map go_args args)) stk in
                go_stack r h stk
            end
          else
            let stk := List.append (Array.to_list (Array.map go_args args)) stk in
            go_stack r h stk
      | (_, _) => Control.throw (Invalid_argument (Some (fprintf "ill-typed term: %t" t)))
      end
    in
    let (t, stk) := go_stack r t [] in
    make (App t (Array.of_list stk)).

  Ltac2 lazy_reduce dbg r t := reduce true dbg r t.
  Ltac2 old_reduce dbg r t := reduce false dbg r t.

  Ltac2 expect dbg r t_in t_out :=
    let t_res := lazy_reduce dbg r t_in in
    if Constr.equal t_res t_out then
      ()
    else
      Control.throw (Invalid_argument (Some (fprintf "Result (%t) differs from expected result (%t)" t_res t_out))).

  Monomorphic Universe U.

  (* GMM: I'm actually surprised that this does not become [block 2].
     In MSP, reduction is completely lexical and [block] is not a function that can be abstracted
     over. *)
  Ltac2 Eval expect false Red.full
    '((fun f => f (1 + 1)) (@block@{U} nat))
    '(block@{U} (1+1)).
  (* GMM: indeed, if you eta-expand [block], then it is reduced. *)
  Fail Ltac2 Eval expect false Red.full
    '((fun f => f (1 + 1)) (fun x => @block nat x))
    '(block (1+1)).

  (* GMM: These reductions involve level-0 [unblock].
     I wonder if it possible to get the same semantics with the following
     definition of [unblock0].
   *)
  Definition unblock0 {T : Type} (e : Blocked T) : T :=
    run e (fun x => x).

  Ltac2 Eval expect false Red.full
    '(unblock0 (block (1+1)))
    '(2).
  (* Set Debug "backtrace". *)
  Ltac2 Eval expect true Red.full
    '((fun (f:forall T, Blocked T -> T) => f (nat) (block (1 + 1))) (@unblock))
    '(2).

  Ltac2 Eval expect false Red.full_whd
    '(block@{U} (run (let n := 2+2 in block (n+1)) (fun x:nat => 2 * 1)))
    '(block@{U} ((fun _ : nat => 2 * 1) (4 + 1))).

  (* The initial strategy is irrelevant since [block] overwrites it with [Id].

     GMM:
     I would expect this to not reduce at all because it does not have any
     [unblock]. The reduction here seems to suggest that [run] is the same as
     [unblock], but that doesn't seem like it should be the case.
   *)
  Ltac2 Eval expect false Red.full
    '(block@{U} (run (let n := 2+2 in block (n+1)) (fun x:nat => 2 * 1)))
    '(block@{U} ((fun _ : nat => 2 * 1) (4 + 1))).

  (* this is [unblock] at level 0. *)
  Ltac2 Eval expect false Red.full
    '(unblock (block (run (let n := 2+2 in block (n+1)) (fun x:nat => 2 * 1))))
    '(2).

  Inductive test (p : unit) : nat -> Set := T n : test p n.

  Ltac2 Eval expect false Red.full '(match T tt 1 return nat with T n => S n end) '(2).

  Ltac2 Eval expect false Red.full '(1 + 0) '1.
  Ltac2 Eval expect false Red.full_whd '(1 + 0)
    '(S ((fix add (n m : nat) {struct n} : nat :=
            match n with
            | 0 => m
            | S p => S (add p m)
            end) 0 0)).

  Ltac2 Eval expect false Red.full
    '(fun x:nat => x * (7 * 8))
    '(fun x : nat =>
        (fix mul (n m : nat) {struct n} : nat :=
           match n with
           | 0 => 0
           | S p =>
               (fix add (n0 m0 : nat) {struct n0} : nat := match n0 with
                                                           | 0 => m0
                                                           | S p0 => S (add p0 m0)
                                                           end) m (mul p m)
           end) x 56).

  Ltac2 Eval expect false Red.full
    '(match O return nat -> Prop with O => fun n => 1 + n = n | _ => fun _ => False end)
    '(fun n : nat => S n = n).


  Ltac2 Eval expect false Red.full '(block@{U} (1+1)) '(block@{U} (1+1)).
  Ltac2 Eval expect false Red.full '(match unblock (block (0+0)) with O => True | _ => False end) 'True.
  Ltac2 Eval expect false Red.full_whd '(match unblock (block (0+0)) with O => True | _ => False end) 'True.
  Ltac2 Eval expect false { Red.reach := Red.Full; Red.flags := { red_flags_none with Std.rBeta := true } }
    '(run (block (1+1)) (fun x => x = x -> True))
    '(1 + 1 = 1 + 1 -> True).

  Record res (A:Type) := Res {}.

  Goal
    let p : prop tO :=
      conj true (ex (block (id nat:Type)) (inj (fun x : nat => block (x = 1+1))))
    in
    run (reflect p) (fun p => res p).
  Proof.
    Set Ltac2 Backtrace.
    lazy_match! goal with
    | [ |- ?g] =>
        let g := lazy_reduce true Red.full_whd g in
        change $g
    end.
    lazy_match! goal with
    | [ |- res (True /\ (exists x : id nat, x = 1 + 1)) ] =>
        constructor
    end.
  Qed.


  Goal
    let p : prop tO :=
      conj true (ex (block (id nat:Type)) (conj true (inj (fun x : nat => block (x = 1+1)))))
    in
    run (reflect (simplify p)) (fun p => res p).
  Proof.
    lazy_match! goal with
    | [ |- ?g] =>
        let g := lazy_reduce false Red.full_whd g in
        change $g
    end.
    lazy_match! goal with
    | [ |- res ((exists x : id nat, x = 1 + 1)) ] =>
        constructor
    end.
  Qed.

  Goal
    let p : prop tO :=
      conj true (ex (block (id nat:Type)) (inj (fun x : nat => block (x = 1+1))))
    in
    run (id (reflect p)) (fun p => res p).
  Proof.
    lazy_match! goal with
    | [ |- ?g ] =>
        let g := lazy_reduce false Red.full_whd g in
        change $g
    end.
    lazy_match! goal with
    | [ |- res (True /\ (exists x : id nat, x = 1 + 1)) ] =>
        constructor
    end.
  Qed.

  Goal run (let n := 1 + 1 in block n) (fun n => n = 2).
  Proof.
    lazy_match! goal with
    | [ |- ?g] =>
        let g := lazy_reduce false Red.full_whd g in
        change $g
    end.
    lazy_match! goal with
    | [ |- ?a = ?a] => reflexivity
    end.
  Qed.

  Goal (let n := 1 + 1 in n = 2).
  Proof.
    lazy_match! goal with
    | [ |- ?g] =>
        let g := lazy_reduce false Red.full_whd g in
        change $g
    end.
    lazy_match! goal with
    | [ |- 1 + 1 = 2] => reflexivity
    end.
  Qed.

  (* Extend a chain of [ex^n true] by one more existential *)
  Fixpoint add_inner_ex {t} (p : prop t) (k : prop t -> Blocked Prop) : Blocked Prop :=
    match p with
    | ex ty p => add_inner_ex p (fun p => k (ex ty p))
    | true =>
        let t :=
          (forall ty' : t -t> Blocked Type,
              unblock (k (ex ty' true)))
        in block t
    | _ => block False
    end.

  Fixpoint add_inner_exs {t} (p : prop t) (n : nat) (k : prop t -> Blocked Prop) {struct n} : Blocked Prop :=
    match n with
    | O => (k p)
    | S n => add_inner_ex p (fun p => (add_inner_exs p n k))
    end.

  Lemma H : forall n, run (add_inner_exs (t:=tO) (true) n (fun p => (reflect (simplify p)))) (fun x => x).
  Admitted.

  Fixpoint prods (n : nat) (t b : Type) : Type :=
    match n with
    | O => b
    | S n => forall _ : t, prods n t b
    end.
  Fixpoint lams (n : nat) (t b : Type) (x : b) : prods n t b :=
    match n as n return prods n t b with
    | O => x
    | S n => fun _ : t => lams n t b x
    end.

  Goal exists _ : nat, True.
    refine '(H 1 (block (nat:Type))).
  Qed.

  Eval lazy in let n := 0 in run (add_inner_exs (t:=tO) (true) n reflect) (fun x => x).

  (* Lemma H' : run ((fun k => k true) (reflect (t:=tO))) (fun x => x). *)


  Axiom args' : forall {t}, tele_arg t.
  Fixpoint reflect' {t} (p : prop t) : t -t> Blocked Prop :=
    match p with
    (* | conj p1 p2 => tele_bind (fun args => block (unblock (tele_app (reflect' p1) args) /\ unblock (tele_app (reflect' p2) args))) *)
    (* | true       => tele_bind (fun _ => block True) *)
    (* | inj P      => tele_bind (fun args => tele_app P args) *)
    | ex T' p     =>
        tele_bind
          (fun args =>
             (* block (exists (x : unblock (tele_app T' args)), unblock (tele_app (reflect' p) (tele_snoc_args args x))) *)
             (* block True *)
             block (exists (x : unblock (tele_app T' args)),
                   let p := unblock (tele_app (reflect' p) (tele_snoc_args args x))
                   in True
               )
          )
    | _      => tele_bind (fun _ => block True)
    end.

  Lemma H' : unblock ((fun k => k (true (t:=tO))) reflect').
  Admitted.
  Succeed Definition bla : True := H' : True.
  Set Debug "backtrace".
  Definition bla : True := let n := 0 in H' : True.


  Goal Nat.iter 0 (fun x => exists _ : nat, x) True.
    pose (n := I).
    (* let n := Std.eval_vm None '&n in *)
    (* let t := '(H $n) in *)
    (* let ty := Constr.type t in *)
    (* assert (x : $ty) by refine t. *)
    exact (H O : True).
    Show Proof.
    (* Set Debug "backtrace". *)
  Abort.

  Goal let n := 0 in Nat.iter n (fun x => exists _ : nat, x) True.
    lazy.
    intros n.
    (* cbn. *)
    let n := Std.eval_vm None '&n in
    let t := '(H $n) in
    let ty := Constr.type t in
    assert (x : $ty) by refine t.

    (* The script below simulates applying [H n] to [n] many telescopic types
       (expressed as nested lambdas to make typechecking interesting).

       The script includes repeated weak head reduction of the function and
       checking the function argument against the expected type. Neither
       operation are available to us directly so we make due with what we have:
       - For weak head reduction we use our own algorithm with MSP disabled
       - For typechecking we typecheck a cast

       In this first script we do not make use of MSP. [unblock] and [run] will
       be reduced as if they were projections (which they are in this file).
     *)
    Succeed
    let n := Std.eval_vm None '&n in
    let rec feed (n : constr) (i : constr) (term : constr) (ty : constr) :=
      lazy_match! n with
      | O => refine term
      | S ?n =>
          let ty := Std.eval_lazy_whnf red_flags_all ty in
          lazy_match! ty with
          | forall x : ?argty, @?ty x =>
              (* printf "argty = %t" argty; *)
              let x := make (App '@lams (Array.of_list [i;'nat; '(Blocked@{U} Type); '(block@{U} (nat:Type))])) in
              let x := Std.eval_lazy red_flags_all x in
              let _ := '($x : $argty) in
              feed n '(S $i) (make (App term (Array.of_list [x]))) (make (App ty (Array.of_list [x])))
          end
      end
    in
    let ty := Constr.type &x in
    time (feed n 'O &x ty).

    exact (H 0).
    (* Qed. *)

    Set Printing All. Set Printing Universes.
    Definition bla' := forall p : run (add_inner_exs true 1 (fun p : prop tO => reflect (simplify p))) (fun x => x),
        p (block (nat:Type)) = p (block (nat:Type)).
    Eval lazywhnf in run (add_inner_exs true 0 (fun p : prop tO => reflect (simplify p))) (fun x => x).
    Set Debug "backtrace".
    Show Proof.
    Time Qed.

    (* The next script uses MSP to perform the same task. However, to make the performance advantage visible,
       we do not count the time taken by our MSP-enabled reduction algorithm. Instead, we approximate the time
       it would take in the kernel by using [lazy] directly. This is OK because we do not have blocked terms that
       contain computation. We also run our own reduction algorithm and make sure that the result agrees.

       The total time taken is the sum of both individual timing results.
     *)
    let n := Std.eval_vm None '&n in
    let rec feed (n : constr) (i : constr) (term : constr) (ty : constr) :=
      lazy_match! n with
      | O => Std.exact_no_check term
      | S ?n =>
          let ty := old_reduce false Red.full_whd ty in
          lazy_match! ty with
          | forall x : ?argty, @?ty x =>
              let x := make (App '@lams (Array.of_list [i;'nat; '(Blocked Type); '(block (nat:Type))])) in
              let x := Std.eval_lazy red_flags_all x in
              let _ := '($x : $argty) in
              feed n '(S $i) (make (App term (Array.of_list [x]))) (make (App ty (Array.of_list [x])))
          end
      end
    in
    let ty := Constr.type &x in
    let ty := time (Std.eval_lazy red_flags_all ty) in
    (* let ty_ours := lazy_reduce false Red.full_whd (Constr.type &x) in *)
    (* (* [ty] and [ty_ours] should be identical but [lazy] also unfolds [unblock] even when it is not fully applied. *)
    (*    So we run one step of post-processing on our result. *)
    (*  *) *)
    (* let ty_ours := *)
    (*   Std.eval_lazy *)
    (*     {Std.rBeta:=true; Std.rDelta:=false; Std.rConst:=[reference:(unblock)]; *)
    (*      Std.rMatch:=false; Std.rFix:=false; Std.rCofix:=false; Std.rZeta:=false} *)
    (*     ty_ours *)
    (* in *)
    (* printf "ty = %t" ty; *)
    (* printf "ty_ours = %t" ty_ours; *)
    (* (if Constr.equal ty ty_ours then () else Control.throw (Invalid_argument None)); *)
    time (feed n 'O &x ty).
  Qed.

End WithTeleAndBlock.
