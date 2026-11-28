Class Big (n : nat) := {}.
Instance bigO : Big O := {}.
Instance bigS n : Big n -> Big (S n) := fun _ => Build_Big _.
Instance big_cheat n : Big n | 100 := {}.

(* Typeclasses Depth backtracks into big_cheat when the limit is hit. *)
Set Typeclasses Depth 100.
Goal Big 1000. Proof. apply _. Qed.
Unset Typeclasses Depth.

(* Typeclasses Fatal Depth reports an error instead. *)
Set Typeclasses Fatal Depth 100.
Goal Big 1000. Proof. Fail apply _. Abort.
Goal Big 1000. Proof. Fail typeclasses eauto. Abort.
(* Implicit resolution reports it too, rather than leaving the evar. *)
Fail Definition d : Big 1000 := _.
(* Ltac try, first and || pass it on instead of trying alternatives. *)
Goal Big 1000. Proof.
  Fail try apply _.
  Fail first [apply _ | exact (big_cheat _)].
  Fail (typeclasses eauto || exact (big_cheat _)).
Abort.

(* Same boundary as Typeclasses Depth. *)
Goal Big 99. Proof. apply _. Qed.
Goal Big 100. Proof. Fail apply _. Abort.
Unset Typeclasses Fatal Depth.
Set Typeclasses Depth 100.
Class Big2 (n : nat) := {}.
Instance big2O : Big2 O := {}.
Instance big2S n : Big2 n -> Big2 (S n) := fun _ => Build_Big2 _.
Goal Big2 99. Proof. apply _. Qed.
Goal Big2 100. Proof. Fail apply _. Abort.
Unset Typeclasses Depth.

(* A loop with a working instance tried later: Typeclasses Depth hides the
   loop, Typeclasses Fatal Depth reports it. *)
Class A := {}.
Class B := {}.
Instance loopA : B -> A | 0 := {}.
Instance loopB : A -> B | 0 := {}.
Instance okA : A | 10 := {}.
Set Typeclasses Fatal Depth 20.
Fail Definition x : A := _.
Unset Typeclasses Fatal Depth.
Set Typeclasses Depth 20.
Definition x : A := _.

(* Typeclasses Warn Depth reports deep searches, successful or not. *)
Unset Typeclasses Depth.
Set Typeclasses Warn Depth 50.
Set Warnings "+typeclasses-deep-search".
Goal Big2 40. Proof. apply _. Qed.
Fail Definition y : Big2 60 := _.
Set Warnings "-typeclasses-deep-search".
Definition y : Big2 60 := _.
