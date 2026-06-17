Declare ML Module "rocq-test-suite.attribute".

#[print]
Definition foo : True := I.

#[print]
Definition bar : False -> False := fun x => x.

Fail #[error]
Definition baz : False -> False := fun x => x.

(* Integer-literal attribute values (Attributes.int_attribute / int_parser). *)

#[size=0]
Definition i0 : True := I.

#[size=42]
Definition i1 : True := I.

(* Negative literals are accepted. *)
#[size=-7]
Definition i2 : True := I.

(* A string payload is not an integer. *)
Fail #[size="3"]
Definition i_bad_string : True := I.

(* A qualid is not an integer. *)
Fail #[size=three]
Definition i_bad_qualid : True := I.

(* The attribute may only be given once. *)
Fail #[size=1, size=2]
Definition i_twice : True := I.

(* par marshals the summary, enforcing that it doesn't contain closures *)
Lemma parfoo : True /\ True.
Proof.
  split.
  par: exact I.
Defined.
