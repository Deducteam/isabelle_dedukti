Unset Implicit Arguments.

Record Type' := { ty :> Type; el : ty }.

Definition Prop' : Type' := {| ty := Prop; el := True |}.
Canonical Prop'.

Definition unit' := {| ty := unit; el := tt |}.
Canonical unit'.

Definition nat' := {| ty := nat; el := 0 |}.
Canonical nat'.

Definition prod (a b : Type') := {| ty := a * b; el := pair (el a) (el b) |}.
Canonical prod.

Definition arr a (b : Type') := {| ty := a -> b; el := fun _ => el b |}.
Canonical arr.

Definition imp (P Q: Prop) := P -> Q.

Definition all (A:Type) (P:A->Prop) := forall x:A, P x.

Lemma dummy : Type.
Proof.
  exact Prop.
Qed.

Lemma type : forall _a : Type',  _a.
Proof.
  intro a. destruct a. apply Build_Type'.
Qed.

Lemma dummy_pattern : forall _a : Type', _a.
Proof.
  intro a. destruct a. apply Build_Type'.
Qed.

Lemma combination : forall _a : Type, forall _b : Type, forall f : _a -> _b, forall g : _a -> _b, forall x : _a, forall y : _a, (@eq (_a -> _b) f g) -> (@eq _a x y) -> @eq _b (f x) (g y).
Proof.
  intros a b f g x y fg xy. rewrite fg, xy. reflexivity.
Qed.

Lemma Trueprop : Prop -> Prop.
Proof.
  intro A. exact A.
Qed.

Lemma undefined : forall _a : Type',  _a.
Proof.
  intro a. destruct a. apply Build_Type'.
Qed.
