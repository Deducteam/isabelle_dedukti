(****************************************************************************)
(* Type of non-empty types, used to interpret HOL-Light types. *)
(****************************************************************************)

Record Type' := { type :> Type; el : type }.

Definition Prop' : Type' := {| type := Prop; el := True |}.
Canonical Prop'.

Definition arr a (b : Type') := {| type := a -> b; el := fun _ => el b |}.
Canonical arr.

(****************************************************************************)
(* Curryfied versions of some Coq connectives. *)
(****************************************************************************)

Definition imp (p q : Prop) : Prop := p -> q.

Definition all (A:Type) (P:A->Prop) := forall x:A, P x.

(****************************************************************************)
(* Coq axioms necessary to handle HOL-Light proofs. *)
(****************************************************************************)

Axiom fun_ext : forall {A B : Type} {f g : A -> B}, (forall x, (f x) = (g x)) -> f = g.

Axiom prop_ext : forall {P Q : Prop}, (P -> Q) -> (Q -> P) -> P = Q.

Require Import ClassicalFacts Coq.Logic.ClassicalEpsilon.

Lemma prop_degen : forall P, P = True \/ P = False.
Proof.
  apply prop_ext_em_degen.
  unfold prop_extensionality. intros A B [AB BA]. apply prop_ext. exact AB. exact BA.
  intro P. apply classic.
Qed.

Definition ε : forall {A : Type'}, (type A -> Prop) -> type A := fun A P => epsilon (inhabits (el A)) P.

Lemma ε_spec {A : Type'} (P : type A -> Prop) : (exists x, P x) -> P (ε P).
Proof. intro h. unfold ε. apply epsilon_spec. exact h. Qed.

(****************************************************************************)
(* Pure. *)
(****************************************************************************)

Unset Automatic Proposition Inductives.
Inductive itself_ (A:Type') : Type := unit.
Definition itself (A:Type') := {| type := itself_ A; el := unit A |}.
Canonical itself.

Definition dummy : Type' := Prop'.

Definition dummy_pattern : forall a : Type', a := el.

Lemma equal_intr : forall A : Prop, forall B : Prop, (A -> B) -> (B -> A) -> @eq Prop A B.
Proof. intros A B AB BA. apply prop_ext. apply AB. apply BA. Qed.

Lemma equal_elim : forall A : Prop, forall B : Prop, (@eq Prop A B) -> A -> B.
Proof. intros A B AB a. rewrite <- AB. exact a. Qed.

Lemma abstract_rule : forall a : Type', forall b : Type', forall f : a -> b, forall g : a -> b, (all a (fun x : a => @eq b (f x) (g x))) -> @eq (a -> b) f g.
Proof. intros A B f g h. apply fun_ext. apply h. Qed.

Lemma combination : forall a : Type', forall b : Type', forall f : a -> b, forall g : a -> b, forall x : a, forall y : a, (@eq (a -> b) f g) -> (@eq a x y) -> @eq b (f x) (g y).
Proof.  intros a b f g x y fg xy. rewrite fg, xy. reflexivity. Qed.

Lemma conjunction_def : forall A : Prop, forall B : Prop, @eq Prop (and A B) (all Prop (fun C : Prop => (A -> B -> C) -> C)).
Proof.
  intros p q. apply prop_ext.
  intros [hp hq]. intros r h. apply (h hp hq).
  intro h. apply h. intros hp hq. split. exact hp. exact hq.
Qed.

Definition term (a : Type') : a -> Prop := fun x : a => all Prop (fun A : Prop => A -> A).

Definition sort_constraint : forall a : Type', (itself a) -> Prop := fun a _ => term (itself a) (unit a).

Lemma sort_constraint_def : forall a : Type', @eq Prop (sort_constraint a (unit a)) (term (itself a) (unit a)).
Proof. reflexivity. Qed.

(****************************************************************************)
(* HOL_HOL. *)
(****************************************************************************)

Definition Trueprop : Prop -> Prop := fun P => P.

Lemma impI : all Prop (fun P : Prop => all Prop (fun Q : Prop => ((Trueprop P) -> Trueprop Q) -> Trueprop (imp P Q))).
Proof. intros P Q PQ. exact PQ. Qed.

Lemma mp : all Prop (fun P : Prop => all Prop (fun Q : Prop => (Trueprop (imp P Q)) -> (Trueprop P) -> Trueprop Q)).
Proof. intros P Q h hP. apply (h hP). Qed.

Lemma True_or_False : all Prop (fun P : Prop => Trueprop (or (@eq Prop P True) (@eq Prop P False))).
Proof. intro P. apply prop_degen. Qed.

(****************************************************************************)
(* alignment of connectives *)

Lemma True_def_raw : @eq Prop True (@eq (Prop -> Prop) (fun x : Prop => x) (fun x : Prop => x)).
Proof. apply prop_ext. reflexivity. intros _; exact I. Qed.

Lemma All_def_raw : forall a : Type', @eq ((a -> Prop) -> Prop) (@all a) (fun P : a -> Prop => @eq (a -> Prop) P (fun x : a => True)).
Proof.
  intro A. apply fun_ext; intro p. apply prop_ext.
  intro h. apply fun_ext; intro x. apply prop_ext.
  intros _. exact I. intros _. exact (h x).
  intros e x. rewrite e. exact I.
Qed.

Lemma Ex_def_raw : forall a : Type', @eq ((a -> Prop) -> Prop) (@ex a) (fun P : a -> Prop => @all Prop (fun Q : Prop => imp (@all a (fun x : a => imp (P x) Q)) Q)).
Proof.
  intro A. apply fun_ext; intro p. apply prop_ext.
  intros [x px] q pq. eapply pq. apply px.
  intro h. apply h. intros x px. apply (ex_intro p x px).
Qed.

Lemma False_def_raw : @eq Prop False (@all Prop (fun P : Prop => P)).
Proof. apply prop_ext. intros b p. apply (False_rec p b). intro h. exact (h False). Qed.

Lemma not_def_raw : @eq (Prop -> Prop) not (fun P : Prop => imp P False).
Proof. reflexivity. Qed.

Lemma and_def_raw : @eq (Prop -> Prop -> Prop) and (fun P : Prop => fun Q : Prop => @all Prop (fun R : Prop => imp (imp P (imp Q R)) R)).
Proof.
  apply fun_ext; intro p. apply fun_ext; intro q. apply prop_ext.
  intros [hp hq]. intros r h. apply (h hp hq).
  intro h. apply h. intros hp hq. split. exact hp. exact hq.
Qed.

Lemma or_def_raw : @eq (Prop -> Prop -> Prop) or (fun P : Prop => fun Q : Prop => @all Prop (fun R : Prop => imp (imp P R) (imp (imp Q R) R))).
Proof.
  apply fun_ext; intro p; apply fun_ext; intro q. apply prop_ext.
  intros pq r pr qr. destruct pq. apply (pr H). apply (qr H).
  intro h. apply h. intro hp. left. exact hp. intro hq. right. exact hq.
Qed.

(****************************************************************************)
(* class type (top class) *)

Definition type_class : Type' -> Prop := fun A => True.

Lemma eq_reflection : forall a : Type', (type_class a) -> all a (fun x : a => all a (fun y : a => (Trueprop (@eq a x y)) -> @eq a x y)).
Proof. intros a _ x y xy. apply xy. Qed.

Lemma refl : forall a : Type', (type_class a) -> all a (fun t : a => Trueprop (@eq a t t)).
Proof. intros a _ t. reflexivity. Qed.

Lemma subst : forall a : Type', (type_class a) -> all a (fun t : a => all a (fun s : a => all (a -> Prop) (fun P : a -> Prop => (Trueprop (@eq a s t)) -> (Trueprop (P s)) -> Trueprop (P t)))).
Proof. intros a _ t s P st Ps. rewrite <- st. exact Ps. Qed.

Lemma ext : forall a : Type', forall b : Type', (type_class a) -> (type_class b) -> all (a -> b) (fun f : a -> b => all (a -> b) (fun g : a -> b => (all a (fun x : a => Trueprop (@eq b (f x) (g x)))) -> Trueprop (@eq (a -> b) f g))).
Proof. intros a b _ _ f g fg. apply fun_ext. apply fg. Qed.

Lemma the_eq_trivial : forall A : Type', (type_class A) -> all A (fun a : A => Trueprop (@eq A (@ε A (fun x : A => @eq A x a)) a)).
Proof. intros a _ x. apply ε_spec. exists x. reflexivity. Qed.

Lemma fun_arity : forall a : Type', forall b : Type', (type_class a) -> (type_class b) -> type_class (a -> b).
Proof. unfold type_class; auto. Qed.

Lemma itself_arity : forall a : Type', (type_class a) -> type_class (itself a).
Proof. unfold type_class; auto. Qed.

Lemma arity_type_bool : type_class Prop.
Proof. unfold type_class; auto. Qed.
