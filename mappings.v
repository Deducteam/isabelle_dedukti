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

(* Basically, extend intros so that it tries these as possible reductions *)
Tactic Notation "ext" ne_simple_intropattern_list(l) :=
  let rec ext' continuation := continuation ||
    (let H := fresh "internal" in match goal with
      | |- forall _,_ => intro H
      | _ => first [apply fun_ext | apply prop_ext] ; intro H end ;
      ext' ltac:(revert H ; continuation))
  in ext' ltac:(intros l).

From Stdlib Require Import ClassicalFacts ClassicalEpsilon.

Lemma prop_degen : forall P, P = True \/ P = False.
Proof.
  apply prop_ext_em_degen.
  - unfold prop_extensionality. intros A B [AB BA]. apply prop_ext.
    + exact AB.
    + exact BA.
  - intro P. apply classic.
Qed.

Definition ε : forall {A : Type'}, (type A -> Prop) -> type A := fun A P => epsilon (inhabits (el A)) P.

Lemma ε_spec {A : Type'} (P : type A -> Prop) : (exists x, P x) -> P (ε P).
Proof. intro h. unfold ε. apply epsilon_spec. exact h. Qed.

(****************************************************************************)
(* Pure. *)
(****************************************************************************)

Inductive itself_ (A:Type') : Type := unit.
Definition itself (A:Type') := {| type := itself_ A; el := unit A |}.
Canonical itself.

Definition equal_intr : forall A : Prop, forall B : Prop, (A -> B) -> (B -> A) -> A = B := @prop_ext.

Lemma equal_elim : forall A : Prop, forall B : Prop, A = B -> A -> B.
Proof.
  intros * ->. exact id.
Qed.

Definition abstract_rule : forall (a b : Type') (f g : a -> b),
  (forall x : a, f x = g x) -> f = g := @fun_ext.

Lemma combination (a b : Type') (f g : a -> b) (x y : a) :
  f = g -> x = y -> f x = g y.
Proof.
  intros * -> ->. reflexivity.
Qed.

Lemma conjunction_def A B : (A /\ B) = forall C, (A -> B -> C) -> C.
Proof.
  ext HAB.
  - intros C HABC. exact (HABC (proj1 HAB) (proj2 HAB)).
  - apply HAB. intros HA HB. split. exact HA. exact HB.
Qed.

Definition term (a : Type') : a -> Prop := fun x : a => all Prop (fun A : Prop => A -> A).

Lemma term_def (_a__var : Type') (x__var : _a__var) : @eq Prop (term _a__var x__var) (all Prop (fun A__var : Prop => A__var -> A__var)).
Proof. exact (@eq_refl Prop (term _a__var x__var)). Qed.

Definition sort_constraint : forall a : Type', (itself a) -> Prop := fun a _ => term (itself a) (unit a).

Lemma sort_constraint_def : forall a : Type', @eq Prop (sort_constraint a (unit a)) (term (itself a) (unit a)).
Proof. reflexivity. Qed.

(****************************************************************************)
(* HOL_HOL. *)
(****************************************************************************)

Definition Trueprop : Prop -> Prop := fun P => P.

Lemma impI : forall P Q, ((Trueprop P) -> Trueprop Q) -> Trueprop (P -> Q).
Proof. exact (fun _ _ => id). Qed.

Lemma mp : forall P Q, (Trueprop (P -> Q)) -> (Trueprop P) -> Trueprop Q.
Proof. exact (fun _ _ => id). Qed.

Definition True_or_False : forall P, Trueprop (P = True \/ P = False) := prop_degen.

(****************************************************************************)
(* alignment of connectives *)

Lemma True_def_raw : True = ((fun x : Prop => x) = (fun x : Prop => x)).
Proof. ext _ ; reflexivity. Qed.

Lemma All_def_raw : forall a : Type', (@all a) = (fun P : a -> Prop => P = (fun x : a => True)).
Proof.
  ext A P H.
  - ext a H'.
    + exact I.
    + exact (H a).
  - rewrite H. exact (fun _ => I).
Qed.

Lemma Ex_def_raw : forall a : Type', (@ex a) = (fun P : a -> Prop => forall Q : Prop, (forall x : a, P x -> Q) -> Q).
Proof.
  ext A P H.
  - destruct H as [y Hy]. exact (fun Q HQ => HQ y Hy).
  - exact (H _ (ex_intro _)).
Qed.

Lemma False_def_raw : False = (forall P : Prop, P).
Proof. ext contra. destruct contra. exact (contra _). Qed.

Lemma not_def_raw : not = (fun P : Prop => P -> False).
Proof. reflexivity. Qed.

Lemma and_def_raw : and = (fun P : Prop => fun Q : Prop => forall R : Prop, (P -> Q -> R) -> R).
Proof.
  ext P Q HPQ.
  - exact (fun _ HPQ' => and_ind HPQ' HPQ).
  - apply HPQ. split ; assumption.
Qed.

Lemma or_def_raw : or = (fun P : Prop => fun Q : Prop => forall R : Prop, (P -> R) -> (Q -> R) -> R).
Proof.
  ext P Q HPQ.
  - exact (fun _ HP HQ => or_ind HP HQ HPQ).
  - exact (HPQ _ (@or_introl _ _) (@or_intror _ _)).
Qed.

(****************************************************************************)
(* class type (top class) *)

Axiom type_class : Type' -> Prop.

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
