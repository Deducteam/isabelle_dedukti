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

Inductive itself_ (A:Type') : Type := unit.
Definition itself (A:Type') := {| type := itself_ A; el := unit A |}.
Canonical itself.

Definition dummy : Type' := Prop'.

Definition dummy_pattern : forall _a_ : Type', _a_ := el.

Lemma equal_intr : forall A_ : Prop, forall B_ : Prop, (A_ -> B_) -> (B_ -> A_) -> @eq Prop A_ B_.
Proof. intros A B AB BA. apply prop_ext. apply AB. apply BA. Qed.

Lemma equal_elim : forall A_ : Prop, forall B_ : Prop, (@eq Prop A_ B_) -> A_ -> B_.
Proof. intros A B AB a. rewrite <- AB. exact a. Qed.

Lemma abstract_rule : forall _a_ : Type', forall _b_ : Type', forall f_ : _a_ -> _b_, forall g_ : _a_ -> _b_, (all _a_ (fun x_ : _a_ => @eq _b_ (f_ x_) (g_ x_))) -> @eq (_a_ -> _b_) f_ g_.
Proof. intros A B f g h. apply fun_ext. apply h. Qed.

Lemma combination : forall _a_ : Type', forall _b_ : Type', forall f_ : _a_ -> _b_, forall g_ : _a_ -> _b_, forall x_ : _a_, forall y_ : _a_, (@eq (_a_ -> _b_) f_ g_) -> (@eq _a_ x_ y_) -> @eq _b_ (f_ x_) (g_ y_).
Proof.  intros a b f g x y fg xy. rewrite fg, xy. reflexivity. Qed.

Lemma conjunction_def : forall A_ : Prop, forall B_ : Prop, @eq Prop (and A_ B_) (all Prop (fun C_ : Prop => (A_ -> B_ -> C_) -> C_)).
Proof.
  intros p q. apply prop_ext.
  intros [hp hq]. intros r h. apply (h hp hq).
  intro h. apply h. intros hp hq. split. exact hp. exact hq.
Qed.

(*Definition sort_constraint : forall _a_ : Type', (itself _a_) -> Prop := fun _a_ _x => term ( itself _a_) _x.

Lemma sort_constraint_def : forall _a_ : Type', @eq Prop (sort_constraint _a_ (unit _a_)) (term ( _a_) (el _a_)).
Proof. reflexivity. Qed.*)

(****************************************************************************)
(* HOL_HOL. *)
(****************************************************************************)

Definition Trueprop : Prop -> Prop := fun P => P.

Lemma impI : all Prop (fun P_ : Prop => all Prop (fun Q_ : Prop => ((Trueprop P_) -> Trueprop Q_) -> Trueprop (imp P_ Q_))).
Proof. intros P Q PQ. exact PQ. Qed.

Lemma mp : all Prop (fun P_ : Prop => all Prop (fun Q_ : Prop => (Trueprop (imp P_ Q_)) -> (Trueprop P_) -> Trueprop Q_)).
Proof. intros P Q h hP. apply (h hP). Qed.

Lemma True_or_False : all Prop (fun P_ : Prop => Trueprop (or (@eq Prop P_ True) (@eq Prop P_ False))).
Proof. intro P. apply prop_degen. Qed.

(****************************************************************************)
(* alignment of connectives *)

Lemma True_def_raw : @eq Prop True (@eq (Prop -> Prop) (fun x_ : Prop => x_) (fun x_ : Prop => x_)).
Proof. apply prop_ext. reflexivity. intros _; exact I. Qed.

Lemma All_def_raw : forall _a_ : Type', @eq ((_a_ -> Prop) -> Prop) (@all _a_) (fun P_ : _a_ -> Prop => @eq (_a_ -> Prop) P_ (fun x_ : _a_ => True)).
Proof.
  intro A. apply fun_ext; intro p. apply prop_ext.
  intro h. apply fun_ext; intro x. apply prop_ext.
  intros _. exact I. intros _. exact (h x).
  intros e x. rewrite e. exact I.
Qed.

Lemma Ex_def_raw : forall _a_ : Type', @eq ((_a_ -> Prop) -> Prop) (@ex _a_) (fun P_ : _a_ -> Prop => @all Prop (fun Q_ : Prop => imp (@all _a_ (fun x_ : _a_ => imp (P_ x_) Q_)) Q_)).
Proof.
  intro A. apply fun_ext; intro p. apply prop_ext.
  intros [x px] q pq. eapply pq. apply px.
  intro h. apply h. intros x px. apply (ex_intro p x px).
Qed.

Lemma False_def_raw : @eq Prop False (@all Prop (fun P_ : Prop => P_)).
Proof. apply prop_ext. intros b p. apply (False_rec p b). intro h. exact (h False). Qed.

Lemma not_def_raw : @eq (Prop -> Prop) not (fun P_ : Prop => imp P_ False).
Proof. reflexivity. Qed.

Lemma and_def_raw : @eq (Prop -> Prop -> Prop) and (fun P_ : Prop => fun Q_ : Prop => @all Prop (fun R_ : Prop => imp (imp P_ (imp Q_ R_)) R_)).
Proof.
  apply fun_ext; intro p. apply fun_ext; intro q. apply prop_ext.
  intros [hp hq]. intros r h. apply (h hp hq).
  intro h. apply h. intros hp hq. split. exact hp. exact hq.
Qed.

Lemma or_def_raw : @eq (Prop -> Prop -> Prop) or (fun P_ : Prop => fun Q_ : Prop => @all Prop (fun R_ : Prop => imp (imp P_ R_) (imp (imp Q_ R_) R_))).
Proof.
  apply fun_ext; intro p; apply fun_ext; intro q. apply prop_ext.
  intros pq r pr qr. destruct pq. apply (pr H). apply (qr H).
  intro h. apply h. intro hp. left. exact hp. intro hq. right. exact hq.
Qed.

(****************************************************************************)
(* class type (top class) *)

Definition type_class : Type' -> Prop := fun A => True.

Lemma eq_reflection : forall _a_ : Type', (type_class _a_) -> all _a_ (fun x_ : _a_ => all _a_ (fun y_ : _a_ => (Trueprop (@eq _a_ x_ y_)) -> @eq _a_ x_ y_)).
Proof. intros a _ x y xy. apply xy. Qed.

Lemma refl : forall _a__var : Type', (type_class _a__var) -> all _a__var (fun t__var : _a__var => Trueprop (@eq _a__var t__var t__var)).
Proof. intros a _ t. reflexivity. Qed.

Lemma subst : forall _a__var : Type', (type_class _a__var) -> all _a__var (fun t__var : _a__var => all _a__var (fun s__var : _a__var => all (_a__var -> Prop) (fun P__var : _a__var -> Prop => (Trueprop (@eq _a__var s__var t__var)) -> (Trueprop (P__var s__var)) -> Trueprop (P__var t__var)))).
Proof. intros a _ t s P st Ps. rewrite <- st. exact Ps. Qed.

Lemma ext : forall _a__var : Type', forall _b__var : Type', (type_class _a__var) -> (type_class _b__var) -> all (_a__var -> _b__var) (fun f__var : _a__var -> _b__var => all (_a__var -> _b__var) (fun g__var : _a__var -> _b__var => (all _a__var (fun x__var : _a__var => Trueprop (@eq _b__var (f__var x__var) (g__var x__var)))) -> Trueprop (@eq (_a__var -> _b__var) f__var g__var))).
Proof. intros a b _ _ f g fg. apply fun_ext. apply fg. Qed.

Lemma the_eq_trivial : forall _a__var : Type', (type_class _a__var) -> all _a__var (fun a__var : _a__var => Trueprop (@eq _a__var (@ε _a__var (fun x__var : _a__var => @eq _a__var x__var a__var)) a__var)).
Proof. intros a _ x. apply ε_spec. exists x. reflexivity. Qed.

Lemma fun_arity : forall _a__var : Type', forall _b__var : Type', (type_class _a__var) -> (type_class _b__var) -> type_class (_a__var -> _b__var).
Proof. unfold type_class; auto. Qed.

Lemma itself_arity : forall _a__var : Type', (type_class _a__var) -> type_class (itself _a__var).
Proof. unfold type_class; auto. Qed.

Lemma arity_type_bool : type_class Prop.
Proof. unfold type_class; auto. Qed.

(****************************************************************************)
(* class default *)

Axiom default_class_default : forall _a_ : Type', _a_.

Definition default : Type' -> Prop := fun _a__var : Type' => type_class _a__var.

Lemma default_class_def : forall _a__var : Type', @eq Prop (default _a__var) (type_class _a__var).
Proof. reflexivity. Qed.

(****************************************************************************)
(* class equal *)

Definition class_equal : forall _a_ : Type', (_a_ -> _a_ -> Prop) -> Prop := fun _a_ equal_ => (@all _a_ (fun x_ : _a_ => @all _a_ (fun y_ : _a_ => @eq Prop (equal_ x_ y_) (@eq _a_ x_ y_)))).

Lemma class_equal_def : forall _a_ : Type', forall equal_ : _a_ -> _a_ -> Prop, @eq Prop (class_equal _a_ equal_) (@all _a_ (fun x_ : _a_ => @all _a_ (fun y_ : _a_ => @eq Prop (equal_ x_ y_) (@eq _a_ x_ y_)))).
Proof. reflexivity. Qed.

(*Class equal_class (_a__var : Type') := { equal_class_equal: _a__var -> _a__var -> Prop }.*)

Axiom equal_class_equal : forall _a__var : Type', _a__var -> _a__var -> Prop.

Definition equal := fun _a_ : Type' => and (type_class _a_) (Trueprop (class_equal _a_ (equal_class_equal _a_))).

(*Definition equal (_a_ : Type') {c:equal_class _a_} := and (type_class _a_) (Trueprop (class_equal _a_ (@equal_class_equal _a_ c))).*)

Lemma equal_class_def : forall _a_ : Type', @eq Prop (equal _a_) (and (type_class _a_) (Trueprop (class_equal _a_ (equal_class_equal _a_)))).
Proof. reflexivity. Qed.

(*Lemma equal_class_def (_a_ : Type') {c:equal_class _a_} : @eq Prop (equal _a_) (and (type_class _a_) (Trueprop (class_equal _a_ (@equal_class_equal _a_ c)))).
Proof. reflexivity. Qed.*)

(*
Axiom equal_itself_inst_equal_itself_def : forall _a_ : Type', @eq (( _a_) -> ( _a_) -> Prop) (equal_class_equal ( _a_)) (equal_itself_inst_equal_itself _a_).

Axiom equal_itself_def_raw : forall _a_ : Type', @eq (( _a_) -> ( _a_) -> Prop) (equal_itself_inst_equal_itself _a_) (@eq ( _a_)).
*)
