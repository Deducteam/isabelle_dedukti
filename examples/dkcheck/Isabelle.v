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

Definition term : forall _a_ : Type', _a_ -> Prop := fun _a_ x_ => all Prop (fun A_ : Prop => A_ -> A_).

Definition sort_constraint : forall _a_ : Type', ( _a_) -> Prop := fun _a_ _x => term ( _a_) _x.

Definition conjunction : Prop -> Prop -> Prop := fun A_ B_ => all Prop (fun C_ : Prop => (A_ -> B_ -> C_) -> C_).

Lemma term_def : forall _a_ : Type', forall x_ : _a_, @eq Prop (term _a_ x_) (all Prop (fun A_ : Prop => A_ -> A_)).
Proof. reflexivity. Qed.

Lemma sort_constraint_def : forall _a_ : Type', @eq Prop (sort_constraint _a_ (el _a_)) (term ( _a_) (el _a_)).
Proof. reflexivity. Qed.

Lemma conjunction_def : forall A_ : Prop, forall B_ : Prop, @eq Prop (conjunction A_ B_) (all Prop (fun C_ : Prop => (A_ -> B_ -> C_) -> C_)).
Proof. reflexivity. Qed.

(****************************************************************************)
(* Tools_Code_Generator. *)
(****************************************************************************)

Definition holds : Prop := @eq (Prop -> Prop) (fun x_ : Prop => x_) (fun x_ : Prop => x_).

Lemma holds_def_raw : @eq Prop holds (@eq (Prop -> Prop) (fun x_ : Prop => x_) (fun x_ : Prop => x_)).
Proof. reflexivity. Qed.

(****************************************************************************)
(* HOL_HOL. *)
(****************************************************************************)

Definition Trueprop : Prop -> Prop := fun P => P.

Definition undefined : forall _a_ : Type', _a_ := el.

Definition default_class_default : forall _a_ : Type', _a_ := el.

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

Definition The : forall _a_ : Type', (_a_ -> Prop) -> _a_ := @ε.

Definition Uniq : forall _a_ : Type', (_a_ -> Prop) -> Prop := fun _a_ => (fun P_ : _a_ -> Prop => @all _a_ (fun x_ : _a_ => @all _a_ (fun y_ : _a_ => imp (P_ x_) (imp (P_ y_) (@eq _a_ y_ x_))))).

Lemma Uniq_def_raw : forall _a_ : Type', @eq ((_a_ -> Prop) -> Prop) (Uniq _a_) (fun P_ : _a_ -> Prop => @all _a_ (fun x_ : _a_ => @all _a_ (fun y_ : _a_ => imp (P_ x_) (imp (P_ y_) (@eq _a_ y_ x_))))).
Proof. reflexivity. Qed.

Definition Ex1 : forall _a_ : Type', (_a_ -> Prop) -> Prop := fun _a_ => (fun P_ : _a_ -> Prop => @ex _a_ (fun x_ : _a_ => and (P_ x_) (@all _a_ (fun y_ : _a_ => imp (P_ y_) (@eq _a_ y_ x_))))).

Lemma Ex1_def_raw : forall _a_ : Type', @eq ((_a_ -> Prop) -> Prop) (Ex1 _a_) (fun P_ : _a_ -> Prop => @ex _a_ (fun x_ : _a_ => and (P_ x_) (@all _a_ (fun y_ : _a_ => imp (P_ y_) (@eq _a_ y_ x_))))).
Proof. reflexivity. Qed.

(*
Axiom refl : forall _a_ : Type', (type_class _a_) -> all _a_ (fun t_ : _a_ => Trueprop (@eq _a_ t_ t_)).
Axiom subst : forall _a_ : Type', (type_class _a_) -> all _a_ (fun t_ : _a_ => all _a_ (fun s_ : _a_ => all (_a_ -> Prop) (fun P_ : _a_ -> Prop => (Trueprop (@eq _a_ s_ t_)) -> (Trueprop (P_ s_)) -> Trueprop (P_ t_)))).
Axiom ext : forall _a_ : Type', forall _b_ : Type', (type_class _a_) -> (type_class _b_) -> all (_a_ -> _b_) (fun f_ : _a_ -> _b_ => all (_a_ -> _b_) (fun g_ : _a_ -> _b_ => (all _a_ (fun x_ : _a_ => Trueprop (@eq _b_ (f_ x_) (g_ x_)))) -> Trueprop (@eq (_a_ -> _b_) f_ g_))).
Axiom the_eq_trivial : forall _a_ : Type', (type_class _a_) -> all _a_ (fun a_ : _a_ => Trueprop (@eq _a_ (The _a_ (fun x_ : _a_ => @eq _a_ x_ a_)) a_)).
*)

Lemma impI : all Prop (fun P_ : Prop => all Prop (fun Q_ : Prop => ((Trueprop P_) -> Trueprop Q_) -> Trueprop (imp P_ Q_))).
Proof. intros P Q PQ. exact PQ. Qed.

Lemma mp : all Prop (fun P_ : Prop => all Prop (fun Q_ : Prop => (Trueprop (imp P_ Q_)) -> (Trueprop P_) -> Trueprop Q_)).
Proof. intros P Q h hP. apply (h hP). Qed.

Lemma True_or_False : all Prop (fun P_ : Prop => Trueprop (or (@eq Prop P_ True) (@eq Prop P_ False))).
Proof. intro P. apply prop_degen. Qed.

Definition If : forall _a_ : Type', Prop -> _a_ -> _a_ -> _a_ := fun _a_ => (fun P_ : Prop => fun x_ : _a_ => fun y_ : _a_ => The _a_ (fun z_ : _a_ => and (imp (@eq Prop P_ True) (@eq _a_ z_ x_)) (imp (@eq Prop P_ False) (@eq _a_ z_ y_)))).

Lemma If_def_raw : forall _a_ : Type', @eq (Prop -> _a_ -> _a_ -> _a_) (If _a_) (fun P_ : Prop => fun x_ : _a_ => fun y_ : _a_ => The _a_ (fun z_ : _a_ => and (imp (@eq Prop P_ True) (@eq _a_ z_ x_)) (imp (@eq Prop P_ False) (@eq _a_ z_ y_)))).
Proof. reflexivity. Qed.

Definition Let : forall _a_ : Type', forall _b_ : Type', _a_ -> (_a_ -> _b_) -> _b_ := fun _a_ _b_ => (fun s_ : _a_ => fun f_ : _a_ -> _b_ => f_ s_).

Lemma Let_def_raw : forall _a_ : Type', forall _b_ : Type', @eq (_a_ -> (_a_ -> _b_) -> _b_) (Let _a_ _b_) (fun s_ : _a_ => fun f_ : _a_ -> _b_ => f_ s_).
Proof. reflexivity. Qed.

(*
Axiom default_class_def : forall _a_ : Type', @eq Prop (default _a_) (type_class _a_).
Axiom eq_reflection : forall _a_ : Type', (type_class _a_) -> all _a_ (fun x_ : _a_ => all _a_ (fun y_ : _a_ => (Trueprop (@eq _a_ x_ y_)) -> @eq _a_ x_ y_)).
*)
Lemma simp_implies_def_raw : @eq (Prop -> Prop -> Prop) imp imp.
Proof. reflexivity. Qed.

Lemma induct_forall_def_raw : forall _a_ : Type', @eq ((_a_ -> Prop) -> Prop) (all _a_) (@all _a_).
Proof. reflexivity. Qed.

Lemma induct_implies_def_raw : @eq (Prop -> Prop -> Prop) imp imp.
Proof. reflexivity. Qed.

Lemma induct_equal_def_raw : forall _a_ : Type', @eq (_a_ -> _a_ -> Prop) (@eq _a_) (@eq _a_).
Proof. reflexivity. Qed.

Lemma induct_conj_def_raw : @eq (Prop -> Prop -> Prop) and and.
Proof. reflexivity. Qed.

Lemma induct_true_def_raw : @eq Prop True True.
Proof. reflexivity. Qed.

Lemma induct_false_def_raw : @eq Prop False False.
Proof. reflexivity. Qed.

Definition NO_MATCH : forall _a_ : Type', forall _b_ : Type', _a_ -> _b_ -> Prop := fun _a_ _b_ => (fun pat_ : _a_ => fun val_ : _b_ => True).

Lemma NO_MATCH_def_raw : forall _a_ : Type', forall _b_ : Type', @eq (_a_ -> _b_ -> Prop) (NO_MATCH _a_ _b_) (fun pat_ : _a_ => fun val_ : _b_ => True).
Proof. reflexivity. Qed.

Definition ASSUMPTION : Prop -> Prop := (fun A_ : Prop => A_).

Lemma ASSUMPTION_def_raw : @eq (Prop -> Prop) ASSUMPTION (fun A_ : Prop => A_).
Proof. reflexivity. Qed.

Definition class_equal : forall _a_ : Type', (_a_ -> _a_ -> Prop) -> Prop := fun _a_ equal_ => (@all _a_ (fun x_ : _a_ => @all _a_ (fun y_ : _a_ => @eq Prop (equal_ x_ y_) (@eq _a_ x_ y_)))).

Lemma class_equal_def : forall _a_ : Type', forall equal_ : _a_ -> _a_ -> Prop, @eq Prop (class_equal _a_ equal_) (@all _a_ (fun x_ : _a_ => @all _a_ (fun y_ : _a_ => @eq Prop (equal_ x_ y_) (@eq _a_ x_ y_)))).
Proof. reflexivity. Qed.

(*
Axiom equal_class_def : forall _a_ : Type', @eq Prop (equal _a_) (Pure.conjunction (type_class _a_) (Trueprop (class_equal _a_ (equal_class_equal _a_)))).

Axiom equal_itself_inst_equal_itself_def : forall _a_ : Type', @eq (( _a_) -> ( _a_) -> Prop) (equal_class_equal ( _a_)) (equal_itself_inst_equal_itself _a_).

Axiom equal_itself_def_raw : forall _a_ : Type', @eq (( _a_) -> ( _a_) -> Prop) (equal_itself_inst_equal_itself _a_) (@eq ( _a_)).
*)
