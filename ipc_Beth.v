Require Import Ensembles Relations.
Set Implicit Arguments.
Implicit Arguments In [U].

Definition var := nat.
Inductive formula : Set :=
| Atom : var -> formula
| Bot : formula
| And : formula -> formula -> formula
| Or : formula -> formula -> formula
| Imp : formula -> formula -> formula.
Infix "'->" := Imp (at level 70, right associativity).
Infix "'\/" := Or (at level 60).
Infix "'/\" := And (at level 50).
(* Definition Not f := f '-> Bot.  *)
(* Definition Top := Bot '-> Bot. *)
Coercion Atom : var >-> formula.

Inductive provable : Ensemble formula -> formula -> Prop :=
| By_axiom : forall fs f, In fs f -> provable fs f
| By_K : forall fs f g, provable fs (f '-> g '-> f)
| By_S : forall fs f g h,
  provable fs ((f '-> g '-> h) '-> (f '-> g) '-> (f '-> h))
| By_proj1 : forall fs f g, provable fs (f '/\ g '-> f)
| By_proj2 : forall fs f g, provable fs (f '/\ g '-> g)
| By_conj : forall fs f g, provable fs (f '-> g '-> f '/\ g)
| By_in1 : forall fs f g, provable fs (f '-> f '\/ g)
| By_in2 : forall fs f g, provable fs (g '-> f '\/ g)
| By_case : forall fs f g h,
  provable fs ((f '-> h) '-> (g '-> h) '-> (f '\/ g '-> h))
| By_MP : forall fs f g,
  provable fs (f '-> g) -> provable fs f -> provable fs g.

Hint Constructors provable.

Module Type BETH_MODEL.
  Parameter W : Type.
  Parameter R : relation W.
  Axiom R_refl : reflexive _ R.
  Axiom R_trans : transitive _ R.
  Parameter V : W -> var -> Prop.
  Axiom monotone : forall x y p, V x p -> R x y -> V y p.
  Axiom atom_covering : forall x p,
    (forall y, R x y -> exists z, R y z /\ V z p) -> V x p.
End BETH_MODEL.

Module Beth_Semantics (M : BETH_MODEL).
  Include M.

  Fixpoint satisfies x f :=
    match f with
      | Atom p => V x p
      | Bot => False
      | And f f' => satisfies x f /\ satisfies x f'
      | Or f f' => forall y, R x y -> exists z,
        R y z /\ (satisfies z f \/ satisfies z f')
      | Imp f f' => forall y, R x y -> satisfies y f -> satisfies y f'
    end.

  Hint Resolve R_refl R_trans monotone.
  Lemma hereditary : forall x y f, 
    satisfies x f -> R x y -> satisfies y f.
    induction f; simpl; intuition eauto.
  Qed.

  Lemma covering : forall f x,
    (forall y, R x y -> exists z, R y z /\ satisfies z f) ->
    satisfies x f.
    induction f; simpl; intuition eauto using atom_covering.

    destruct (H x); firstorder.

    destruct (H x); intuition.
    apply IHf1; intuition.
    destruct (H y); intuition.
    eauto.

    destruct (H x); intuition.
    apply IHf2; intuition.
    destruct (H y); intuition; eauto.

    destruct (H y); intuition.
    destruct (H3 x0); intuition; eauto.

    destruct (H y); intuition.
    apply IHf2; intuition.
    destruct (H y0); intuition; eauto.
    eauto 6 using hereditary.
  Qed.


  Theorem soundness : forall fs f x,
    provable fs f -> (forall g, In fs g -> satisfies x g) -> satisfies x f.
    induction 1; simpl; intuition; eauto using hereditary.

    apply covering; intuition.
    destruct H5 with y2; intuition.
    exists x0; intuition.
    apply H1; intuition eauto.
    exists x0; intuition.
    apply H3; intuition eauto.
  Qed.

End Beth_Semantics.

Lemma deduction_theorem' : forall fs fs' f g,
  provable fs' g -> fs' = Add _ fs f -> provable fs (f '-> g).
  induction 1; intro; subst; [| eauto ..].
  inversion H; try inversion H0; subst; eauto.
  Existential 1 := Bot.
  Existential 1 := Bot.
  Existential 1 := Bot.
Qed.

Lemma deduction_theorem : forall fs f g,
  provable (Add _ fs f) g -> provable fs (f '-> g).
  eauto using deduction_theorem'.
Qed.

Lemma weakening : forall fs f g, provable fs f -> provable (Add _ fs g) f.
  induction 1; solve [repeat constructor; auto | eauto]. 
Qed.

Hint Constructors Union Singleton.
Hint Extern 1 (provable (Add _ _ _) _) => unfold Add.

Lemma converse_deduction_theorem :
  forall fs f g, provable fs (f '-> g) -> provable (Add _ fs f) g.
  intros; apply (@By_MP _ f g); auto using weakening.
Qed.

Module Canonical_Model <: BETH_MODEL.
  Definition consistent fs := ~provable fs Bot.

  Definition W := { T : Ensemble formula | consistent T }.

  Definition R (T U : W) :=
    forall f, provable (proj1_sig T) f -> provable (proj1_sig U) f.
  Hint Unfold R Included.
  Lemma R_refl : forall T, R T T.
    auto.
  Qed.
  Lemma R_trans : forall T U V, R T U -> R U V -> R T V.
    auto.
  Qed.
  Definition V (T : W) (p : var) := provable (proj1_sig T) p.
  Hint Unfold V.
  Lemma monotone : forall x y p, V x p -> R x y -> V y p.
    intuition.
  Qed.
  Lemma atom_covering : forall x p,
    (forall y, R x y -> exists z, R y z /\ V z p) -> V x p.
    intuition.
  Qed.
End Canonical_Model.

Module Canonical_Model_facts.
  Module M := Beth_Semantics Canonical_Model.
  
  Import Canonical_Model M.

  (* Hint Resolve R_refl R_trans monotone deduction_theorem hereditary *)
  Hint Unfold R.

  Ltac destruct_iff :=
    match goal with
      [ H : forall _, _ <-> _ |- _] =>
      pose proof (fun x => proj1 (H x));
        pose proof (fun x => proj2 (H x));
          clear H
    end.

  Lemma equivalence : forall f x, provable (proj1_sig x) f <-> satisfies x f.
    induction f;
      intro x; destruct x as [T ?]_eqn;
        simpl in *; intuition;
          repeat destruct_iff; eauto.

    assert (provable T f1 /\ provable T f2) by firstorder.
    intuition; eauto.

    assert (provable T f1 \/ provable T f2) by auto 6; intuition. 

    assert (provable T f1) by firstorder.
    eauto.

    assert (provable T f2) by firstorder.
    eauto.

    apply deduction_theorem.
    apply prime_lemma.
    auto 8 using weakening.
  Qed.

  Hint Resolve (fun f x => proj1 (equivalence f x)).
  Hint Resolve (fun f x => proj2 (equivalence f x)).

  Theorem completeness : forall fs f,
    (forall T, (forall g, In fs g -> satisfies T g) -> satisfies T f) ->
    provable fs f.
    auto 7 using prime_lemma.
  Qed.
End Canonical_Model_facts.

Print Assumptions Canonical_Model_facts.completeness.
