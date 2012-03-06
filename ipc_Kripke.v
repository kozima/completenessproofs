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
| By_exfalso : forall fs f, provable fs (Bot '-> f)
| By_MP : forall fs f g,
  provable fs (f '-> g) -> provable fs f -> provable fs g.

Hint Constructors provable.

Module Type KRIPKE_MODEL.
  Parameter W : Type.
  Parameter R : relation W.
  Axiom R_refl : reflexive _ R.
  Axiom R_trans : transitive _ R.
  Parameter V : W -> var -> Prop.
  Axiom monotone : forall x y p, V x p -> R x y -> V y p.
End KRIPKE_MODEL.

Module Kripke_Semantics (K : KRIPKE_MODEL).
  Export K.

  Fixpoint satisfies x f :=
    match f with
      | Atom p => V x p
      | Bot => False
      | And f f' => satisfies x f /\ satisfies x f'
      | Or f f' => satisfies x f \/ satisfies x f'
      | Imp f f' => forall y, R x y -> satisfies y f -> satisfies y f'
    end.

  Hint Resolve R_refl R_trans monotone.
  Lemma hereditary : forall x y f, 
    satisfies x f -> R x y -> satisfies y f.
    induction f; simpl; intuition eauto.
  Qed.

  Theorem soundness : forall fs f x,
    provable fs f -> (forall g, In fs g -> satisfies x g) -> satisfies x f.
    induction 1; simpl; intuition; eauto using hereditary.
  Qed.
End Kripke_Semantics.

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

Module Canonical_Model <: KRIPKE_MODEL.
  Definition prime fs :=
    forall f g, provable fs (f '\/ g) -> provable fs f \/ provable fs g.
  Definition consistent fs := ~provable fs Bot.

  Definition W := { T : Ensemble formula | prime T /\ consistent T }.

  Definition R (x y : W) :=
    forall f, provable (proj1_sig x) f -> provable (proj1_sig y) f.
  Hint Unfold R Included.
  Lemma R_refl : forall x, R x x.
    auto.
  Qed.
  Lemma R_trans : forall x y z, R x y -> R y z -> R x z.
    auto.
  Qed.
  Definition V (x : W) (p : var) := provable (proj1_sig x) p.
  Hint Unfold V.
  Lemma monotone : forall x y p, V x p -> R x y -> V y p.
    intuition.
  Qed.
End Canonical_Model.

Module Canonical_Model_facts.
  Module M := Kripke_Semantics Canonical_Model.
  
  Import M.

  Hint Unfold R.

  Axiom prime_lemma : forall fs f,
    (forall x : W, (forall g, provable fs g -> provable (proj1_sig x) g) ->
      provable (proj1_sig x) f) ->
    provable fs f.

  Ltac destruct_iff :=
    match goal with
      [ H : forall _, _ <-> _ |- _] =>
      pose proof (fun x => proj1 (H x));
        pose proof (fun x => proj2 (H x));
          clear H
    end.

  Lemma equivalence : forall f x, provable (proj1_sig x) f <-> satisfies x f.
    induction f;
      intro x; destruct x as [T [? ?]];
        simpl in *; intuition;
          repeat destruct_iff; eauto 3.

    assert (provable T f1 /\ provable T f2) by firstorder.
    intuition; eauto.

    assert (provable T f1 \/ provable T f2) by auto; intuition.

    assert (provable T f1) by firstorder.
    eauto.

    assert (provable T f2) by firstorder.
    eauto.

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
