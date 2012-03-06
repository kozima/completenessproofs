Require Import Ensembles Relations.
Set Implicit Arguments.
Implicit Arguments In [U].

Definition var := nat.
Inductive formula : Set :=
| Atom : var -> formula
| Bot : formula
| And : formula -> formula -> formula
| Or : formula -> formula -> formula
| Imp : formula -> formula -> formula
| Box : formula -> formula
| Dia : formula -> formula.
Infix "'->" := Imp (at level 70, right associativity).
Infix "'\/" := Or (at level 60).
Infix "'/\" := And (at level 50).
Notation "[]" := Box.
Notation "<>" := Dia.
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
| By_exfalso : forall fs f, provable fs (Bot '-> f)
| By_KBox : forall fs f g, provable fs ([](f '-> g) '-> []f '-> []g)
| By_KDia : forall fs f g, provable fs ([](f '-> g) '-> <>f '-> <>g)
| By_NDia : forall fs, provable fs (<>Bot '-> Bot)
| By_MP : forall fs f g,
  provable fs (f '-> g) -> provable fs f -> provable fs g
| By_Nec : forall fs f, provable (Empty_set _) f -> provable fs ([] f).

Hint Constructors provable.

Module Type KRIPKE_MODEL.
  Parameter W : Type.
  Parameter R Ri : relation W.
  Axiom Ri_refl : reflexive _ Ri.
  Axiom Ri_trans : transitive _ Ri.
  Infix "<=" := Ri.
  Parameter V : W -> var -> Prop.
  Axiom monotone : forall x y p, V x p -> x <= y -> V y p.
End KRIPKE_MODEL.

Module Kripke_Semantics (K : KRIPKE_MODEL).
  Import K.

  Fixpoint satisfies x f :=
    match f with
      | Atom p => V x p
      | Bot => False
      | And f f' => satisfies x f /\ satisfies x f'
      | Or f f' => satisfies x f \/ satisfies x f'
      | Imp f f' => forall y, x <= y -> satisfies y f -> satisfies y f'
      | Box f => forall y z, x <= y -> R y z -> satisfies z f
      | Dia f => forall y, x <= y -> exists z, R y z /\ satisfies z f
    end.

  Hint Resolve Ri_trans Ri_refl monotone.
  Lemma hereditary : forall f x y, 
    satisfies x f -> x <= y -> satisfies y f.
    induction f; simpl; intuition eauto.
  Qed.

  Hint Extern 0 =>
    match goal with [ H : In (Empty_set _) _ |- _ ] => inversion H end.
  Theorem soundness : forall fs f, provable fs f ->
    forall x, (forall g, In fs g -> satisfies x g) -> satisfies x f.
    induction 1; simpl in *; intuition; eauto using hereditary.
    destruct (H3 y1); intuition eauto.

    destruct (H1 y); intuition.
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

  Definition W := { P : Ensemble formula * formula |
    prime (fst P) /\ consistent (fst P) /\ ~provable (fst P) (<> (snd P)) }.

  Definition Ri (T U : W) :=
    forall f, provable (fst (proj1_sig T)) f -> provable (fst (proj1_sig U)) f.
  Definition R (T U : W) :=
    (forall f, provable (fst (proj1_sig T)) ([]f) ->
      provable (fst (proj1_sig U)) f) /\
    ~provable (fst (proj1_sig U)) (snd (proj1_sig T)).

  Hint Unfold R Ri Included.
  Infix "<=" := Ri.
  Lemma Ri_refl : forall T, T <= T.
    auto.
  Qed.
  Lemma Ri_trans : forall T U V, T <= U -> U <= V -> T <= V.
    auto.
  Qed.
  Definition V (T : W) (p : var) := provable (fst (proj1_sig T)) p.
  Hint Unfold V.
  Lemma monotone : forall x y p, V x p -> x <= y -> V y p.
    intuition.
  Qed.
End Canonical_Model.

Module Canonical_Model_facts.
  Module M := Kripke_Semantics Canonical_Model.
  
  Import Canonical_Model M.

  Definition boxinv fs f := provable fs ([] f).

  Lemma boxinv_closed : forall fs f,
    provable (boxinv fs) f ->  In (boxinv fs) f.
    intros fs f; generalize (refl_equal (boxinv fs));
      generalize (boxinv fs) at -1.
    induction 2; intuition; unfold In; subst; unfold boxinv; eauto 3.
  Qed.

  Axiom prime_extension : forall fs f, ~provable fs f ->
    exists fs', prime fs' /\ ~provable fs' f /\
      forall h, provable fs h -> provable fs' h.
  Axiom pr_decidable : forall fs f, provable fs f \/ ~provable fs f.

  Ltac assert_pt z x f :=
    let H := fresh in
      assert(H : prime x /\ consistent x /\ ~provable x (<> f))
        by (intuition; eauto);
        set (z := exist _ (x, f) H : W).

  Hint Unfold consistent.

  Lemma prime_lemma : forall fs f,
    (forall x : W, (forall g, provable fs g -> provable (fst (proj1_sig x)) g) ->
      provable (fst (proj1_sig x)) f) ->
    provable fs f.
    intros fs f H; assert (~~provable fs f);
      [ | case (pr_decidable fs f)]; intuition.
    destruct (prime_extension H0) as [T [? [? ?]]].
    assert_pt y T Bot.
    specialize (H y).
    auto.
    Existential 1 := Bot.
  Qed.

  Ltac destruct_iff :=
    match goal with
      [ H : forall _, _ <-> _ |- _] =>
      pose proof (fun x => proj1 (H x));
        pose proof (fun x => proj2 (H x));
          clear H
    end.

  Lemma equivalence : forall f x, provable (fst (proj1_sig x)) f <-> satisfies x f.
    induction f;
      intro x; destruct x as [T [p [con mcon]]];
        simpl in *; intuition; repeat destruct_iff.

    apply H2; eauto.

    apply H0; eauto.

    assert (provable (fst T) f1 /\ provable (fst T) f2) by firstorder.
    intuition; eauto 3.

    assert (provable (fst T) f1 \/ provable (fst T) f2) by auto; intuition. 

    assert (provable (fst T) f1) by firstorder.
    eauto 3.

    assert (provable (fst T) f2) by firstorder.
    eauto.

    eauto.

    apply deduction_theorem.
    apply prime_lemma.
    auto 8 using weakening.

    destruct H1.
    eauto.

    assert (In (boxinv (fst T)) f); [| eauto].
    apply boxinv_closed.
    apply prime_lemma.
    intros.
    assert_pt x' (fst T) Bot.
    specialize (H x').
    apply H1; apply H; intuition.

    unfold R.
    intuition.

    destruct x; simpl in *; intuition.

    destruct y as [[T' g] [? [? mcon']]]; simpl in *.
    destruct (@prime_extension (Add _ (boxinv T') f) g); intuition.
    apply mcon'.
    assert (provable (boxinv T') (f '-> g))
      by auto using deduction_theorem.
    assert (provable T' ([] (f '-> g))) by
      (specialize (boxinv_closed H4); auto).
    eauto 4.

    assert_pt x1 x0 Bot.
    exists x1; intuition.
    unfold R; intuition.
    apply H1; auto.

    destruct T as [x' ?]; simpl in *.
    assert (~~provable x' (<> f)); intuition.
    assert_pt z x' f.
    destruct (H z).
    auto.

    intuition.
    destruct H5.
    subst; simpl in *; auto.

    case (pr_decidable x' (<> f)); intuition.

    Existential 1 := Bot.
    Existential 1 := Bot.
  Qed.

  Hint Resolve (fun f x => proj1 (equivalence f x)).
  Hint Resolve (fun f x => proj2 (equivalence f x)).

  Theorem completeness : forall fs f,
    (forall T, (forall g, In fs g -> satisfies T g) -> satisfies T f) ->
    provable fs f.
    auto 7 using prime_lemma.
  Qed.
End Canonical_Model_facts.
