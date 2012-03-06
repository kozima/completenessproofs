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
Definition Top := Bot '-> Bot.
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
| By_Nbd : forall fs, provable fs (<>Top '\/ []Bot)
| By_MP : forall fs f g,
  provable fs (f '-> g) -> provable fs f -> provable fs g
| By_Nec : forall fs f, provable (Empty_set _) f -> provable fs ([] f).

Hint Constructors provable.

Module Type NBD_MODEL.
  Parameter W : Type.
  Parameter Ri : relation W.
  Parameter N : W -> Ensemble W -> Prop.
  Axiom Ri_refl : reflexive _ Ri.
  Axiom Ri_trans : transitive _ Ri.
  Infix "<=" := Ri.
  Parameter V : W -> var -> Prop.
  Axiom monotone : forall x y p, V x p -> x <= y -> V y p.
  Axiom nbd_constraint1 : forall x x',
    x <= x' -> forall n, N x n -> exists n', N x' n' /\ Included _ n' n.
  Axiom nbd_constraint2 : forall x x',
    x <= x' -> forall n, N x' n -> forall y, In n y ->
      exists n', N x n' /\ In n' y.
End NBD_MODEL.

Module Nbd_Semantics (M : NBD_MODEL).
  Import M.

  Fixpoint satisfies x f :=
    match f with
      | Atom p => V x p
      | Bot => False
      | And f f' => satisfies x f /\ satisfies x f'
      | Or f f' => satisfies x f \/ satisfies x f'
      | Imp f f' => forall y, x <= y -> satisfies y f -> satisfies y f'
      | Box f => forall n, N x n -> forall y, In n y -> satisfies y f
      | Dia f => exists n, N x n /\ forall y, In n y -> satisfies y f
    end.

  Hint Resolve Ri_trans Ri_refl monotone.
  Lemma hereditary : forall f x y, 
    satisfies x f -> x <= y -> satisfies y f.
    induction f; simpl; intuition eauto.
    destruct (nbd_constraint2 H0 H1 y0); intuition; eauto.

    destruct H as [n Hn]; destruct (nbd_constraint1 H0 (proj1 Hn)) as [n0 ?];
      exists n0; intuition.
  Qed.

  Hint Extern 0 =>
    match goal with [ H : In (Empty_set _) _ |- _ ] => inversion H end.

  Axiom nbd_inh_dec : forall x, (forall n, ~N x n) \/ exists n, N x n.

  Theorem soundness : forall fs f, provable fs f ->
    forall x, (forall g, In fs g -> satisfies x g) -> satisfies x f.
    induction 1; simpl in *; intuition; eauto using hereditary.
    destruct (nbd_constraint2 H2 H4 _ H5) as [n' ?];
        eauto; refine (H1 n' _ y1 _ _ _ _); intuition eauto.

    destruct H3 as [n [Hn H']].
    exists n; intuition.
    assert (satisfies y0 ([](f '-> g))) by eauto using hereditary.
    simpl in *; eauto.

    case (nbd_inh_dec x); intro H'; [| destruct H']; intuition; eauto.
  Qed.

End Nbd_Semantics.

Lemma deduction_theorem' : forall fs fs' f g,
  provable fs' g -> fs' = Add _ fs f -> provable fs (f '-> g).
  induction 1; intro; subst; [| eauto ..].
  inversion H; try inversion H0; subst; eauto 4.
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

Module Canonical_Model <: NBD_MODEL.
  Definition prime fs :=
    forall f g, provable fs (f '\/ g) -> provable fs f \/ provable fs g.
  Definition consistent fs := ~provable fs Bot.

  Definition W := { T : Ensemble formula | prime T /\ consistent T }.

  Definition Ri (x y : W) :=
    forall f, provable (proj1_sig x) f -> provable (proj1_sig y) f.

  Definition boxinv fs f := provable fs ([] f).

  Definition nbd (x : W) (f : formula) : Ensemble W := fun y =>
    (forall g, In (boxinv (proj1_sig x)) g -> provable (proj1_sig y) g) /\
    provable (proj1_sig y) f.
  Inductive N' (x : W) : Ensemble W -> Prop :=
  | nbd_intro : forall f, provable (proj1_sig x) (<> f) -> N' x (nbd x f).
  Definition N := N'.

  Hint Constructors N'.
  Hint Unfold N Ri nbd Included.
  Infix "<=" := Ri.
  Lemma Ri_refl : forall x, x <= x.
    auto.
  Qed.
  Lemma Ri_trans : forall x y z, x <= y -> y <= z -> x <= z.
    auto.
  Qed.
  Definition V (x : W) (p : var) := provable (proj1_sig x) p.
  Hint Unfold V.
  Lemma monotone : forall x y p, V x p -> x <= y -> V y p.
    intuition.
  Qed.

  Lemma nbd_constraint1 : forall x x',
    x <= x' -> forall n, N x n -> exists n', N x' n' /\ Included _ n' n.
    intuition.
    inversion H0.
    exists (nbd x' f).
    intuition.
    unfold Included, nbd, In.
    intuition.
    apply H4; auto.
    apply H.
    auto.
  Qed.

  (* Lemma nbd_inh_dec : forall x, (exists n, N x n) \/ (forall n, ~N x n). *)
  (*   (* intro x; destruct x as [? [? ?]]; *) *)
  (*   (*   elimtype (provable x (<>Top) \/ provable x ([]Bot)); *) *)
  (*   (*   [ left | right | eauto]; intuition eauto. *) *)
  (*   (* unfold N; inversion H0. *) *)
  (*   (* simpl in *. *) *)
    
  (*   (* Existential 1 := Bot. *) *)
  (* Admitted. *)

  Lemma boxinv_monotone : forall T U,
    (forall f, provable T f -> provable U f) ->
    (forall f, In (boxinv T) f -> In (boxinv U) f).
    unfold boxinv, In; auto.
  Qed.

  Hint Resolve boxinv_monotone.

  Lemma nbd_constraint2 : forall x x',
    x <= x' -> forall n, N x' n -> forall y, In n y ->
      exists n', N x n' /\ In n' y.
    intuition.
    inversion H0.
    case (nbd_inh_dec x).
    intro n0.
    destruct x as [T [p con]]_eqn.
    elimtype (provable T (<>Top) \/ provable T ([]Bot));
    [ | | ecase p; intuition; eauto]; intuition.
    exists (nbd x Top); intuition.
    unfold N.
    subst; split; auto.
    split; [| apply deduction_theorem; auto].
    intros.
    assert (In (boxinv (proj1_sig x')) g) by (subst; eauto).
    assert (provable (proj1_sig x') ([] g)) by eauto.
    subst n; unfold nbd, In; simpl in H1; intuition.
    unfold In, nbd in H1.
    intuition.

    subst n; unfold In, nbd in H1.
    assert (provable (proj1_sig x') ([] Bot)) by auto.
    assert (provable (proj1_sig y) Bot) by
      eauto using (proj1 H1 Bot).
    destruct y as [? [? ?]]; contradiction.

    destruct x as [T [p con]]_eqn.
    elimtype (provable T (<>Top) \/ provable T ([]Bot));
    [ | | eauto]; intuition.
    exists (nbd x Top).
    intuition.
    unfold N.
    subst; split; auto.
    unfold In, nbd; intuition.
    subst; firstorder.

    apply deduction_theorem; auto.

    destruct y; subst; simpl in *.
    contradiction (proj2 a).
    unfold nbd, In in H1; simpl in H1; destruct H1.
    apply H1.
    apply H; eauto.
  Qed.
End Canonical_Model.

Module Canonical_Model_facts.
  Module M := Nbd_Semantics Canonical_Model.
  
  Import Canonical_Model M.

  Lemma boxinv_closed : forall fs f,
    provable (boxinv fs) f ->  In (boxinv fs) f.
    intros fs f; generalize (refl_equal (boxinv fs));
      generalize (boxinv fs) at -1.
    induction 2; intuition; unfold In; subst; unfold boxinv; eauto 3.
  Qed.

  (* Axiom prime_extension : forall fs f, ~provable fs f -> *)
  (*   exists fs', prime fs' /\ ~provable fs' f /\ *)
  (*     forall h, provable fs h -> provable fs' h. *)
  (* Axiom pr_decidable : forall fs f, provable fs f \/ ~provable fs f. *)

  Ltac assert_pt z x :=
    let H := fresh in
      assert(H : prime x /\ consistent x) by (intuition; eauto);
        set (z := exist _ x H : W).

  Hint Unfold consistent.

  Axiom prime_lemma : forall fs f,
    (forall x : W, (forall g, provable fs g -> provable (proj1_sig x) g) ->
      provable (proj1_sig x) f) ->
    provable fs f.
  (*   intros fs f H; assert (~~provable fs f); *)
  (*     [ | case (pr_decidable fs f)]; intuition. *)
  (*   destruct (prime_extension H0) as [T [? [? ?]]]. *)
  (*   assert_pt y T. *)
  (*   specialize (H y). *)
  (*   auto. *)
  (* Qed. *)

  Ltac destruct_iff :=
    match goal with
      [ H : forall _, _ <-> _ |- _] =>
      pose proof (fun x => proj1 (H x));
        pose proof (fun x => proj2 (H x));
          clear H
    end.

  Hint Extern 1 (provable _ (?x '-> ?x)) => apply deduction_theorem.
  Hint Extern 1 (provable _ Top) => apply deduction_theorem.

  Lemma equivalence : forall f x, provable (proj1_sig x) f <-> satisfies x f.
    induction f;
      intro x; destruct x as [T [p con]]_eqn;
        simpl in *; intuition; repeat destruct_iff.

    apply H2; eauto.

    apply H0; eauto.

    assert (provable T f1 /\ provable T f2) by firstorder.
    intuition; eauto 3.

    assert (provable T f1 \/ provable T f2) by auto; intuition. 

    assert (provable T f1) by firstorder.
    eauto 3.

    assert (provable T f2) by firstorder.
    eauto.

    eauto.

    apply deduction_theorem.
    apply prime_lemma.
    auto 8 using weakening.

    apply H2.
    unfold N in H0; inversion H0.
    subst; unfold In, nbd in H1; simpl in *.
    intuition.

    assert (H' : provable T (<>Top) \/ provable T ([]Bot)) by eauto;
      intuition; [intuition | assert (provable T ([] Bot '-> [] f)); eauto].
    assert (In (boxinv T) f); [| eauto].
    apply boxinv_closed.
    apply prime_lemma.
    intros.
    assert (N x (nbd x Top)) by (subst; auto).
    inversion H4.
    apply H1.
    apply (H (nbd x Top)); subst; auto.
    split; auto.

    exists (nbd x f).
    intuition.
    subst; auto.
    apply H0.
    unfold nbd, In in H2; intuition.

    destruct H as [n [Hn Hs]].
    inversion Hn as [g ?].
    assert (provable (boxinv T) (g '-> f)).
    apply deduction_theorem; apply prime_lemma.
    intuition.
    apply H1; apply Hs; intuition.
    subst; unfold In, nbd; intuition.

    assert (provable T ([] (g '-> f))) by
      (specialize (boxinv_closed H3); eauto).
    simpl in *; eauto 3.
  Qed.

  Hint Resolve (fun f x => proj1 (equivalence f x)).
  Hint Resolve (fun f x => proj2 (equivalence f x)).

  Theorem completeness : forall fs f,
    (forall T, (forall g, In fs g -> satisfies T g) -> satisfies T f) ->
    provable fs f.
    auto 7 using prime_lemma.
  Qed.
End Canonical_Model_facts.
