Require Import Ensembles Relations Classical ipc_Kripke Arith Omega.

Import Canonical_Model.

(* enumeration of formulas *)
Module Type ENUMERATION.
  Parameter t : Type.
  Parameter enc : t -> nat.
  Parameter dec : nat -> t.
  Axiom enc_dec_id : forall x, dec (enc x) = x.
End ENUMERATION.

Module prime_lemma (M : ENUMERATION
  with Definition t := formula).
  Include M.

  Lemma eq_formula_dec : forall f g : formula, {f = g} + {f <> g}.
    intros f g; case (eq_nat_dec (enc f) (enc g));
      [left; rewrite <- (enc_dec_id f), <- (enc_dec_id g); auto
        | intuition congruence].
  Qed.

  Variable fs : Ensemble formula.
  Variable f : formula.
  Hypothesis unprovable : ~provable fs f.

  Fixpoint T n : Ensemble formula :=
    match n with
      | 0 => fs
      | S n' => fun g =>
        (enc g = n' -> ~provable (Add _ (T n') g) f) /\
        (enc g <> n' -> In (T n') g)
    end.
  Definition U : Ensemble formula :=
    fun g => exists n, In (T n) g.

  Lemma T_add_n_only : forall n g, In (T (S n)) g -> enc g = n \/ In (T n) g.
    unfold In; simpl; intros n g; case (eq_nat_dec (enc g) n); intuition.
  Qed.    

  Lemma T_add_lt_n : forall n g, In (T n) g -> enc g < n \/ In fs g.
    induction n; intuition.
    case (T_add_n_only n g H); intuition.
    specialize (IHn g H0); intuition.
  Qed.

  Lemma T_pr_eq : forall n, provable (Add _ (T n) (dec n)) f ->
    Included _ (T (S n)) (T n).
    intros n H g Hg; unfold Included, In in Hg; simpl in Hg; intuition.
    case (eq_nat_dec (enc g) n); intuition.
    subst; rewrite enc_dec_id in *; auto.
  Qed.

  Lemma pr_monotone : forall T U f, Included _ T U -> provable T f -> provable U f.
    induction 2; eauto 4.
  Qed.

  Hint Unfold In Add.
  Hint Extern 0 (Union ?U ?B ?C ?e) => change (In (Union U B C) e).

  Lemma T_pr_sub : forall n, Included _ (T (S n)) (Add formula (T n) (dec n)).
    intros n g Hg; case (T_add_n_only n g Hg); intro; subst; intuition.
    rewrite enc_dec_id; auto.
  Qed.

  Lemma T_not_prove_f : forall n, ~provable (T n) f.
    induction n; intuition eauto using pr_monotone, T_pr_eq, T_pr_sub, unprovable.
  Qed.

  Lemma T_increasing : forall m n, m <= n -> Included _ (T m) (T n).
    induction 1; auto.
    intros g Hg; simpl; unfold In; intuition.
    assert (In (T m0) g) by auto.
    assert (Included _ (Add formula (T m0) g) (T m0)).
    intros g' Hg'.
    inversion Hg'; subst; auto.
    inversion H3; subst; auto.

    assert (provable (T m0) f) by eauto using pr_monotone.
    eapply T_not_prove_f; eauto.

    apply IHle; auto.
  Qed.

  Lemma U_extends_fs : forall g, provable fs g -> provable U g.
    intros g Hp.
    assert (Included _ fs U) by (exists 0; auto).
    induction Hp; intuition eauto.
  Qed.

  Lemma T_monotone : forall m n g, m <= n -> provable (T m) g -> provable (T n) g.
    induction 1; eauto using pr_monotone, T_increasing.
  Qed.

  (* a consequence of compactness *)
  Lemma compact : forall g, provable U g -> exists n, provable (T n) g.
    generalize (refl_equal U); generalize U at -1.
    induction 2; subst; intuition; try solve [exists 0; auto].
    unfold U, In in H0.
    destruct H0; eauto.

    destruct H as [n1 ?]; destruct H0 as [n2 ?]; exists (n1 + n2).
    eapply By_MP; eapply T_monotone; try (apply H || apply H0);
      auto with arith.
  Qed.

  Lemma U_not_prove_f : ~provable U f.
    intro H; case (compact _ H); apply T_not_prove_f; auto.
  Qed.

  Lemma U_includes_T : forall n, Included _ (T n) U.
    unfold U; eauto.
  Qed.

  Lemma T_unpr_in : forall n g, ~provable (Add _ (T n) g) f -> enc g = n ->
    In (T (S n)) g.
    intros; subst; unfold In; simpl; intuition.
  Qed.

    (* Lemma T_unpr_in_U : forall n g, ~provable (Add _ (T n) g) f -> enc g = n -> *)
    (*   In U g. *)
    (*   eexists; eauto using T_unpr_in. *)
    (* Qed. *)

  Lemma add_included_compat : forall S S' x,
    Included formula S S' -> Included formula (Add _ S x) (Add _ S' x).
    intros S S' x Hi x' Hx'; inversion Hx'; subst; auto 6.
  Qed.

  Lemma U_unpr_pr_f : forall g,
    ~provable U g -> provable (Add _ U g) f.
    intros g Hg.
    assert (~provable (T (S (enc g))) g).
    intro.
    apply Hg; eauto using pr_monotone, U_includes_T.
    assert (~~provable (Add _ (T (enc g)) g) f) by auto using T_unpr_in.
    assert (Included _ (Add _ (T (enc g)) g) (Add formula U g)).
    auto using add_included_compat, U_includes_T.
    eapply pr_monotone; try apply H1.
    case (classic (provable (Add formula (T (enc g)) g) f)); intuition.
  Qed.

  Hint Immediate U_unpr_pr_f.

  Lemma U_prime : prime U.
    intros g h H.
    case (classic (provable U g \/ provable U h)); intuition.
    assert (provable (Add _ U g) f) by auto.
    assert (provable (Add _ U h) f) by auto.
    assert (provable U (g '-> f)) by auto using deduction_theorem.
    assert (provable U (h '-> f)) by auto using deduction_theorem.
    assert (provable U (g '\/ h '-> f)) by eauto.
    assert (provable U f) by eauto.
    case U_not_prove_f; auto.
  Qed.

  Lemma U_con : consistent U.
    unfold consistent; eauto using U_not_prove_f.
    Existential 1 := Bot.
  Qed.

  Lemma prime_lemma :
    (forall x : W, (forall g, provable fs g -> provable (proj1_sig x) g) ->
      provable (proj1_sig x) f) ->
    provable fs f.
    case (classic (provable fs f)); intuition.
    specialize (H0 (exist _ U (conj U_prime U_con))).
    elim U_not_prove_f.
    auto using U_extends_fs.
  Qed.
End prime_lemma.
