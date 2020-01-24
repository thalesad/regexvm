Require Import
        PeanoNat
        Tactics.Tactics.


Section STRONG_INDUCTION.
  Variable P : nat -> Prop.

  Hypothesis IH : forall n, (forall k, k < n -> P k) -> P n.

  Lemma P0 : P 0.
  Proof.
    apply IH ; intros.
    exfalso ; inversion H.
  Qed.

  Hint Resolve P0 : core.

  Lemma pred_increasing : forall n m,
      n <= m ->
      Nat.pred n <= Nat.pred m.
  Proof.
    induction n; cbn; intros.
    apply le_0_n.
    induction H; subst; cbn; eauto.
    destruct m; eauto.
  Qed.

  Hint Resolve le_S_n : core.

  Local Lemma strong_induction_all : forall n,
      (forall m, m <= n -> P m).
  Proof.
    induction n; intros;
      match goal with
      | [ H: _ <= _ |- _ ] =>
        inversion H
      end; eauto.
  Qed.

  Theorem strong_induction : forall n, P n.
  Proof.
    eauto using strong_induction_all.
  Qed.
End STRONG_INDUCTION.

Tactic Notation "strong" "induction" ident(n) := induction n using strong_induction.

