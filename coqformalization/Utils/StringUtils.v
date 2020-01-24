Set Implicit Arguments.

Require Export
        Arith_base
        Ascii
        String
        Tactics.Tactics
        Wellfounded.

Open Scope string_scope.

Lemma empty_string_concat : forall s s', "" = s ++ s' -> s = "" /\ s' = "".
Proof.
  induction s ; destruct s' ; intros ; crush.
Qed.

Lemma string_app_nil_end : forall s, s ++ "" = s.
Proof.
  induction s ; crush.
Qed.

Lemma string_app_rewind : forall s s' a, String a (s ++ s') = (String a s) ++ s'.
Proof.
  crush.
Qed.

Lemma string_app_length : forall s s', length (s ++ s') = length s + length s'.
Proof.
  induction s ; crush.
Qed.


Lemma string_app_conv
  : forall xs ys zs ts, xs ++ ys = zs ++ ts -> exists us, (xs = zs ++ us /\ ts = us ++ ys) \/
                                             (zs = xs ++ us /\ ys = us ++ ts).
Proof.
  induction xs ; destruct zs ; intros ; simpl in * ; substs*.
  +
    injects H.
    lets J : IHxs H0 ; crush.
    eexists ; eauto.
    eexists ; eauto.
Qed.


Lemma string_app_assoc : forall s1 s2 s3, s1 ++ s2 ++ s3 = (s1 ++ s2) ++ s3.
Proof.
  induction s1 ; crush.
Qed.

(** well founded ordering on strings: length based *)

Definition string_lt (s s' : string) : Prop :=
  length s < length s'.

Definition wf_string_lt : well_founded string_lt :=
  @wf_inverse_image string
                    nat
                    lt
                    length
                    lt_wf.

Lemma string_sing_l : forall s1 s2 a, s1 ++ String a "" = s2 ++ String a "" -> s1 = s2.
Proof.
  induction s1 ; intros s2 a' H ; destruct s2 ; simpl in * ; auto.
  inverts H.
  apply empty_string_concat in H2 ; crush.
  inverts* H. symmetry in H2.
  apply empty_string_concat in H2 ; crush.
  inverts* H.
  fequals*.
Qed.

Lemma string_app_congl : forall s1 s2 s3, s1 ++ s3 = s2 ++ s3 -> s1 = s2.
Proof.
  intros s1 s2 s3 ; gen s1 s2 ; induction s3 ; crush.
  -
    now rewrite! string_app_nil_end in H.
  -
    assert (Hx : String a s3 = String a "" ++ s3) by crush.
    rewrite! Hx in H.
    rewrite! string_app_assoc in H.
    assert (He : s1 ++ String a "" = s2 ++ String a "") by crush.
    apply string_sing_l in He ; auto.
Qed.
