Set Implicit Arguments.

Require Export
        Morphisms
        Syntax.Regex
        Tactics.Tactics
        Utils.Notations
        Utils.StringUtils.


Lemma eps_cat : #1 @ #1 === #1.
Proof.
  unfolds ; intros s ; splits ; intros Hs ; inverts* Hs.
  -
    inverts* H1 ; crush.
Qed.

Lemma eps_choice_eps : #1 :+: #1 === #1.
Proof.
  unfolds ; intros s ; splits ; intros Hs ; inverts* Hs.
Qed.

Lemma string_app_assoc : forall s1 s2 s3, (s1 ++ s2) ++ s3 = s1 ++ (s2 ++ s3).
Proof.
  induction s1 ; crush.
Qed.

Lemma string_app_length : forall s s', length (s ++ s') = length s + length s'.
Proof.
  induction s ; crush.
Qed.

Lemma string_lt_lemma1 : forall s s' a, string_lt s (String a (s' ++ s)).
Proof.
  intros s s' a. unfolds. induction s as [ | a' s] ; crush.
  apply lt_n_S. rewrite string_app_length. crush.
Qed.

Lemma string_lt_lemma2
  : forall s1 s2 s3 a a', string_lt s1 (String a (s2 ++ String a' (s3 ++ s1))).
Proof.
  intros s1 s2 s3 a a' ; unfolds.
  rewrite string_app_rewind, string_app_length.
  rewrite string_app_rewind, string_app_length.
  crush.
Qed.

Lemma string_lt_lemma3
  : forall s1 s2 s3 a a', string_lt (String a s1)(String a' (s2 ++ String a (s1 ++ s3))).
Proof.
  intros s1 s2 s3 a a' ; unfolds.
  rewrite string_app_rewind, string_app_length.
  rewrite string_app_rewind, string_app_length.
  crush.
Qed.

Lemma string_lt_lemma4
  : forall s1 s2 s3 a a', string_lt (String a s1) (String a (s1 ++ String a' (s2 ++ s3))).
Proof. 
  intros s1 s2 s3 a a' ; unfolds.
  rewrite string_app_rewind, string_app_length.
  rewrite string_app_rewind, string_app_length.
  crush.
Qed.


Hint Resolve
     string_lt_lemma1
     string_lt_lemma2
     string_lt_lemma3
     string_lt_lemma4.


Lemma choice_comm : forall e1 e2, (e1 :+: e2) === (e2 :+: e1).
Proof.
  intros e1 e2 s ; gen e1 e2.
  induction s as [ | a s] ; intros e1 e2 ;
    splits ; intros H ; inverts* H ; eauto.
Qed.

Definition eps_choice_left_star1_type :=
    fun e s => s <<- ((#1 :+: e) ^*) -> s <<- (e ^*).

Lemma eps_choice_left_star1_F
  : forall e s, (forall s', string_lt s' s -> eps_choice_left_star1_type e s') ->
         eps_choice_left_star1_type e s.
Proof.
  intros e s IH ; unfold eps_choice_left_star1_type in * ; intros H.
  destruct s as [ | a s] ; crush.
  -
    inverts* H.
    destruct s0 ; crush.
    inverts* H2. inverts* H4.
Qed.

Lemma eps_choice_left_star1 : forall e s, s <<- ((#1 :+: e) ^*) -> s <<- (e ^*).
Proof.
  intros e.
  eapply (well_founded_ind
           wf_string_lt
           (eps_choice_left_star1_type e)).
  apply eps_choice_left_star1_F.
Qed.

Definition eps_choice_left_star2_type :=
  fun e s => s <<- (e ^*) -> s <<- ((#1 :+: e)^*).

Lemma eps_choice_left_star2_F
  : forall e s, (forall s', string_lt s' s -> eps_choice_left_star2_type e s') ->
         eps_choice_left_star2_type e s.
Proof.
  intros e s IH ; unfold eps_choice_left_star2_type in * ; intros H.
  destruct s as [ | a s] ; crush.
  -
    inverts* H.
    destruct s0 ; crush.
    rewrite string_app_rewind ; eauto.
Qed.

Lemma eps_choice_left_star2 : forall e s, s <<- (e ^*) -> s <<- ((#1 :+: e)^*).
Proof.
  intros e.
  eapply (well_founded_ind
            wf_string_lt
            (eps_choice_left_star2_type e)).
  apply eps_choice_left_star2_F.
Qed.

Lemma eps_choice_left_star : forall e, (#1 :+: e) ^* === e ^*.
Proof.
  intros e s.
  splits.
  apply eps_choice_left_star1.
  apply eps_choice_left_star2.
Qed.

Definition eps_choice_right_star1_type :=
    fun e s => s <<- ((e :+: #1) ^*) -> s <<- (e ^*).

Lemma eps_choice_right_star1_F
  : forall e s, (forall s', string_lt s' s -> eps_choice_right_star1_type e s') ->
         eps_choice_right_star1_type e s.
Proof.
  intros e s IH ; unfold eps_choice_right_star1_type in * ; intros H.
  destruct s as [ | a s] ; crush.
  -
    inverts* H.
    destruct s0 ; crush.
    inverts* H2. inverts* H4.
Qed.

Lemma eps_choice_right_star1 : forall e s, s <<- ((e :+: #1) ^*) -> s <<- (e ^*).
Proof.
  intros e.
  eapply (well_founded_ind
           wf_string_lt
           (eps_choice_right_star1_type e)).
  apply eps_choice_right_star1_F.
Qed.

Definition eps_choice_right_star2_type :=
  fun e s => s <<- (e ^*) -> s <<- ((e :+: #1)^*).

Lemma eps_choice_right_star2_F
  : forall e s, (forall s', string_lt s' s -> eps_choice_right_star2_type e s') ->
         eps_choice_right_star2_type e s.
Proof.
  intros e s IH ; unfold eps_choice_right_star2_type in * ; intros H.
  destruct s as [ | a s] ; crush.
  -
    inverts* H.
    destruct s0 ; crush.
    rewrite string_app_rewind ; eauto.
Qed.

Lemma eps_choice_right_star2 : forall e s, s <<- (e ^*) -> s <<- ((e :+: #1)^*).
Proof.
  intros e.
  eapply (well_founded_ind
            wf_string_lt
            (eps_choice_right_star2_type e)).
  apply eps_choice_right_star2_F.
Qed.

Lemma eps_choice_right_star : forall e, (e :+: #1) ^* === e ^*.
Proof.
  intros e s ; splits.
  apply eps_choice_right_star1.
  apply eps_choice_right_star2.
Qed.

Lemma eps_star : #1 ^* === #1.
Proof.
  unfolds ; intros s ; splits ; intros Hs ; inverts* Hs.
  inverts* H1. crush.
Qed.

Lemma eps_cat_left : forall e, #1 @ e === e.
Proof.
  intros e ; unfolds ; intros s ; splits ; intros H.
  -
    inverts* H.
    inverts* H2.
  - 
    assert (Hs : "" ++ s = s) by auto.
    rewrite <- Hs. eauto.
Qed.

Lemma eps_cat_right : forall e, e @ #1 === e.
Proof.
  intros e ; unfolds ; intros s ; splits ; intros H.
  -
    inverts* H.
    inverts* H4.
    rewrite string_app_nil_end ; auto.
  -
    assert (Hs : s ++ "" = s) by (rewrite string_app_nil_end ; auto).
    rewrite <- Hs ; eauto.
Qed.

Lemma star_singleton : forall e s, s <<- e -> s <<- (e ^*).
Proof.
  intros e s H.
  destruct s ; eauto.
  apply InStarRight with (s := String a s)(s' := "") ; crush.
  rewrite string_app_nil_end. auto.
Qed.

Definition star_cat_type :=
  fun e s => s <<- (e ^*) -> forall s', s' <<- (e ^*) -> (s ++ s') <<- (e ^*).

Lemma star_cat_F
  : forall e s, (forall s', string_lt s' s -> star_cat_type e s') -> star_cat_type e s.
Proof.
  intros e s IH ; unfold star_cat_type in * ; destruct s ; intros H s' H'.
  -
    crush.
  -
    inverts* H. destruct s0. congruence.
    injects* H5.
    rewrite string_app_rewind,  string_app_assoc.
    apply InStarRight with (s := String a0 s0)(s' := s'0 ++ s') ; auto.
Qed.

Lemma star_cat : forall e s, s <<- (e ^*) -> forall s', s' <<- (e ^*) -> (s ++ s') <<- (e ^*).
Proof.
  intros e .
  eapply (well_founded_ind
           wf_string_lt
           (star_cat_type e)).
  apply star_cat_F.
Qed.

Lemma star_inv_1 : forall e s, s <<- (e ^*) -> s <<- ((e ^*) ^*).
Proof.
  intros e s H ; apply star_singleton in H ; auto.
Qed.

Definition star_inv_type := fun e s => s <<- ((e ^*) ^*) -> s <<- (e ^*).

Lemma star_inv_F
  : forall e s, (forall s', string_lt s' s -> star_inv_type e s') -> star_inv_type e s.
  intros e s ; gen e ; destruct s ; intros e IH ;
    unfold star_inv_type in * ; intros H ; eauto.
  -
    inverts* H.
    destruct s0. congruence.
    injects* H5.
    inverts* H2.
    destruct s ; crush.
    assert (Hlt : string_lt s' (String a ((s ++ s'0)  ++ s')))
      by (apply string_lt_lemma1).
    specialize (IH _ Hlt H3).
    rewrite  string_app_assoc, string_app_rewind.
    apply InStarRight with (s := String a s)(s' := s'0 ++ s') ; eauto.  
    apply star_cat ; auto.
Qed.

Lemma star_inv_2 : forall s e, s <<- ((e ^*) ^*) -> s <<- (e ^*).
Proof.
  intros s e ; gen s.
  eapply (well_founded_ind
            wf_string_lt
            (star_inv_type e)).
  eapply star_inv_F.
Qed.

Lemma star_involutive : forall e, ((e ^*) ^*) === (e ^*).
Proof.
  intros e s ; splits.
  apply star_inv_2.
  apply star_inv_1.
Qed.

Definition choice_star_cat_star1_type :=
  fun e1 e2 (H1 : "" <<- e1)(H2 : "" <<- e2) s =>
    s <<- ((e1 @ e2) ^*) -> s <<- ((e1 :+: e2) ^*).

Lemma choice_star_cat_star1_F
  : forall e1 e2 (H1 : "" <<- e1)
            (H2 : "" <<- e2)
            s, (forall s', string_lt s' s -> choice_star_cat_star1_type H1 H2 s') ->
               choice_star_cat_star1_type H1 H2 s.
Proof.
  intros e1 e2 H1 H2 s IH ; unfold choice_star_cat_star1_type in * ; intros H.
  destruct s ; crush.
  -
    inverts* H. inverts* H4.
    destruct s1 ; crush.
    destruct s'0 ; crush.
    +
      rewrite string_app_rewind.
      apply InStarRight with (s := String a0 s'0)(s' := s') ; eauto.
    +
      rewrite string_app_rewind.
      apply InLeft with (e' := e2) in H6.
      apply InRight with (e := e1) in H9.
      assert (Hx : String a0 s1 <<- e1 :+: e2) by auto.
      apply star_singleton in H6.
      apply star_singleton in H9.
      assert (Hs' : s' <<- ((e1 :+: e2) ^*)) by (apply IH ; eauto).
      rewrite string_app_rewind.
      apply star_cat ; eauto.
      apply InStarRight with (s := String a0 s1)(s' := s'0) ; crush.
Qed.

Lemma choice_star_cat_star1
  : forall e1 e2, "" <<- e1 ->
             "" <<- e2 -> forall s, s <<- ((e1 @ e2) ^*) -> s <<- ((e1 :+: e2) ^*).
Proof.
  intros e1 e2 H1 H2.
  eapply (well_founded_ind
            wf_string_lt
            (choice_star_cat_star1_type H1 H2)).
  eapply choice_star_cat_star1_F.
Qed.

Definition choice_star_cat_star2_type :=
  fun e1 e2 (H1 : "" <<- e1)(H2 : "" <<- e2) s =>
    s <<- ((e1 :+: e2) ^*) -> s <<- ((e1 @ e2) ^*).

Lemma choice_star_cat_star2_F
  : forall e1 e2 (H1 : "" <<- e1)
            (H2 : "" <<- e2)
            s, (forall s', string_lt s' s -> choice_star_cat_star2_type H1 H2 s') ->
               choice_star_cat_star2_type H1 H2 s.
Proof.
  intros e1 e2 H1 H2 s IH ; unfold choice_star_cat_star2_type in * ; intros H.
  destruct s ; crush.
  inverts* H. destruct s0 ; crush.
  inverts* H4.
  rewrite string_app_rewind.
  apply InStarRight with (s := String a0 s0)(s' := s') ; eauto.
  apply InCat with (s := String a0 s0)(s' := "") ; crush.
  rewrite string_app_nil_end ; auto.
Qed.


Lemma choice_star_cat_star2
  : forall e1 e2, "" <<- e1 ->
             "" <<- e2 ->
             forall s, s <<- ((e1 :+: e2) ^*) -> s <<- ((e1 @ e2) ^*).
Proof.
  intros e1 e2 H1 H2.
  eapply (well_founded_ind
            wf_string_lt
            (choice_star_cat_star2_type H1 H2)).
  apply choice_star_cat_star2_F.
Qed.

Lemma choice_star_cat_star : forall e1 e2, "" <<- e1 ->
                                      "" <<- e2 ->
                                      ((e1 @ e2) ^*) === ((e1 :+: e2) ^*). 
Proof.
  intros e1 e2 H1 H2 s ; splits.
  apply choice_star_cat_star1 ; eauto.
  apply choice_star_cat_star2 ; eauto.
Qed.


Definition choice_star_star_r1_type :=
  fun e1 e2 (H2 : "" <<- e2) s => s <<- (e1 :+: e2 ^*) -> s <<- ((e1 :+: (e2 ^*)) ^*).

Lemma choice_star_star_r1_F
  : forall e1 e2 (H2 : "" <<- e2) s,
      (forall s', string_lt s' s -> choice_star_star_r1_type e1 H2 s') ->
      choice_star_star_r1_type e1 H2 s.
Proof.
  intros e1 e2 H2 s IH ; unfold choice_star_star_r1_type in * ;
    intros H ; destruct s ; eauto.
  inverts* H. destruct s0 ; crush.
  inverts* H3. rewrite string_app_rewind.
  assert (Hx : s' <<- ((e1 :+: (e2 ^*))^*)) by (apply IH ; auto).
  apply InStarRight with (s := String a0 s0)(s' := s') ; eauto.
  apply InRight ; eauto.
  apply star_singleton ; eauto.
Qed.

Lemma choice_star_star_r1
  : forall e1 e2, "" <<- e2 -> forall s, s <<- (e1 :+: e2 ^*) -> s <<- ((e1 :+: (e2 ^*)) ^*).
Proof.
  intros e1 e2 H2.
  apply (well_founded_ind
           wf_string_lt
           (choice_star_star_r1_type e1 H2)).
  apply choice_star_star_r1_F.
Qed.

Definition choice_star_star_r2_type :=
  fun e1 e2 (H2 : "" <<- e2) s =>  s <<- ((e1 :+: (e2 ^*)) ^*) -> s <<- ((e1 :+: e2) ^*).

Lemma choice_star_star_r2_F
  : forall e1 e2 (H2 : "" <<- e2) s,
      (forall s', string_lt s' s -> choice_star_star_r2_type e1 H2 s') ->
      choice_star_star_r2_type e1 H2 s.
Proof.
  intros e1 e2 H2 s IH ; unfold choice_star_star_r2_type in * ; intros H.
  destruct s ; eauto.
  - 
    inverts* H. destruct s0 ; crush.
    inverts* H3. rewrite string_app_rewind.
    inverts* H4.
    +
      rewrite string_app_nil_end in *.
      inverts* H5. destruct s ; crush.
      rewrite string_app_rewind.
      apply star_cat.
      *
        apply star_singleton ; eauto.
      *
        apply IH ; eauto.
        apply star_singleton ; eauto.
    +
      apply star_singleton in H3.
      apply InRight with (e := e1) in H5.
      apply star_singleton in H5. destruct s ; crush.
      apply IH in H5 ; eauto. apply IH in H3 ; eauto.
      rewrite string_app_rewind.
      apply star_cat ; eauto.
      rewrite string_app_rewind.
      apply IH in H6 ; eauto.
      apply star_cat ; eauto.
Qed.

Lemma choice_star_star_r2 
  : forall e1 e2, "" <<- e2 ->
            forall s, s <<- ((e1 :+: (e2 ^*)) ^*) -> s <<- ((e1 :+: e2) ^*).
Proof.
  intros e1 e2 H2.
  apply (well_founded_ind
           wf_string_lt
           (choice_star_star_r2_type e1 H2)).
  apply choice_star_star_r2_F.
Qed.

Lemma choice_star_star_r
  : forall e1 e2, "" <<- e2 ->
             ((e1 :+: e2) ^*) === ((e1 :+: (e2 ^*))^*).
Proof.
  intros e1 e2 H2 s ; splits.
  apply choice_star_star_r1 ; auto.
  apply choice_star_star_r2 ; auto.
Qed.

Lemma choice_star_star
  : forall e1 e2, "" <<- e1 ->
             "" <<- e2 ->
             ((e1 :+: e2) ^*) === (((e1 ^*) :+: (e2 ^*))^*).
Proof.
  intros e1 e2 H1 H2.
  rewrite <- choice_star_star_r ; eauto.
  rewrite choice_comm with (e1 := (e1 ^*))(e2 := e2).
  rewrite <- choice_star_star_r ; eauto.
  rewrite choice_comm.
  reflexivity.
Qed.

Definition choice_star_cat_star_star1_type :=
  fun e1 e2 s => s <<- (e1 :+: e2 ^*) -> s <<- ((e1 ^*) @ (e2 ^*) ^*).

Lemma choice_star_cat_star_star1_F 
  : forall e1 e2 s, (forall s', string_lt s' s -> choice_star_cat_star_star1_type e1 e2 s') ->
               choice_star_cat_star_star1_type e1 e2 s.
Proof.
  intros e1 e2 s IH ; unfold choice_star_cat_star_star1_type in * ;
    intros H ; inverts* H.
  destruct s0 ; crush.
  apply IH in H3 ; eauto.
  inverts* H2.
  -
    apply star_singleton in H4.
    rewrite string_app_rewind.
    apply star_cat ; auto.
    assert (Hx : String a s0  = String a s0 ++ "")
      by (rewrite string_app_nil_end ; auto).
    rewrite Hx.
    apply star_cat with (s := String a s0)(s' := "") ; eauto.
  - 
    apply star_singleton in H4.
    rewrite string_app_rewind.
    apply star_cat ; auto.
    assert (Hx : String a s0 <<- (e1 ^*) @ (e2 ^*)).
    +
      apply InCat with (s' := String a s0)(s := "") ; auto.
    +
      apply star_singleton ; auto.
Qed.

Lemma choice_star_cat_star_star1 
  : forall e1 e2 s,  s <<- (e1 :+: e2 ^*) -> s <<- ((e1 ^*) @ (e2 ^*) ^*).
Proof.
  intros e1 e2.
  apply (well_founded_ind
           wf_string_lt
           (choice_star_cat_star_star1_type e1 e2)).
  apply choice_star_cat_star_star1_F.
Qed.


Definition star_incl_type :=
  fun e s => s <<- (e ^*) -> forall e', s <<- ((e' :+: e) ^*).

Lemma star_incl_F 
  : forall e s, (forall s', string_lt s' s -> star_incl_type e s') -> star_incl_type e s.
Proof.
  intros e s IH ; unfold star_incl_type in * ; intros H e'.
  inverts* H.
  apply InRight with (e := e') in H2.
  apply star_singleton in H2.
  apply IH with (e' := e') in H3 ; eauto.
  -
    apply star_cat ; eauto.
  -
    destruct s0 ; crush.
Qed.

Lemma star_incl : forall e s, s <<- (e ^*) -> forall e', s <<- ((e' :+: e) ^*).
Proof.
  intros e.
  apply (well_founded_ind
           wf_string_lt
           (star_incl_type e)).
  apply star_incl_F.
Qed.

Definition choice_star_cat_star_star2_type :=
  fun e1 e2 s => s <<- ((e1 ^*) @ (e2 ^*) ^*) -> s <<- (e1 :+: e2 ^*).


Lemma choice_star_cat_star_star2_F 
  : forall e1 e2 s, (forall s', string_lt s' s -> choice_star_cat_star_star2_type e1 e2 s') ->
               choice_star_cat_star_star2_type e1 e2 s.
Proof.
  intros e1 e2 s IH ; unfold choice_star_cat_star_star2_type in * ;
    intros H ; inverts* H.
  destruct s0 ; crush.
  apply IH in H3 ; auto.
  inverts* H2.
  destruct s ; crush.
  -
    apply star_incl with (e' := e1) in H6.
    rewrite string_app_rewind.
    apply star_cat ; eauto.
  - 
    apply star_incl with (e' := e1) in H6.
    apply star_incl with (e' := e2) in H4.
    rewrite choice_comm in H4.
    rewrite string_app_assoc.
    rewrite string_app_rewind.
    apply star_cat ; eauto.
    apply star_cat ; eauto.
Qed.

Lemma choice_star_cat_star_star2
  : forall e1 e2 s, s <<- ((e1 ^*) @ (e2 ^*) ^*) -> s <<- (e1 :+: e2 ^*).
Proof.
  intros e1 e2.
  apply (well_founded_ind
           wf_string_lt
           (choice_star_cat_star_star2_type e1 e2)).
  apply choice_star_cat_star_star2_F.
Qed.


Lemma choice_star_cat_star_star
  : forall e1 e2, ((e1 :+: e2)^*) === (((e1 ^*) @ (e2 ^*))^*).
Proof.
  intros e1 e2 s ; split ;
    [apply choice_star_cat_star_star1 | apply choice_star_cat_star_star2].
Qed.
