Set Implicit Arguments.

Require Import
        List
        String
        Ascii
        Omega
        Syntax.Regex
        Syntax.BitCodes
        Syntax.Input
        Syntax.Problematic
        Utils.StrongNatInduction.


Import ListNotations.

Open Scope string_scope.

(** greedy relation for bit code trees *)

Inductive output : Set := 
| Ok    : string -> string -> code -> output
| Error : output.

Inductive greedy : regex -> string -> nat -> output -> Prop :=
| G_Empty
  : forall s, greedy #0 s 0 Error
| G_Eps
  : forall s, greedy #1 s 1 (Ok "" s [])
| G_ChrOk 
  : forall a s, greedy ($ a) (String a s) 2 (Ok (String a "") s [])
| G_ChrErr1
  : forall a b s, a <> b -> greedy ($ a) (String b s) 2 Error
| G_ChrErr2
  : forall a, greedy ($ a) "" 2 Error
| G_CatOk
  : forall e1 e2 s s1 r1 s2 r2 bs1 bs2 n m,
    s = s1 ++ r1 ->
    r1 = s2 ++ r2 ->
    greedy e1 s n (Ok s1 r1 bs1) ->
    greedy e2 r1 m (Ok s2 r2 bs2) ->
    greedy (e1 @ e2) s (1 + n + m) (Ok (s1 ++ s2) r2 (bs1 ++ bs2)%list)
| G_CatErr1
  : forall e1 e2 s n,
    greedy e1 s n Error ->
    greedy (e1 @ e2) s (1 + n) Error
| G_CatErr2
  : forall e1 e2 s s1 r1 bs1 n m,
    s = s1 ++ r1 ->
    greedy e1 s n (Ok s1 r1 bs1) ->
    greedy e2 r1 m Error ->
    greedy (e1 @ e2) s (1 + n + m) Error
| G_Choice_Ok1 
  : forall e1 e2 s s1 r1 bs1 n,
    s = s1 ++ r1 ->
    greedy e1 s n (Ok s1 r1 bs1) ->
    greedy (e1 :+: e2) s (1 + n) (Ok s1 r1 (O :: bs1))
| G_Choice_Ok2
  : forall e1 e2 s s2 r2 bs2 n m,
    s = s2 ++ r2 ->
    greedy e1 s n Error ->
    greedy e2 s m (Ok s2 r2 bs2) -> 
    greedy (e1 :+: e2) s (1 + n + m) (Ok s2 r2 (I :: bs2))
| G_Choice_Err
  : forall e1 e2 s n m,
    greedy e1 s n Error ->
    greedy e2 s m Error ->
    greedy (e1 :+: e2) s (1 + n + m) Error
| G_Star_Rec
  : forall e1 s s1 r1 bs1 s2 r2 bs2 n m,
    s = s1 ++ r1 ->
    greedy e1 s n (Ok s1 r1 bs1) ->
    r1 = s2 ++ r2 -> 
    greedy (Star e1) r1 m (Ok s2 r2 bs2) ->
    greedy (Star e1) s (1 + n + m) (Ok (s1 ++ s2) r2 (O :: bs1 ++ bs2))
| G_Star_Base
  : forall e1 s n,
    greedy e1 s n Error ->
    greedy (Star e1) s (1 + n) (Ok "" s (I :: [])).

Hint Constructors greedy : core.

Definition greedy_sound_type e s :=
  fun n s1 r1 bs => unproblematic e -> greedy e s n (Ok s1 r1 bs) -> s1 <<- e.

Lemma greedy_sound_F
  : forall p,
    (forall p', input_lt p' p -> forall n s1 r1 bs1,
          greedy_sound_type (get_regex p') (get_string p') n s1 r1 bs1) ->
     forall n s1 r1 bs1, greedy_sound_type (get_regex p) (get_string p) n s1 r1 bs1.
Proof.
  intros [e s] IH n s1 r1 bs1 ; unfold greedy_sound_type in * ; simpl in * ;
    intros Hu Hg.
  destruct e ; inverts* Hg ; simpl ; eauto.
  -
    inverts* Hu.
    assert (HLt1 : input_lt (mk_input e1 (s2 ++ s3 ++ r1))
                            (mk_input (e1 @ e2) (s2 ++ s3 ++ r1))) by 
        (apply left_lex ; unfolds ; crush).
    assert (HLt2 : input_lt (mk_input e2 (s3 ++ r1))
                            (mk_input (e1 @ e2) (s2 ++ s3 ++ r1))) by 
        (apply left_lex ; unfolds ; crush).
    lets H11 : IH HLt1 H1 H8 ; simpl in *.
    lets H22 : IH HLt2 H2 H9 ; crush.
  -
    inverts* Hu.
    assert (HLt1 : input_lt (mk_input e1 (s1 ++ r1))
                            (mk_input (e1 :+: e2) (s1 ++ r1))) by 
        (apply left_lex ; unfolds ; crush).
    lets H : IH HLt1 H1 H7 ; crush.
  -
    inverts* Hu.
    assert (HLt2 : input_lt (mk_input e2 (s1 ++ r1))
                            (mk_input (e1 :+: e2) (s1 ++ r1))) by 
        (apply left_lex ; unfolds ; crush).
    lets H : IH HLt2 H2 H8 ; crush.
  -
    inverts* Hu.
    assert (HLte : input_lt (mk_input e (s2 ++ s3 ++ r1))
                            (mk_input (Star e) (s2 ++ s3 ++ r1))).
    apply left_lex ; unfolds ; crush.
    lets IHe : IH HLte H1 H6 ; crush.
    destruct s2 eqn : Hs2 ; crush.
    assert (HLts : input_lt (mk_input (e ^*) (s3 ++ r1))
                            (mk_input (e ^*) (String a (s ++ s3 ++ r1)))).
    apply right_lex ; unfolds ; simpl ; rewrite! string_app_length ; crush.
    assert (Hu : unproblematic (Star e)) by eauto.
    lets IHes : IH HLts Hu H8 ; simpl in * ; rewrite string_app_rewind.
    eapply InStarRight ; eauto ; crush.
Qed.

Theorem greedy_sound
  : forall e s n s1 r1 bs1,
            s = s1 ++ r1 ->
            unproblematic e -> 
            greedy e s n (Ok s1 r1 bs1) ->
            s1 <<- e.
Proof.
  intros e s n s1 r1 bs1 Hu Heq.
  change s with (get_string (mk_input e s)).
  change e with (get_regex (mk_input e s)) in *.
  apply (well_founded_ind
           wf_input_lt
           (fun p => forall n s1 r1 bs1,
                greedy_sound_type (get_regex p) (get_string p) n s1 r1 bs1)
        ) ; eauto.
  apply greedy_sound_F.
Qed.

Hint Resolve greedy_sound : core.

Definition greedy_typed_type e s :=
  fun n s1 r1 bs => s = s1 ++ r1 -> unproblematic e -> greedy e s n (Ok s1 r1 bs) -> bs :# e.

Lemma greedy_typed_F
  : forall p, (forall p', input_lt p' p ->
          forall n s1 r1 bs, greedy_typed_type (get_regex p') (get_string p') n s1 r1 bs) ->
         forall n s1 r1 bs, greedy_typed_type (get_regex p) (get_string p) n s1 r1 bs.
Proof.
  intros [e s] IH n s1 r1 bs Heq Hu Hg ; simpl in *.
  destruct e ; inverts* Hg.
  -
    inverts* Hu.
    assert (HLt1 : input_lt (mk_input e1 ((s2 ++ s3) ++ r1))
                            (mk_input (e1 @ e2) ((s2 ++ s3) ++ r1))).
    apply left_lex. unfolds. crush.
    lets IH1 : IH HLt1 H8 ; crush.
    assert (HLt2 : input_lt (mk_input e2 (s3 ++ r1))
                            (mk_input (e1 @ e2) ((s2 ++ s3) ++ r1))).
    apply left_lex. unfolds. crush.
    lets IH2 : IH HLt2 H9 ; crush.
  -
    inverts* Hu.
    assert (HLt1 : input_lt (mk_input e1 (s1 ++ r1))
                            (mk_input (e1 :+: e2) (s1 ++ r1))).
    apply left_lex. unfolds. crush.
    lets* IH1 : IH HLt1 H7 ; crush.
  -
    inverts* Hu.
    assert (HLt1 : input_lt (mk_input e2 (s1 ++ r1))
                            (mk_input (e1 :+: e2) (s1 ++ r1))).
    apply left_lex. unfolds. crush.
    lets IH2 : IH HLt1 H8 ; crush.
  -
    inverts* Hu.
    assert (HLte : input_lt (mk_input e ((s2 ++ s3) ++ r1))
                            (mk_input (Star e) ((s2 ++ s3) ++ r1))).
    apply left_lex. unfolds. crush.
    lets IHe : IH HLte H6 ; crush.
    lets Se : greedy_sound H2 H6 ; try rewrite string_app_assoc ; auto.
    destruct s2 eqn : Hs2 ; crush.
    assert (HLtes : input_lt (mk_input (Star e) (s3 ++ r1))
                             (mk_input (Star e) (String a ((s ++ s3) ++ r1)))).
    apply right_lex ; unfolds ; repeat (rewrite! string_app_length ; simpl) ; crush.
    assert (Hu : unproblematic (Star e)) by eauto.
    lets IHs : IH HLtes Hu H8 ; crush.
Qed.

Theorem greedy_typed
  : forall e s n s1 r1 bs,
    unproblematic e -> 
    s = s1 ++ r1 ->
    greedy e s n (Ok s1 r1 bs)  -> bs :# e.
Proof.
  intros e s n s1 r1 bs1 Hu Heq.
  change s with (get_string (mk_input e s)).
  change e with (get_regex (mk_input e s)) in *.
  apply (well_founded_ind
           wf_input_lt
           (fun p => forall n s1 r1 bs1,
                greedy_typed_type (get_regex p) (get_string p) n s1 r1 bs1)
        ) ; eauto.
  apply greedy_typed_F.  
Qed.

Theorem greedy_deterministic
  : forall n e s o1, greedy e s n o1 -> forall m o2, greedy e s m o2 -> n = m /\ o1 = o2.
Proof.
  strong induction n ; intros e s o1 Hg1 m o2 Hg2 ;
    splits ; inverts Hg1 ; inverts* Hg2 ; crush.
  -
    assert (Hk : n0 < S (n0 + m0)) by crush.
    lets IH1 : H Hk H2 H6 ; crush.
    assert (Hk1 : m0 < S (n + m0)) by crush.
    injects* H1. rewrite H0 in *.
    lets IH2 : H Hk1 H3 H10 ; crush.
  -
    assert (Hk : n0 < S (n0 + m0)) by crush.
    lets IH1 : H Hk H2 H7 ; crush.
  -
    assert (Hk : n0 < S (n0 + m0)) by crush.
    lets IH1 : H Hk H2 H5 ; crush.
    injects* H1.
    assert (Hk1 : m0 < S (n + m0)) by crush.
    lets IH2 : H Hk1 H3 H9 ; crush.
  -
    assert (Hk : n0 < S n0) by crush.
    lets IH1 : H Hk H0 H5 ; crush.
  -
    assert (Hk : n0 < S n0) by crush.
    lets IH1 : H Hk H0 H6 ; crush.
  -
    assert (Hk : n0 < S n0) by crush.
    lets IH1 : H Hk H0 H4 ; crush.
  -
    assert (Hk : n0 < S (n0 + m0)) by crush.
    lets IH1 : H Hk H1 H6 ; crush.
    injects* H3.
    assert (Hk1 : m0 < S (n + m0)) by crush.
    lets IH2 : H Hk1 H2 H10 ; crush.
  -
    assert (Hk : n0 < S (n0 + m0)) by crush.
    lets IH1 : H Hk H1 H7 ; crush.
  -
    assert (Hk : n0 < S (n0 + m0)) by crush.
    lets IH1 : H Hk H1 H5 ; crush.
    injects* H3.
    assert (Hk1 : m0 < S (n + m0)) by crush.
    lets IH2 : H Hk1 H2 H9 ; crush.
  -
    assert (Hk : n0 < S n0) by crush.
    lets IH1 : H Hk H1 H7 ; crush.
  -
    assert (Hk : n0 < S n0) by crush.
    lets IH1 : H Hk H1 H4 ; crush.
  -
    assert (Hk : n0 < S n0) by crush.
    lets IH1 : H Hk H1 H3 ; crush.
  -
    assert (Hk : n0 < S (n0 + m0)) by crush.
    lets IH1 : H Hk H1 H8 ; crush.
  -
    assert (Hk : n0 < S (n0 + m0)) by crush.
    lets IH1 : H Hk H1 H5 ; crush.
    assert (Hk1 : m0 < S (n + m0)) by crush.
    lets IH2 : H Hk1 H2 H9 ; crush.
  -
    assert (Hk : n0 < S (n0 + m0)) by crush.
    lets IH1 : H Hk H1 H4 ; crush.
    assert (Hk1 : m0 < S (n + m0)) by crush.
    lets IH2 : H Hk1 H2 H8 ; crush.
  -
    assert (Hk : n0 < S (n0 + m0)) by crush.
    lets IH1 : H Hk H0 H8 ; crush.
  -
    assert (Hk : n0 < S (n0 + m0)) by crush.
    lets IH1 : H Hk H0 H5 ; crush.
    assert (Hk1 : m0 < S (n + m0)) by crush.
    lets IH2 : H Hk1 H1 H9 ; crush.
  -
    assert (Hk : n0 < S (n0 + m0)) by crush.
    lets IH1 : H Hk H0 H4 ; crush.
    assert (Hk1 : m0 < S (n + m0)) by crush.
    lets IH2 : H Hk1 H1 H8 ; crush.
  -
    assert (Hk : n0 < S (n0 + m0)) by crush.
    lets IH1 : H Hk H1 H4 ; crush.
    injects* H5.
    assert (Hk1 : m0 < S (n + m0)) by crush.
    rewrite H0 in *.
    lets IH2 : H Hk1 H3 H6 ; crush.
  -
    assert (Hk : n0 < S (n0 + m0)) by crush.
    lets IH1 : H Hk H1 H2 ; crush.
  -
    assert (Hk : n0 < S n0) by crush.
    lets IH1 : H Hk H0 H3 ; crush.
  -
    assert (Hk : n0 < S n0) by crush.
    lets IH1 : H Hk H0 H2 ; crush.
  -
    assert (Hk : n0 < S (n0 + m0) /\ m0 < S (n0 + m0)) by crush.
    destruct Hk as [Hk1 Hk2].
    lets IH1 : H Hk1 H2 H6 ; crush.
    injects* H1.
    rewrite H0 in *.
    lets IH2 : H Hk2 H3 H10 ; crush.
  -
    assert (Hk : n0 < S (n0 + m0) /\ m0 < S (n0 + m0)) by crush.
    destruct Hk as [Hk1 Hk2].
    lets IH1 : H Hk1 H2 H7 ; crush.
  -
    assert (Hk : n0 < S (n0 + m0) /\ m0 < S (n0 + m0)) by crush.
    destruct Hk as [Hk1 Hk2].
    lets IH1 : H Hk1 H2 H5 ; crush.
    injects* H1.
    lets IH2 : H Hk2 H3 H9 ; crush.
  -
    assert (Hk : n0 < S n0) by crush.
    lets IH1 : H Hk H0 H5 ; crush.
  -
    assert (Hk : n0 < S (n0 + m0) /\ m0 < S (n0 + m0)) by crush.
    destruct Hk as [Hk1 Hk2].
    lets IH1 : H Hk1 H1 H6 ; crush.
    injects* H3.
    lets IH2 : H Hk2 H2 H10 ; crush.
  -
    assert (Hk : n0 < S n0) by crush.
    lets IH1 : H Hk H1 H7 ; crush.
  -
    assert (Hk : n0 < S n0) by crush.
    lets IH1 : H Hk H1 H4 ; crush.
  -
   assert (Hk : n0 < S n0) by crush.
   lets IH1 : H Hk H1 H3 ; crush.
  -
    assert (Hk : n0 < S (n0 + m0) /\ m0 < S (n0 + m0)) by crush.
    destruct Hk as [Hk1 Hk2].
    lets IH1 : H Hk1 H1 H8 ; crush.
  -
    assert (Hk : n0 < S (n0 + m0) /\ m0 < S (n0 + m0)) by crush.
    destruct Hk as [Hk1 Hk2].
    lets IH1 : H Hk1 H1 H5 ; crush.
    lets IH2 : H Hk2 H2 H9 ; crush.
  -
    assert (Hk : n0 < S (n0 + m0) /\ m0 < S (n0 + m0)) by crush.
    destruct Hk as [Hk1 Hk2].
    lets IH1 : H Hk1 H1 H4 ; crush.
    lets IH2 : H Hk2 H2 H8 ; crush.
  -
    assert (Hk : n0 < S (n0 + m0) /\ m0 < S (n0 + m0)) by crush.
    destruct Hk as [Hk1 Hk2].
    lets IH1 : H Hk1 H0 H8 ; crush.
  -
    assert (Hk : n0 < S (n0 + m0) /\ m0 < S (n0 + m0)) by crush.
    destruct Hk as [Hk1 Hk2].
    lets IH1 : H Hk1 H0 H5 ; crush.
    lets IH2 : H Hk2 H1 H9 ; crush.
  -
    assert (Hk : n0 < S (n0 + m0) /\ m0 < S (n0 + m0)) by crush.
    destruct Hk as [Hk1 Hk2].
    lets IH1 : H Hk1 H1 H4 ; crush.
    injects* H5.
    rewrite H0 in *.
    lets IH2 : H Hk2 H3 H6 ; crush.
  -
    assert (Hk : n0 < S (n0 + m0) /\ m0 < S (n0 + m0)) by crush.
    destruct Hk as [Hk1 Hk2].
    lets IH1 : H Hk1 H1 H2 ; crush.
  -
    assert (Hk : n0 < S n0) by crush.
    lets IH1 : H Hk H0 H3 ; crush.
Qed.

Theorem greedy_prefix
  : forall e s n s1 r1 bs1, greedy e s n (Ok s1 r1 bs1) -> s = s1 ++ r1.
Proof.
  intros e s n s1 r1 bs1 H ; inverts* H ; rewrite string_app_assoc ; auto.
Qed.

Definition greedy_interp_type e s :=
  unproblematic e -> {r | greedy e s (fst r) (snd r)}.

Definition greedy_interp_F 
  : forall p, (forall p', input_lt p' p -> greedy_interp_type (get_regex p') (get_string p')) ->
         greedy_interp_type (get_regex p) (get_string p).
  intros [e s] IH Hu ; simpl in *.
  destruct e.
  -
    exists (0 , Error) ; eauto.
  -
    exists (1, Ok "" s []) ; simpl ; eauto.
  -
    destruct s as [ | a' s'] ; simpl ; eauto.
    +
      exists (2 , Error) ; simpl ; eauto.
    +
      destruct (ascii_dec a a') ; crush ; eauto.
      *
        exists (2 , Ok (String a' "") s' []) ; simpl ; eauto.
      *
        exists (2 , Error) ; simpl ; eauto.
  -
    assert (HLt1 : input_lt (mk_input e1 s)
                            (mk_input (e1 @ e2) s)).
    apply left_lex ; unfolds ; crush.
    assert (Hu1 : unproblematic e1) by inverts* Hu.
    assert (Hu2 : unproblematic e2) by inverts* Hu.
    lets IH1 : IH HLt1 Hu1. simpl in *.
    destruct IH1 as [[n1 o1] IH1]. simpl in *.
    destruct o1 as [c1 r1 bs1 | ].
    +
      assert (HLt2 : input_lt (mk_input e2 r1)
                              (mk_input (e1 @ e2) s)).
      apply left_lex ; unfolds ; crush.
      lets IH2 : IH HLt2 Hu2. simpl in *.
      destruct IH2 as [[n2 o2] IH2]. simpl in *.
      destruct o2 as [c2 r2 bs2 | ].
      *
        lets IG1 : greedy_prefix IH1.
        exists (1 + n1 + n2, Ok (c1 ++ c2) r2 (bs1 ++ bs2)%list) ; simpl.
        eapply G_CatOk ; eauto.
        eapply greedy_prefix ; eauto.
      *
        exists (1 + n1 + n2, Error) ; simpl.
        eapply G_CatErr2 ; eauto.
        eapply greedy_prefix ; eauto.
    +
      exists (1 + n1, Error) ; simpl ; eapply G_CatErr1 ; eauto.
  -
    assert (HLt1 : input_lt (mk_input e1 s)
                            (mk_input (e1 :+: e2) s)).
    apply left_lex ; unfolds ; crush.
    assert (Hu1 : unproblematic e1) by inverts* Hu.
    lets IH1 : IH HLt1 Hu1.
    destruct IH1 as [[n1 o1] IH1].
    destruct o1 as [c1 r1 bs1 | ] ; simpl in *.
    +
      exists (1 + n1, Ok c1 r1 (O :: bs1)) ; simpl.
      apply G_Choice_Ok1 ; eauto.
      eapply greedy_prefix ; eauto.
    +
      assert (HLt2 : input_lt (mk_input e2 s)
                              (mk_input (e1 :+: e2) s)).
      apply left_lex ; unfolds ; crush.
      assert (Hu2 : unproblematic e2) by inverts* Hu.
      lets IH2 : IH HLt2 Hu2.
      destruct IH2 as [[n2 o2] IH2].
      destruct o2 as [c2 r2 bs2 | ] ; simpl in *.
      *
        exists (1 + n1 + n2, Ok c2 r2 (I :: bs2)) ; simpl.
        apply G_Choice_Ok2 ; eauto.
        eapply greedy_prefix ; eauto.
      *
        exists (1 + n1 + n2, Error) ; simpl.
        apply G_Choice_Err ; eauto.
  -
    assert (HLte : input_lt (mk_input e s)
                            (mk_input (Star e) s)).
    apply left_lex ; unfolds ; crush.
    assert (Hue : unproblematic e) by inverts* Hu.
    lets IHe : IH HLte Hue ; simpl in *.
    destruct IHe as [[ne oe] IHe]. simpl in *.
    destruct oe as [ce re bse | ].
    +
      assert (Hs : s = ce ++ re) by (eapply greedy_prefix ; eauto).
      assert (He : ce <<- e) by (eapply greedy_sound ; eauto).
      destruct ce as [ | a' s'].
      *
        assert (False).
        inverts* Hu. elim H.
      *
        assert (HLtes : input_lt (mk_input (Star e) re)
                                 (mk_input (Star e) ((String a' s') ++ re))).
        apply right_lex. unfolds. simpl. rewrite! string_app_length ; crush.
        rewrite Hs in *. lets IHes : IH HLtes Hu.
        destruct IHes as [[nes oes] IHes]. simpl in *.
        destruct oes as [ces res bses | ].
        **
          exists (1 + ne + nes, Ok (String a' s' ++ ces) res (O :: bse ++ bses)%list) ;
            simpl.
          rewrite! string_app_rewind.
          eapply G_Star_Rec ; eauto.
          eapply greedy_prefix ; eauto.
        **
          assert(Hc : False).
          inverts* IHes.
          elim Hc.
    +
      exists (1 + ne, Ok "" s (I :: [])) ; simpl ; eauto.
Defined.

Definition greedy_interp : forall e s, greedy_interp_type e s.
  intros e s Hu.
  change e with (get_regex (mk_input e s)) in *.
  change s with (get_string (mk_input e s)).
    apply (well_founded_induction
           wf_input_lt
           (fun p => 
                greedy_interp_type (get_regex p) (get_string p))
          ) ; eauto.

  apply greedy_interp_F.  
Defined.

Definition interp_type e s :=
  {bs : code | exists e', e === e' /\ exists n cs rs, greedy e' s n (Ok cs rs bs) /\ bs :# e'} +
  {exists e' m, e === e' /\ greedy e' s m Error}.

Definition interp e s : interp_type e s.
  lets Hu : unprob e.
  destruct Hu as [e' [Heq' Hu']].
  assert (Hr : {r : nat * output | greedy e' s (fst r) (snd r)}).
  apply greedy_interp ; eauto.
  destruct Hr as [[n o] Hr] ; simpl in *.
  destruct o as [cs rs bs | ].
  -
    left ; exists* bs.
    exists e' ; splits* ; exists n cs rs ; splits*.
    assert (s = cs ++ rs) by (eapply greedy_prefix ; eauto).
    eapply greedy_typed ; eauto.
  -
    right ; exists* e' n.
Defined.