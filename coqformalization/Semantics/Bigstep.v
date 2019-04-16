Set Implicit Arguments.

Require Export
        Syntax.BitCodes
        Syntax.Input
        Syntax.Problematic
        Syntax.Regex
        Tactics.Tactics.

Open Scope string_scope.

Reserved Notation "s '<$-' e ';' s1 ';' s2" (at level 60, no associativity).

Inductive in_regex_p : string -> regex -> string -> string -> Prop :=
| InEpsP
  : forall s, s <$- #1 ; "" ; s
| InChrP
  : forall a s,
    (String a s) <$- ($ a) ; (String a "") ; s
| InLeftP
  : forall s s' e e',
    (s ++ s') <$- e ; s ; s' ->
    (s ++ s') <$- (e :+: e') ; s ; s'
| InRightP : forall s s' e e',
    (s ++ s') <$- e' ; s ; s' ->
    (s ++ s') <$- (e :+: e') ; s ; s'
| InCatP : forall s s' s'' e e',
    (s ++ s' ++ s'') <$- e ; s ; (s' ++ s'') ->
    (s' ++ s'') <$- e' ; s' ; s'' ->
    (s ++ s' ++ s'') <$- (e @ e') ; (s ++ s') ; s''
| InStarLeftP : forall s e,
    s <$- (Star e) ; "" ; s
| InStarRightP : forall s1 s2 s3 e,
    s1 <> "" ->
    (s1 ++ s2 ++ s3) <$- e ; s1 ; (s2 ++ s3) ->
    (s2 ++ s3) <$- (Star e) ; s2 ; s3 ->
    (s1 ++ s2 ++ s3) <$- (Star e) ; (s1 ++ s2) ; s3
where "s '<$-' e ';' s1 ';' s2" := (in_regex_p s e s1 s2).

Hint Constructors in_regex_p.

Definition in_regex_p_type :=
  fun e s => s <<- e -> forall s', (s ++ s') <$- e ; s ; s'.

Lemma in_regex_p_complete_F
  : forall p, (forall p', input_lt p' p -> in_regex_p_type (get_regex p') (get_string p')) ->
         in_regex_p_type (get_regex p) (get_string p).
Proof.
  intros [e s] IH ; unfold in_regex_p_type in * ; simpl in * ; intros H s'.
  inverts* H.
  -
    change (String c s') with (String c "" ++ s').
    apply InChrP.
  -
    assert (LT1 : input_lt (mk_input e0 s0) (mk_input (e0 @ e') (s0 ++ s'0)))
      by crush.
    lets IH1 : IH (mk_input e0 s0) LT1 H0 (s'0 ++ s').
    assert (LT2 : input_lt (mk_input e' s'0) (mk_input (e0 @ e') (s0 ++ s'0)))

      by crush.
    lets IH2 : IH (mk_input e' s'0) LT2 H1 s'.
    simpl in *.
    rewrite string_app_assoc ; eauto.
  -
    assert (LT : input_lt (mk_input e0 s)(mk_input (e0 :+: e') s))
       by (apply left_lex ; unfold regex_lt ; crush).
    lets IHe : IH (mk_input e0 s) LT H0 s' ; crush.
  -
    assert (LT : input_lt (mk_input e' s)(mk_input (e0 :+: e') s))
       by (apply left_lex ; unfold regex_lt ; crush).
    lets IHe : IH (mk_input e' s) LT H0 s' ; crush.
  -
    assert (LTe : input_lt (mk_input e0 s0) (mk_input (Star e0) (s0 ++ s'0))) by crush.
    destruct s0 ; crush.
    assert (LTs : input_lt (mk_input (Star e0) s'0)
                           (mk_input (Star e0) (String a s0 ++ s'0))) by crush.
    lets IHe : IH (mk_input e0 (String a s0))
                  LTe
                  H1 (s'0 ++ s') ; simpl in *.
    lets IHes : IH (mk_input (Star e0) s'0)
                   LTs
                   H2
                   s' ; simpl in *.
    rewrite string_app_assoc.
    rewrite! string_app_rewind ; eauto.
Qed.

Lemma in_regex_p_complete : forall e s, s <<- e -> forall s', (s ++ s') <$- e ; s ; s'.
Proof.
  intros e s.
  change s with (get_string (mk_input e s)).
  change e with (get_regex (mk_input e s)).  
  eapply (well_founded_ind
            wf_input_lt
            (fun p => in_regex_p_type (get_regex p) (get_string p))
            in_regex_p_complete_F
            (mk_input e s)).
Qed.

Definition in_regex_p_sound_type :=
  fun e s s1 s' => s <$- e ; s1 ; s' -> s = s1 ++ s' /\ s1 <<- e.


Lemma in_regex_p_sound_F
  : forall p, (forall p', input_lt p' p -> forall s1 s', in_regex_p_sound_type (get_regex p')
                                                               (get_string p')
                                                               s1 s') ->
            forall s1 s', in_regex_p_sound_type (get_regex p) (get_string p) s1 s'.
Proof.
  intros [e s] IH s1 s' ; unfold in_regex_p_sound_type in * ; simpl in * ; intros H.
  inverts* H.
  -
    assert (LT : input_lt (mk_input e0 (s1 ++ s')) (mk_input (e0 :+: e') (s1 ++ s'))) 
      by crush. 
    lets IHe : IH (mk_input e0 (s1 ++ s')) LT H0.
    simpl in *.
    destruct IHe as [Heqs Hes] ; crush.
  -
    assert (LT : input_lt (mk_input e' (s1 ++ s')) (mk_input (e0 :+: e') (s1 ++ s'))) 
      by crush. 
    lets IHe : IH (mk_input e' (s1 ++ s')) LT H0.
    destruct IHe as [Heqs Hes] ; crush.
  -
    assert (LTL : input_lt (mk_input e0 (s0 ++ s'0 ++ s'))
                           (mk_input (e0 @ e') (s0 ++ s'0 ++ s')))
      by (apply left_lex ; unfold regex_lt ; crush).
    assert (LTR : input_lt (mk_input e' (s'0 ++ s'))
                           (mk_input (e0 @ e') (s0 ++ s'0 ++ s')))
      by (apply left_lex ; unfold regex_lt ; crush).
    lets IHl : IH (mk_input e0 (s0 ++ s'0 ++ s')) LTL H0. simpl in *.
    lets IHr : IH (mk_input e' (s'0 ++ s')) LTR H1. simpl in *.
    destruct IHl as [Hel Hsl].
    destruct IHr as [Her Hsr] ; crush.
    rewrite <- string_app_assoc.
    fequals*. eauto.
  - 
    destruct s0 ; crush.
    assert (LTe : input_lt (mk_input e0 (String a (s0 ++ s2 ++ s')))
                           (mk_input (Star e0) (String a (s0 ++ s2 ++ s'))))
      by (apply left_lex ; unfold regex_lt ; crush).
    assert (LTs : input_lt (mk_input (Star e0) (s2 ++ s'))
                           (mk_input (Star e0) (String a (s0 ++ s2 ++ s')))).
    +
      apply right_lex ; unfold string_lt ; crush.
      rewrite! string_app_length ; crush.
    +
      fequals*.
      now rewrite string_app_assoc.
    +
      assert (LTe : input_lt (mk_input e0 (String a (s0 ++ s2 ++ s')))
                             (mk_input (Star e0) (String a (s0 ++ s2 ++ s'))))
        by (apply left_lex ; unfold regex_lt ; crush).
      assert (LTs : input_lt (mk_input (Star e0) (s2 ++ s'))
                             (mk_input (Star e0) (String a (s0 ++ s2 ++ s')))).
      *
        apply right_lex ; unfold string_lt ; crush.
        rewrite! string_app_length ; crush.
      * 
        lets IHe : IH (mk_input e0 (String a (s0 ++ s2 ++ s'))) LTe H1.
        lets IHs : IH (mk_input (Star e0) (s2 ++ s')) LTs H2. simpl in *.
        destruct IHe as [Hse He].
        destruct IHs as [Hss Hs] ; crush.
        rewrite string_app_rewind. eauto.
Qed.

Lemma in_regex_p_sound : forall e s s1 s', s <$- e ; s1 ; s' -> s = s1 ++ s' /\ s1 <<- e.
Proof.
  intros e s.
  change s with (get_string (mk_input e s)).
  change e with (get_regex (mk_input e s)).
  apply (well_founded_ind
           wf_input_lt
           (fun p => forall s1 s', in_regex_p_sound_type (get_regex p) (get_string p) s1 s')
        ).
  apply in_regex_p_sound_F.
Qed.


Lemma starp_singleton
  : forall e s s', (s ++ s') <$- e ; s ; s' -> (s ++ s') <$- (e ^*) ; s ; s' .
Proof.
  intros e s s' H.
  destruct s ; crush.
  assert (Heq : String a s = String a s ++ "")
    by (now rewrite string_app_nil_end).
  rewrite! string_app_rewind.
  rewrite Heq.
  rewrite string_app_assoc.
  apply InStarRightP ; crush.
Qed.

Hint Resolve starp_singleton.

Record result : Set
  := Result {
      bitcode   : code
    ; consumed  : string  
    ; remaining : string
    }.

Definition valid_result e s := 
  {{r | s = (consumed r ++ remaining r) /\
       (consumed r ++ remaining r) <$- e ; (consumed r) ; (remaining r) /\
                                          (bitcode r) :# e}}.

Definition interp_type e s := unproblematic e -> valid_result e s.
 
Definition interp_F
  : forall p, (forall p', input_lt p' p -> interp_type (get_regex p') (get_string p')) ->
         interp_type (get_regex p) (get_string p).
  intros [e s] IH ; simpl in *.
  refine (match e as e', s as s' return e = e' -> s = s' -> interp_type e' s' with
          | #0 , _ => fun _ _ _ => ??
          | #1 , _ => fun _ _ _ => [| Result (@nil bit) "" s |]
          | $ a', "" => fun _ _ _ => ??
          | $ a', (String a s1) => fun _ _ _ =>
             if ascii_dec a a' then [| Result (@nil bit) (String a' "") s1 |] else ??
          | e1 @ e2, _ => fun _ _ _ =>
             match IH (mk_input e1 s) _ _ with
             | [| r1 |] => 
               match IH (mk_input e2 (remaining r1)) _ _ with
               | [| r2 |] => [| Result (bitcode r1 ++ bitcode r2)%list
                                      (consumed r1 ++ consumed r2) (remaining r2) |]
               | ?? => ??
               end
             | ?? => ??
             end
          | e1 :+: e2, _ => fun _ _ _ =>
             match IH (mk_input e1 s) _ _ with
             | [| r1 |] => [| Result (O :: bitcode r1)
                                    (consumed r1)
                                    (remaining r1) |]
             | ??       =>
               match IH (mk_input e2 s) _ _ with
               | [| r1 |] => [| Result (I :: bitcode r1)
                                    (consumed r1)
                                    (remaining r1) |]
               | ??       => ??
               end
             end
          | Star _, "" => fun _ _ _ => [| Result (I :: nil) "" "" |]
          | Star e1, _ => fun _ _ _ =>
             match IH (mk_input e1 s) _ _ with
             | [| r1 |] =>
               match string_dec (remaining r1) "" with
               | Yes => [| Result (O :: bitcode r1 ++ [ I ])%list
                                 (consumed r1) "" |]
               | No => 
                 match IH (mk_input (Star e1) (remaining r1)) _ _ with 
                 | [| r2 |] => [| Result (O :: bitcode r1 ++ bitcode r2)%list
                                        (consumed r1 ++ consumed r2)
                                        (remaining r2) |]
                 | ??       => [| Result (O :: bitcode r1 ++ [ I ])%list
                                        (consumed r1)
                                        (remaining r1) |]
                 end
               end
             | ?? => [| Result (I :: nil) "" s |]
             end
          end (eq_refl e) (eq_refl s)) ; simpl in * ;
    try solve [apply left_lex ; unfolds ; crush] ; crush.
    inverts* u. inverts* u.
    rewrite! string_app_assoc ; crush.
    rewrite string_app_assoc.
    apply InCatP ; auto.  
    rewrite H1 in H3 ; auto.
    inverts* u.
    inverts* u. inverts* u.

    rewrite e3 in *.
    apply starp_singleton in H1 ; auto.
    destruct (consumed r1) eqn : Hc1 ; crush.
    apply in_regex_p_sound in H1. crush. inverts* u.
    crush.
    now rewrite string_app_assoc.
    rewrite string_app_assoc.
    apply InStarRightP ; eauto. inverts* u.
    intro Hc. rewrite Hc in *. simpl in *.
    apply in_regex_p_sound in H3. crush.
    crush.
Defined.

Definition interp'
   : forall p : input, interp_type (get_regex p) (get_string p).
  intros [e s].
  apply (well_founded_induction
           wf_input_lt
           (fun p => interp_type (get_regex p) (get_string p))).
  apply interp_F.
Defined.

Definition interp
  : forall e s, {{r | exists e', unproblematic e' /\ e === e'  /\
                       s = consumed r ++ remaining r /\
                      (consumed r ++ remaining r) <$- e' ; consumed r ; remaining r /\
                      (bitcode r) :# e'}}. 
  intros e s.
  lets J : unprob e.
  destruct J as [e' [Heq Hun]].
  lets J : interp' (mk_input e' s) Hun.
  unfolds in J. simpl in *.
  destruct J as [ | r [Hs [He' Hb]]].
  - exact ??.
  -
    apply Found with (x := r).
    exists e' ; crush.
Defined.
