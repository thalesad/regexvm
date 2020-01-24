Set Implicit Arguments.

Require Export
        Syntax.BitCodes
        Syntax.Input
        Syntax.Problematic
        Syntax.Regex
        Semantics.Greedy
        Tactics.Tactics.


Open Scope string_scope.

Record result : Set
  := Result {
      bitcode   : code
    ; consumed  : string  
    ; remaining : string
    }.

Reserved Notation "s '<$-' e '~>' r" (at level 60, no associativity).

Inductive in_regex_p : string -> regex -> result -> Prop :=
| InEpsP
  : forall s, s <$- #1 ~> (Result [] "" s)
| InChrP
  : forall a s,
    (String a s) <$- ($ a) ~> (Result [] (String a "") s)
| InLeftP
  : forall s s' e e' bs r,
    bs = bitcode r ->
    s  = consumed r ->
    s' = remaining r -> 
    (s ++ s') <$- e ~> r ->
    (s ++ s') <$- (e :+: e') ~> (Result (O :: bs) s s')
| InRightP : forall s s' e e' bs r,
    bs = bitcode r ->
    s  = consumed r ->
    s' = remaining r -> 
    ~ (s <<- e) -> 
    (s ++ s') <$- e' ~> r ->
    (s ++ s') <$- (e :+: e') ~> (Result (I :: bs) s s')
| InCatP : forall s s' s'' s1 e e' bs1 bs2 r2 r1,
    bs1 = bitcode r1 ->
    s = consumed r1 ->
    s1 = remaining r1 ->
    s1 = s' ++ s'' ->
    bs2 = bitcode r2 ->
    s' = consumed r2 ->
    s'' = remaining r2 -> 
    (s ++ s' ++ s'') <$- e ~> r1 ->
    (s' ++ s'') <$- e' ~> r2 ->
    ~ (exists s2 s3, s = s2 ++ s3 /\ s2 <<- e /\ (s3 ++ s') <<- e') ->  
    (s ++ s' ++ s'') <$- (e @ e') ~> (Result (bs1 ++ bs2)%list  (s ++ s') s'')
| InStarLeftP : forall s e,
    s <$- (Star e) ~> (Result (I :: []) "" s)
| InStarRightP : forall s1 s2 s3 e bs bss r1 s1' rs,
    s1 <> "" ->
    s1 = consumed r1 ->
    bs = bitcode r1 ->
    s1' = remaining r1 ->
    s1' = s2 ++ s3 -> 
    (s1 ++ s2 ++ s3) <$- e ~> r1 -> 
    (s2 ++ s3) <$- (Star e) ~> rs ->
    s2 = consumed rs ->
    s3 = remaining rs ->
    bss = bitcode rs ->
    ~ (exists s4 s5, s1 = s4 ++ s5 /\ s4 <> "" /\ s4 <<- e /\ (s5 ++ s2) <<- (e ^*)) -> 
    (s1 ++ s2 ++ s3) <$- (Star e) ~> (Result (O :: (bs ++ bss))%list (s1 ++ s2) s3)
where "s '<$-' e '~>' r" := (in_regex_p s e r).

Hint Constructors in_regex_p : core.

(*
Definition in_regex_p_type :=
  fun e s => s <<- e \/ not_in_regex s e ->
          forall s', (exists bs, (s ++ s') <$- e ; s ; s' ; bs /\ is_code_of bs e) \/
                (forall bs, ~ (s ++ s') <$- e ; s ; s' ; bs).

Lemma in_regex_p_complete_F
  : forall p, (forall p', input_lt p' p -> in_regex_p_type (get_regex p') (get_string p')) ->
         in_regex_p_type (get_regex p) (get_string p).
Proof.
  intros [e s] IH ; unfold in_regex_p_type in * ; simpl in * ; intros H s'.
  destruct H as [H | H'].
  -
    inverts* H.
    +
      left ; exists (@nil bit) ; splits ; simpl ; eauto.
    +
      assert (LT1 : input_lt (mk_input e0 s0) (mk_input (e0 @ e') (s0 ++ s'0)))
        by crush.
      assert (He0 : s0 <<- e0 \/ not_in_regex s0 e0) by crush.
      lets IH1 : IH (mk_input e0 s0) LT1 He0 (s'0 ++ s').
      assert (LT2 : input_lt (mk_input e' s'0) (mk_input (e0 @ e') (s0 ++ s'0)))
        by crush.
      assert (He'0 : s'0 <<- e' \/ not_in_regex s'0 e') by crush.
      lets IH2 : IH (mk_input e' s'0) LT2 He'0 s'.
      crush.
      left ; exists (x0 ++ x)%list ; splits ; eauto.
      rewrite string_app_assoc. eapply InCatP ; eauto.
      right. intros bs' Hx.
      inverts* Hx.
  inverts* H.
  -
    change (String c s') with (String c "" ++ s').
    exists (@nil bit). splits*.
    apply InChrP.
  -
    assert (LT1 : input_lt (mk_input e0 s0) (mk_input (e0 @ e') (s0 ++ s'0)))
      by crush.
    lets IH1 : IH (mk_input e0 s0) LT1 H0 (s'0 ++ s').
    assert (LT2 : input_lt (mk_input e' s'0) (mk_input (e0 @ e') (s0 ++ s'0)))
      by crush.
    lets IH2 : IH (mk_input e' s'0) LT2 H1 s'. crush.
    simpl in *.
    exists (x0 ++ x)%list. splits*.
    rewrite string_app_assoc ; eauto.
  -
    assert (LT : input_lt (mk_input e0 s)(mk_input (e0 :+: e') s))
       by (apply left_lex ; unfold regex_lt ; crush).
    lets IHe : IH (mk_input e0 s) LT H0 s' ; crush.
    exists* (O :: x).
  -
    assert (LT : input_lt (mk_input e' s)(mk_input (e0 :+: e') s))
       by (apply left_lex ; unfold regex_lt ; crush).
    lets IHe : IH (mk_input e' s) LT H0 s' ; crush.
    exists* (I :: x). splits*. constructor ; eauto.
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
    crush.
    exists (O :: (x0 ++ x))%list.
    rewrite string_app_assoc.
    rewrite! string_app_rewind ; eauto.
Qed.

Lemma in_regex_p_complete
  : forall e s, s <<- e -> forall s', exists bs, (s ++ s') <$- e ; s ; s' ; bs /\ is_code_of bs e.
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
*)

Definition in_regex_p_sound_type :=
  fun e s r => s <$- e ~> r -> s = (consumed r) ++ (remaining r) /\
                               (consumed r) <<- e           /\
                               is_code_of (bitcode r) e.


Lemma in_regex_p_sound_F
  : forall p, (forall p', input_lt p' p -> forall r, in_regex_p_sound_type (get_regex p')
                                                           (get_string p')
                                                           r) ->
            forall r, in_regex_p_sound_type (get_regex p) (get_string p) r.
Proof.
  intros [e s] IH [bs s1 s'] ;
    unfold in_regex_p_sound_type in * ; simpl in * ; intros H.
  inverts* H ; splits* ; try (rewrite string_app_assoc) ; auto.
  -
    assert (LT : input_lt (mk_input e0 ((consumed r) ++ (remaining r)))
                          (mk_input (e0 :+: e') ((consumed r) ++ (remaining r))))
      by crush. 
    lets IHe : IH (mk_input e0 ((consumed r) ++ (remaining r))) LT H8.
    simpl in *.
    destruct IHe as [Heqs Hes] ; crush.
  -
    assert (LT : input_lt (mk_input e0 ((consumed r) ++ (remaining r)))
                          (mk_input (e0 :+: e') ((consumed r) ++ (remaining r))))
      by crush.
    lets IHe : IH (mk_input e0 ((consumed r) ++ (remaining r))) LT H8.
    destruct IHe as [Heqs Hes] ; crush.    
  -
    assert (LT : input_lt (mk_input e' ((consumed r) ++ (remaining r)))
                          (mk_input (e0 :+: e') ((consumed r) ++ (remaining r)))) 
      by crush.
    lets IHe : IH (mk_input e' ((consumed r) ++ (remaining r))) LT H9.
    destruct IHe as [Heqs Hes] ; crush.
  -
    assert (LT : input_lt (mk_input e' ((consumed r) ++ (remaining r)))
                          (mk_input (e0 :+: e') ((consumed r) ++ (remaining r))))
      by crush.
    lets IHe : IH (mk_input e' ((consumed r) ++ (remaining r))) LT H9.
    destruct IHe as [Heqs Hes] ; crush.
  -
    assert (LTL : input_lt
                    (mk_input e0 (consumed r1 ++ consumed r2 ++ remaining r2))
                    (mk_input (e0 @ e') (consumed r1 ++ consumed r2 ++ remaining r2)))
      by (apply left_lex ; unfold regex_lt ; crush).
    assert (LTR : input_lt
                    (mk_input e' (consumed r2 ++ remaining r2))
                    (mk_input (e0 @ e') (consumed r1 ++ consumed r2 ++ remaining r2)))
      by (apply left_lex ; unfold regex_lt ; crush).
    lets IHl : IH (mk_input e0 (consumed r1 ++ consumed r2 ++ remaining r2)) LTL H12.
    simpl in *.
    lets IHr : IH (mk_input e' (consumed r2 ++ remaining r2)) LTR H13. simpl in *.
    destruct IHl as [Hel Hsl].
    destruct IHr as [Her Hsr] ; crush.
  -
    assert (LTL : input_lt
                    (mk_input e0 (consumed r1 ++ consumed r2 ++ remaining r2))
                    (mk_input (e0 @ e') (consumed r1 ++ consumed r2 ++ remaining r2)))
      by (apply left_lex ; unfold regex_lt ; crush).
    assert (LTR : input_lt
                    (mk_input e' (consumed r2 ++ remaining r2))
                    (mk_input (e0 @ e') (consumed r1 ++ consumed r2 ++ remaining r2)))
      by (apply left_lex ; unfold regex_lt ; crush). 
    lets IHl : IH (mk_input e0 (consumed r1 ++ consumed r2 ++ remaining r2)) LTL H12.
    simpl in *.
    lets IHr : IH (mk_input e' (consumed r2 ++ remaining r2)) LTR H13. simpl in *.
    destruct IHl as [Hel Hsl].
    destruct IHr as [Her Hsr] ; crush ; eauto.
  -
    destruct (consumed r1) eqn : Hr1 ; crush.
    assert (LTe : input_lt
                    (mk_input e0 (String a (s ++ consumed rs ++ remaining rs)))
                    (mk_input (Star e0) (String a (s ++ consumed rs ++ remaining rs))))
      by (apply left_lex ; unfold regex_lt ; crush).
    assert (LTs : input_lt
                    (mk_input (Star e0) (consumed rs ++ remaining rs))
                    (mk_input (Star e0) (String a (s ++ consumed rs ++ remaining rs)))).
    +
      apply right_lex ; unfold string_lt ; crush.
      rewrite! string_app_length ; crush.
    +
      rewrite string_app_rewind.
      apply InStarRight with (s := String a s)(s' := consumed rs) ; crush.
      lets IHe : IH (mk_input e0 (String a (s ++ consumed rs ++ remaining rs))) LTe H8.
      lets IHs : IH (mk_input (Star e0) (consumed rs ++ remaining rs)) LTs H9.
      simpl in *.
      destruct IHe as [Hse He].
      destruct IHs as [Hss Hs] ; crush.
      lets IHe : IH (mk_input e0 (String a (s ++ consumed rs ++ remaining rs))) LTe H8.
      lets IHs : IH (mk_input (Star e0) (consumed rs ++ remaining rs)) LTs H9.
      simpl in *.
      crush.
  -
    destruct (consumed r1) eqn : Hr1 ; crush.
    assert (LTe : input_lt
                    (mk_input e0 (String a (s ++ consumed rs ++ remaining rs)))
                    (mk_input (Star e0) (String a (s ++ consumed rs ++ remaining rs))))
      by (apply left_lex ; unfold regex_lt ; crush).
    assert (LTs : input_lt
                    (mk_input (Star e0) (consumed rs ++ remaining rs))
                    (mk_input (Star e0) (String a (s ++ consumed rs ++ remaining rs)))).
    +
      apply right_lex ; unfold string_lt ; crush.
      rewrite! string_app_length ; crush.
    +
     lets IHe : IH (mk_input e0 (String a (s ++ consumed rs ++ remaining rs))) LTe H8.
     lets IHs : IH (mk_input (Star e0) (consumed rs ++ remaining rs)) LTs H9.
     simpl in *.
     crush.
Qed.

Lemma in_regex_p_sound
  : forall e s r, s <$- e ~> r ->
             s = (consumed r) ++ (remaining r) /\
             (consumed r) <<- e               /\
             is_code_of (bitcode r) e.
Proof.
  intros e s.
  change s with (get_string (mk_input e s)).
  change e with (get_regex (mk_input e s)).
  apply (well_founded_ind
           wf_input_lt
           (fun p => forall r,
                in_regex_p_sound_type (get_regex p) (get_string p) r)
        ).
  apply in_regex_p_sound_F.
Qed.
(*    
Lemma starp_singleton
  : forall e s a s' bs r,
    String a s = consumed r      ->
    s' = remaining r             ->
    bs = bitcode r               -> 
    (String a s ++ s') <$- e ~> r ->
    (String a s ++ s') <$- (Star e ) ~> (Result (O :: bs ++ [I])%list (String a s) s').
Proof.
  intros e s a s' bs r Hc Hr Hb H. substs.
  assert (Heq : String a s ++ remaining r = String a s ++ "" ++ remaining r) by crush.
  rewrite Heq.
  assert (Hn : String a s <> "") by crush.
  eapply InStarRightP with (bs := (bitcode r))(s2 := "")(s3 := remaining r) in Hn ;
    eauto.
  rewrite string_app_nil_end in * ; auto.
  crush.
 admit.
Admitted.
*)

Definition in_regex_p_greedy_type :=
  fun e s r => s <$- e ~> r -> greedy e (consumed r) (bitcode r).

Lemma in_regex_p_greedy_F
  : forall p, (forall p', input_lt p' p -> forall r, in_regex_p_greedy_type (get_regex p') (get_string p') r) ->
         forall r, in_regex_p_greedy_type (get_regex p) (get_string p) r.
  intros [e s] IH r ; unfold in_regex_p_greedy_type in * ; simpl in * ; intros He.
  inverts* He ; crush.
  -
    assert (HLt : input_lt (mk_input e0 (consumed r0 ++ remaining r0))
                           (mk_input (e0 :+: e') (consumed r0 ++ remaining r0)))
      by crush.
    lets J : IH HLt H2 ; simpl in * ; eauto.
  -
    assert (HLt : input_lt (mk_input e' (consumed r0 ++ remaining r0))
                           (mk_input (e0 :+: e') (consumed r0 ++ remaining r0))) by crush.
    lets J : IH HLt H3 ; simpl in * ; eauto.
  -
    assert (HLt1 : input_lt (mk_input e0 (consumed r1 ++ consumed r2 ++ remaining r2))
                            (mk_input (e0 @ e') (consumed r1 ++ consumed r2 ++ remaining r2)))
      by (apply left_lex ; unfold regex_lt ; crush).
    assert (HLt2 : input_lt (mk_input e' (consumed r2 ++ remaining r2))
                            (mk_input (e0 @ e') (consumed r1 ++ consumed r2 ++ remaining r2)))
      by (apply left_lex ; unfold regex_lt ; crush).
    lets J1 : IH HLt1 H6.
    lets J2 : IH HLt2 H7.
    crush. 
  -
    assert (HLt1 : input_lt (mk_input e0 (consumed r1 ++ consumed rs ++ remaining rs))
                            (mk_input (e0 ^*) (consumed r1 ++ consumed rs ++ remaining rs)))
             by (apply left_lex ; unfolds ; crush).
    destruct (consumed r1) eqn : Hr1 ; crush.
    assert (HLt2 : input_lt (mk_input (e0 ^*) (consumed rs ++ remaining rs))
                            (mk_input (e0 ^*) (String a s ++ consumed rs ++ remaining rs)))
             by (apply right_lex ; unfolds ; rewrite! string_app_length ; crush).
    lets J1 : IH HLt1 H4.
    lets J2 : IH HLt2 H5.
    rewrite string_app_rewind.
    econstructor ; crush.
Qed.

Lemma in_regex_p_greedy
   : forall e s r, s <$- e ~> r -> greedy e (consumed r) (bitcode r).
Proof.
  intros e s r.
  change s with (get_string (mk_input e s)).
  change e with (get_regex (mk_input e s)).
  apply (well_founded_ind
           wf_input_lt
           (fun p => forall r,
                in_regex_p_greedy_type (get_regex p) (get_string p) r)
        ).
  apply in_regex_p_greedy_F.
Qed.

Definition valid_result e s := 
  {r | s = (consumed r ++ remaining r) /\ s <$- e ~> r } + {~ s <<- e}.

Definition interp_type e s := unproblematic e -> valid_result e s.

Definition interp_F
  : forall p, (forall p', input_lt p' p -> interp_type (get_regex p') (get_string p')) ->
         interp_type (get_regex p) (get_string p).
  intros [e s] IH ; simpl in *.
  refine (match e as e', s as s' return e = e' -> s = s' -> interp_type e' s' with
          | #0 , _ => fun _ _ _ => !!
          | #1 , _ => fun _ _ _ => [|| Result (@nil bit) "" s ||]
          | $ a', "" => fun _ _ _ => !!
          | $ a', (String a s1) => fun _ _ _ =>
             if ascii_dec a a' then [|| Result (@nil bit) (String a' "") s1 ||] else !!
          | e1 @ e2, _ => fun _ _ _ =>
             match IH (mk_input e1 s) _ _ with
             | [|| r1 ||] => 
               match IH (mk_input e2 (remaining r1)) _ _ with
               | [|| r2 ||] => [|| Result (bitcode r1 ++ bitcode r2)%list
                                      (consumed r1 ++ consumed r2) (remaining r2) ||]
               | !! => !!
               end
             | !! => !!
             end
          | e1 :+: e2, _ => fun _ _ _ =>
             match IH (mk_input e1 s) _ _ with
             | [|| r1 ||] => [|| Result (O :: bitcode r1)
                                    (consumed r1)
                                    (remaining r1) ||]
             | !!       => 
             match IH (mk_input e2 s) _ _ with
               | [|| r1 ||] => [|| Result (I :: bitcode r1)
                                    (consumed r1)
                                    (remaining r1) ||]
               | !!       => !!
               end 
             end
          | Star _, "" => fun _ _ _ => [|| Result (I :: nil) "" "" ||]
          | Star e1, _ => fun _ _ _ =>
             match IH (mk_input e1 s) _ _ with
             | [|| r1 ||] =>
               match string_dec (remaining r1) "" with
               | Yes => [|| Result (O :: bitcode r1 ++ [ I ])%list
                                 (consumed r1) "" ||]
               | No => 
                 match IH (mk_input (Star e1) (remaining r1)) _ _ with 
                 | [|| r2 ||] => [|| Result (O :: bitcode r1 ++ bitcode r2)%list
                                        (consumed r1 ++ consumed r2)
                                        (remaining r2) ||]
                 | !!       => [|| Result (O :: bitcode r1 ++ [ I ])%list
                                        (consumed r1)
                                        (remaining r1) ||]
                 end
               end
             | !! => [|| Result (I :: nil) "" s ||]
             end
          end (eq_refl e) (eq_refl s)) ; clear IH ; substs ; eauto ;
    try solve [apply left_lex ; unfolds ; crush] ;
    try solve [inverts* u] ; crush ; try solve [rewrite string_app_assoc ; auto] ;
      try solve [econstructor ; crush] ; try solve [inverts* H].
  -
    rewrite H1 in * ; eapply InCatP ; eauto.
  -
    inverts* u.
    inverts* H.
    (* rewrite H1 in * ; eapply InCatP ; crush.
    clear s1 s2 s0 e3.
    rewrite H3 in *. clear H3.
    apply in_regex_p_sound in H0 ; crush.
  -
    inverts* H.
    rewrite <- (string_app_nil_end s).
    apply NotCatLeft ; auto.
  -

  -
    inverts* u.
    apply in_regex_p_sound in H0 ; crush.
    destruct (consumed r1) eqn : Hc1 ; crush.
  -
    inverts* u.
    rewrite H1 in *. rewrite H in H0.
    apply InStarRightP with (r1 := r1)
                            (s1' := consumed r2 ++ remaining r2)
                            (rs := r2) ; crush.
    apply in_regex_p_sound in H0 ; crush.
  -
    inverts* u.
    destruct r1 as [bs1 cs1 rs1]. simpl in *.
    assert (He1 : cs1 <<- e1).
    +
      apply in_regex_p_sound in H0 ; crush.
    +
      destruct cs1 ; crush.
      rewrite string_app_rewind.
      apply starp_singleton with (r := Result bs1 (String a0 cs1) rs1) ; crush.
Defined. *)


Definition interp'
   : forall p : input, interp_type (get_regex p) (get_string p).
  intros [e s].
  apply (well_founded_induction
           wf_input_lt
           (fun p => interp_type (get_regex p) (get_string p))).
  apply interp_F.
Defined.

Definition interp
  : forall e s,
    {r | exists e', unproblematic e' /\ e === e'  /\
               s = consumed r ++ remaining r /\
               s <$- e' ~> r /\
               (bitcode r) :# e'} + {exists e', e === e' /\ not_in_regex s e'}. 
  intros e s.
  lets J : unprob e.
  destruct J as [e' [Heq Hun]].
  lets J : interp' (mk_input e' s) Hun.
  unfolds in J. simpl in *.
  destruct J as [[r [Hs He']] | Hnr ] ; try solve [right*].
  -
    left ; exists r e' ; crush.
    apply in_regex_p_sound in He' ; crush.
Defined.
