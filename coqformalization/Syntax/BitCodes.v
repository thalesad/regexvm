Set Implicit Arguments.


Require Export
        List 
        Syntax.Tree.

Export ListNotations.

Open Scope list_scope.

Inductive bit : Set := O : bit | I : bit.

Definition code := list bit.

Reserved Notation "bs ':#' e" (at level 60, no associativity).

Inductive is_code_of : code -> regex -> Prop :=
| ICEpsilon : [] :# #1
| ICChar    : forall c, [] :# ($ c)
| ICLeft    : forall bs e e'
  , bs :# e ->
    (O :: bs) :# (e :+: e')
| ICRight   : forall bs e e'
  , bs :# e' ->
    (I :: bs) :# (e :+: e')
| ICCat : forall bs bs' e e'
  , bs :# e ->
    bs' :# e' ->
    (bs ++ bs') :# (e @ e')
| ICNil : forall e, (I :: []) :# (e ^*)
| ICCons : forall e bs bss, 
    bs :# e -> 
    bss :# (e ^*) -> 
    (O :: bs ++ bss) :# (e ^*) 
where "bs ':#' e" := (is_code_of bs e).


Hint Constructors is_code_of.


Fixpoint encode (t : tree) : code :=
  match t with
  | TLeft t' => O :: encode t'
  | TRight t' => I :: encode t'
  | TCat tl tr => encode tl ++ encode tr
  | TNil => [ I ]
  | TCons t ts =>
    O :: encode t ++ encode ts
  | _ => [] 
  end.

Lemma encode_sound
  : forall bs e, bs :# e -> exists t, t :> e /\ encode t = bs.
Proof.
  intros bs e H ; induction H.
  +
    exists* TUnit.
  +
    exists* (TChr c).
  +
    destruct IHis_code_of as [tl [Htl Hcl]].
    exists (TLeft tl) ; simpl ; crush.
  +
    destruct IHis_code_of as [tr [Htr Hcr]].
    exists (TRight tr) ; simpl ; crush.
  +
    destruct IHis_code_of1 as [tl [Htl Hcl]].
    destruct IHis_code_of2 as [tr [Htr Hcr]].
    exists (TCat tl tr) ; simpl ; crush.
  + 
    exists TNil ; simpl ; crush.
  +
    destruct IHis_code_of1 as [t [Ht Hc]].
    destruct IHis_code_of2 as [ts [Hts Hcs]].
    exists (TCons t ts) ; crush.
Qed.

Lemma encode_complete
  : forall t e, t :> e -> (encode t) :# e.
Proof.
  induction t ; intros e H ; inverts H ; crush.
Qed.


Section WF_DECODE.
  Definition decode_input := sigT (fun _ : regex => code).

  Definition mk_input (e : regex)(bs : code) :=
    existT _ e bs.

  Definition get_bits (inp : decode_input) : code :=
    let (_,bs) := inp in bs.

  Definition get_regex (inp : decode_input) : regex :=
    let (e,_) := inp in e.

  Definition decode_input_lt : decode_input -> decode_input -> Prop :=
    lexprod regex
            (fun _ => list bit)
            (fun (e e' : regex) => size e < size e')
            (fun (e : regex)(xs ys : list bit) => List.length xs < List.length ys).

  Definition wf_decode_input : well_founded decode_input_lt :=
    @wf_lexprod regex
                (fun _ : regex => list bit)
                (fun (e e' : regex) => size e < size e')
                (fun (e : regex)(xs ys : list bit) => List.length xs < List.length ys)
                (well_founded_ltof regex size)
                (fun _ => well_founded_ltof (list bit) (@List.length bit)).

  Lemma decode_lt_lemma1
      : forall e e' bs, decode_input_lt (mk_input e bs)
                                   (existT (fun _ : regex => list bit)
                                           (e :+: e') (O :: bs)).
  Proof.
    intros ; unfold mk_input, decode_input_lt ; apply left_lex ; crush.
  Qed.

  Lemma decode_lt_lemma2
      : forall e e' bs, decode_input_lt (mk_input e' bs)
                                   (existT (fun _ : regex => list bit)
                                           (e :+: e') (I :: bs)).
  Proof.
    intros ; unfold mk_input, decode_input_lt ; apply left_lex ; crush.
  Qed.

  Lemma decode_lt_lemma3
    : forall e e' bs, decode_input_lt (mk_input e bs)
                                 (existT (fun _ : regex => list bit) (e @ e') bs).
  Proof.
    intros ; unfold mk_input, decode_input_lt ; apply left_lex ; crush.
  Qed.

  Lemma decode_lt_lemma4
    : forall e e' bs bs1, decode_input_lt (mk_input e' bs1)
                                     (existT (fun _ : regex => list bit) (e @ e') bs).
  Proof.
    intros ; unfold mk_input, decode_input_lt ; apply left_lex ; crush.
  Qed.

  Lemma decode_lt_lemma5
    : forall e bs, decode_input_lt (mk_input e bs)
                              (existT (fun _ : regex => list bit) (e ^*) (O :: bs)).
  Proof.
    intros ; unfold mk_input, decode_input_lt ; apply left_lex ; crush.
  Qed.

  Lemma decode_lt_lemma6
    : forall e bs bs1, decode_input_lt (mk_input (e ^*) bs1)
                                         (existT (fun _ : regex => list bit) (e ^*)
                                              (O :: bs ++ bs1)).
   Proof.
     intros ; unfold decode_input_lt, mk_input ; apply right_lex ; crush.
     rewrite app_length ; crush.
   Qed.
End WF_DECODE.

Hint Resolve decode_lt_lemma1 decode_lt_lemma2
     decode_lt_lemma3 decode_lt_lemma4 decode_lt_lemma5
     decode_lt_lemma6 wf_decode_input.

Inductive nocode_for : code -> regex -> Prop :=
| NCEmpty : forall bs, nocode_for bs #0
| NCChoicenil : forall e e', nocode_for [] (e :+: e')
| NCLBase : forall bs e e', nocode_for bs e -> nocode_for (O :: bs) (e :+: e')
| NCRBase : forall bs e e', nocode_for bs e' -> nocode_for (I :: bs) (e :+: e')
| NCCat1 : forall bs bs1 bs2 e e',
    is_code_of bs1 e ->
    nocode_for bs2 e' ->
    bs = bs1 ++ bs2  ->
    nocode_for bs (e @ e')
| NCCat2 : forall bs e e',
    nocode_for bs e ->
    nocode_for bs (e @ e')
| NCStarnil : forall e, nocode_for [] (e ^*)
| NCStar : forall bs bs1 bs2 e,
      is_code_of bs1 e ->
      nocode_for bs2 (e ^*) ->
      bs = O :: bs1 ++ bs2  ->
      nocode_for bs (e ^*)
| NCStar1 : forall bs e,
    nocode_for bs e ->
    nocode_for (O :: bs) (e ^*).

Hint Constructors nocode_for.

Definition decode_type bs e :=
  {p : (tree * list bit) | exists bs2 t, p = (t,bs2) /\
                                    is_tree_of t e /\
                                    bs = (encode t) ++ bs2} +
  {nocode_for bs e}.

Definition decode_F : forall 
           (inp : decode_input)
           (IH : forall inp', decode_input_lt inp' inp -> decode_type (get_bits inp')
                                                                (get_regex inp')),
    decode_type (get_bits inp) (get_regex inp).
  intros inp canRec.
  destruct inp as [e bs] ; simpl in *.
  destruct e.
  +
    right*.
  +
    left ; exists* (TUnit , bs).
  +
    left ; exists* (TChr a , bs).
  +
    assert (Hlt : decode_input_lt (mk_input e1 bs) (mk_input (e1 @ e2) bs)) by eauto.
    lets K : canRec Hlt.
    destruct K.
    destruct s.
    destruct x as [t bs1].
    assert (Hlt1 : decode_input_lt (mk_input e2 bs1) (mk_input (e1 @ e2) bs)) by eauto.
    lets K1 : canRec Hlt1.
    destruct K1.
    destruct s.
    destruct x as [t1 bs2].
    left.
    exists (TCat t t1, bs2) bs2 (TCat t t1) ; splits* ; crush.
    simpl in *.
    right.
    destruct e as [bs2 [t1 Hx]].
    destruct Hx as [Hx1 [Hx2 Hx3]].
    injects Hx1.
    eapply NCCat1 ; eauto.
    apply encode_complete ; auto.
    simpl in *.
    right.
    eapply NCCat2 ; eauto.
  +
    destruct bs as [ | b' bs'] ; [right* | destruct b'].
    * 
      assert (Hlt1 : decode_input_lt (mk_input e1 bs')
                                     (mk_input (e1 :+: e2) (O :: bs'))) by eauto.
      lets K : canRec Hlt1.
      destruct K.
      left.
      destruct s. destruct x as [tl bs1].
      exists ((TLeft tl), bs1). exists bs1 (TLeft tl) ; splits ; crush.
      simpl in *.
      right. eauto.
    *
      assert (Hlt2 : decode_input_lt (mk_input e2 bs')
                                     (mk_input (e1 :+: e2) (I :: bs'))) by eauto.
      lets K : canRec Hlt2.
      destruct K.
      left.
      destruct s. destruct x as [tr bs1].
      exists (TRight tr, bs1). exists bs1 (TRight tr) ; splits ; crush.
      simpl in *. right ; eauto.
  +  
    destruct bs as [ | b' bs'] ; [ right* | destruct b'].
    * 
      assert (Hlt : decode_input_lt (mk_input e bs')
                                    (mk_input (e ^*) (O :: bs'))) by eauto.
      lets K : canRec Hlt ; simpl in *.
      destruct K.
      destruct s. destruct x as [t bs1].
      assert (Hlt1 : decode_input_lt (mk_input (e ^*) bs1)
                                     (mk_input (e ^*) (O :: (encode t) ++ bs1)))
                                       by eauto.
      assert (decode_type bs1 (e ^*)). 
        apply (canRec (mk_input (e ^*) bs1)) ; simpl in * ; crush.
      destruct H.
      destruct s. destruct x as [ts bs2].
      left. exists (TCons t ts, bs2) ; exists bs2 (TCons t ts) ; splits ; crush.
      right ; crush ; eauto.
      eapply NCStar ; eauto. apply encode_complete ; auto.
      right ; eapply NCStar1 ; eauto.
    *
      left. exists (TNil, bs') ; exists bs' TNil ; crush.
Defined.


Definition decode' (inp : decode_input) : decode_type (get_bits inp)
                                                      (get_regex inp) :=
  @well_founded_induction
    decode_input
    decode_input_lt
    wf_decode_input
    (fun inp' => decode_type (get_bits inp') (get_regex inp'))
    decode_F
    inp.

Definition invalid_code bs e :=
  nocode_for bs e \/ exists t b1 bs1, bs = (encode t) ++ (b1 :: bs1).

Definition decode e bs : {t | bs = encode t /\ is_tree_of t e} + {invalid_code bs e}.
  unfold invalid_code ; destruct* (decode' (mk_input e bs)).
  +
    destruct s as [[t bs2] H].
    destruct bs2.
    *
      left ; exists t ; crush. now rewrite app_nil_end.
    *
      right ; right ; crush.
      eexists ; eexists ; eexists ; eauto.
Defined.
