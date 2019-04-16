Set Implicit Arguments.

Require Export
        Syntax.Input
        Syntax.Regex
        Syntax.StarLemmas
        Tactics.Tactics
        Utils.Notations
        Utils.StringUtils.

Inductive tree : Set :=
| TUnit  : tree
| TChr   : ascii -> tree
| TCat   : tree -> tree -> tree 
| TLeft  : tree -> tree
| TRight : tree -> tree 
| TNil   : tree
| TCons  : tree -> tree -> tree.

Reserved Notation "t ':>' e" (at level 60, no associativity).

Inductive is_tree_of : tree -> regex -> Prop :=
| ITUnit : TUnit :> #1
| ITChr  : forall c, (TChr c) :> ($ c)
| ITCat  : forall e t e' t',
    t :> e   ->
    t' :> e' ->
    (TCat t t') :> (e @ e')
| ITLeft : forall e t e',
    t :> e ->
    (TLeft t) :> (e :+: e')
| ITRight : forall e e' t',
    t' :> e' ->
    (TRight t') :> (e :+: e')
| ITNil : forall e, TNil :> (Star e)
| ITCons : forall e t ts,
    t :> e ->
    ts :> (Star e) ->
    (TCons t ts) :> (Star e)
where "t ':>' e" := (is_tree_of t e).

Hint Constructors is_tree_of.

Ltac is_tree_of_inverts :=
  match goal with
  | [H : TUnit :> _ |- _] => inverts* H
  | [H : (TChr _) :> _ |- _] => inverts* H
  | [H : (TCat _ _) :> _ |- _] => inverts* H
  | [H : (TLeft _) :> _ |- _] => inverts* H
  | [H : (TRight _) :> _ |- _] => inverts* H
  | [H : TNil :> _ |- _] => inverts* H
  | [H : (TCons _ _) :> _ |- _] => inverts* H
  end.

Definition tc : forall t e, {t :> e} + {~ t :> e}.
  refine (fix tc t e : {t :> e} + {~ t :> e} :=
            match t as t', e as e'
                  return t = t' -> e = e' -> {t' :> e'} + {~ t' :> e'} with
            | TUnit, #1 => fun Heq Heq' => Yes
            | TChr c, $ c' => fun Heq Heq' =>
                if ascii_dec c c' then Yes else No
            | TCat t t', e1 @ e2 => fun Heq Heq' =>
                match tc t e1, tc t' e2 with
                | Yes, Yes => Yes
                | No , Yes => No
                | Yes, No  => No
                | No , No  => No
                end
            | TLeft t, e1 :+: e2 => fun Heq Heq' =>
                if tc t e1 then Yes else No
            | TRight t', e1 :+: e2 => fun Heq Heq' =>
                if tc t' e2 then Yes else No
            | TNil, (Star e) => fun Heq Heq' => Yes
            | TCons t ts, (Star e) => fun Heq Heq' => 
              match tc t e, tc ts (Star e) with
              | Yes, Yes => Yes
              | No , Yes => No
              | Yes, No  => No
              | No , No  => No
              end
            | _    , _  => fun _ _      => No
            end (eq_refl t) (eq_refl e)) ; clear tc ; crush ;
    repeat is_tree_of_inverts.
Defined.


Fixpoint flatten (t : tree) : string :=
  match t with
  | TUnit => ""
  | TChr c => String c ""
  | TCat t1 t2 => flatten t1 ++ flatten t2
  | TLeft t => flatten t
  | TRight t => flatten t
  | TNil => ""
  | TCons t ts => flatten t ++ flatten ts
  end.

Theorem flatten_correct
  : forall t e, t :> e -> (flatten t) <<- e.
Proof.
  induction t ; intros e Ht ; inverts* Ht ; simpl in * ; eauto.
  +
    destruct (flatten t1) eqn : Ht1 ; crush.
    rewrite string_app_rewind ; 
    eapply InStarRight with (s := String a s) ; crush.
Qed.

Definition flatten_complete_type :=
  fun p => get_string p <<- (get_regex p) ->
         exists t, t :> (get_regex p) /\ flatten t = (get_string p).


Lemma flatten_complete_F
  : forall p, (forall p', input_lt p' p -> flatten_complete_type p') ->
         flatten_complete_type p.
Proof.
  intros p IH ; unfold flatten_complete_type in * ; intros H.
  destruct p as [e s] ; simpl in * ; destruct e ; try solve [ inverts* H ].
  -
    inverts* H.
    +
      assert (Hlt1 : input_lt (mk_input e1 s0) (mk_input (e1 @ e2) (s0 ++ s')))
        by auto.
      assert (Hlt2 : input_lt (mk_input e2 s') (mk_input (e1 @ e2) (s0 ++ s')))
        by auto.
      assert (He1 : exists t, t :> (get_regex (mk_input e1 s0)) /\
                         flatten t = get_string (mk_input e1 s0))
        by (eapply IH ; eauto).
      assert (He2 : exists t, t :> (get_regex (mk_input e2 s')) /\
                         flatten t = get_string (mk_input e2 s'))
        by (eapply IH ; eauto).
      destruct He1 as [t1 [Ht1 Hf1]].
      destruct He2 as [t2 [Ht2 Hf2]].
      exists (TCat t1 t2) ; crush.
  -
    inverts* H.
    +
      assert (Hlt : input_lt (mk_input e1 s) (mk_input (e1 :+: e2) s)) by auto.
      assert (He1 : exists t, t :> get_regex (mk_input e1 s) /\
                         flatten t = get_string (mk_input e1 s))
        by (eapply IH ; eauto).
      destruct He1 as [t [Ht Hf]].
      exists (TLeft t) ; crush.
    +
      assert (Hlt : input_lt (mk_input e2 s) (mk_input (e1 :+: e2) s)) by auto.
      assert (He2 : exists t, t :> get_regex (mk_input e2 s) /\
                         flatten t = get_string (mk_input e2 s))
        by (eapply IH ; eauto).
      destruct He2 as [t [Ht Hf]].
      exists (TRight t) ; crush.
  -
    inverts* H.
    destruct s0 ; crush.
    assert (Hlte : input_lt (mk_input e (String a s0))
                            (mk_input (e ^*) (String a s0 ++ s'))) by auto.
    assert (He : exists t : tree,
               t :> get_regex (mk_input e (String a s0)) /\
               flatten t = get_string (mk_input e (String a s0)))
       by (eapply IH ; eauto).
    assert (Hes : exists t, t :> get_regex (mk_input (e ^*) s') /\
                   flatten t = get_string (mk_input (e ^*) s'))
       by (apply IH ; eauto ; try apply star_input_lt_2).
    destruct He as [t [Ht Hf]].
    destruct Hes as [ts [Hts Hfs]].
    exists (TCons t ts) ; crush.
Qed.

Lemma flatten_complete1
  : forall p, get_string p <<- (get_regex p) ->
         exists t, t :> (get_regex p) /\ flatten t = (get_string p).
Proof.
  intros p.
  apply (well_founded_ind
           wf_input_lt
           flatten_complete_type).
  apply flatten_complete_F.
Qed.

Theorem flatten_complete
  : forall e s, s <<- e -> exists t, t :> e /\ flatten t = s.
Proof.
  intros e s.
  change e with (get_regex (mk_input e s)).
  change s with (get_string (mk_input e s)).
  eapply flatten_complete1.
Qed.