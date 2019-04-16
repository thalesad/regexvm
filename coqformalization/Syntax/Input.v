Set Implicit Arguments.

Require Export
        Relation_Operators
        Syntax.Regex
        Utils.StringUtils.


Fixpoint size (e : regex) : nat :=
  match e with
  | #0 => 0
  | #1 => 1
  | $ _ => 2
  | e :+: e' => 1 + size e + size e'
  | e @ e' => 1 + size e + size e'
  | Star e => 1 + size e
  end.

Definition regex_lt e e' := size e < size e'.

Definition wf_regex_lt :=
  @wf_inverse_image regex
                    nat
                    lt
                    size
                    lt_wf.

Definition input := @sigT regex (fun _ => string).

Definition get_regex (p : input) : regex :=
  let (e,_) := p in e.

Definition get_string (p : input) : string :=
  let (_,s) := p in s.

Definition input_lt (p p' : input) :=
  @lexprod
    regex
    (fun _ => string)
    regex_lt
    (fun _ => string_lt)
    p p'.

Definition wf_input_lt : well_founded input_lt :=
  @wf_lexprod regex
              (fun _ => string)
              regex_lt
              (fun _ => string_lt)
              wf_regex_lt
              (fun _ => wf_string_lt).

Definition mk_input (e : regex)(s : string) : input := 
  @existT regex (fun _ => string) e ((fun _  : regex => s) e).

Lemma cat_input_lt_1
  : forall s s' e1 e2, input_lt (mk_input e1 s) (mk_input (e1 @ e2) (s ++ s')).
Proof.
  intros s s' e1 e2.
  apply left_lex ; unfold regex_lt ; crush.
Qed.

Lemma cat_input_lt_2
  : forall s s' e1 e2, input_lt (mk_input e2 s') (mk_input (e1 @ e2) (s ++ s')).
Proof.
  intros s s' e1 e2.
  apply left_lex ; unfold regex_lt ; crush.
Qed.

Lemma choice_input_lt_l
  : forall s e1 e2, input_lt (mk_input e1 s) (mk_input (e1 :+: e2) s).
Proof.
  intros s e1 e2 ; apply left_lex ; unfold regex_lt ; crush.
Qed.

Lemma choice_input_lt_r
  : forall s e1 e2, input_lt (mk_input e2 s) (mk_input (e1 :+: e2) s).
Proof.
  intros s e1 e2 ; apply left_lex ; unfold regex_lt ; crush.
Qed.

Lemma star_input_lt_1
  : forall s s' e, input_lt (mk_input e s) (mk_input (e ^*) (s ++ s')).
Proof.
  intros s s' e ; apply left_lex ; unfold regex_lt ; crush.
Qed.

Lemma star_input_lt_2
  : forall a s s' e, input_lt (mk_input (e ^*) s') (mk_input (e ^*) (String a (s ++ s'))).
Proof. 
  intros a s s' e ; apply right_lex ;
    unfold string_lt ; rewrite string_app_rewind, string_app_length ; crush.
Qed.

Hint Resolve
     cat_input_lt_1
     cat_input_lt_2
     choice_input_lt_l
     choice_input_lt_r
     star_input_lt_1
     star_input_lt_2.
