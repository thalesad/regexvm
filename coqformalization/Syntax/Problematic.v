Set Implicit Arguments.

Require Export
        Syntax.StarLemmas.

(** nullability test *)

Definition null : forall e, {"" <<- e} + {~ "" <<- e}.
  refine (fix null e : {"" <<- e} + {~ "" <<- e} :=
            match e as e' return e = e' -> {"" <<- e'} + {~ "" <<- e'} with
            | #0 => fun Heq => No
            | #1 => fun Heq => Yes
            | $ a => fun Heq => No
            | e1 @ e2 => fun Heq =>
               match null e1 , null e2 with
               | Yes , Yes  => Yes
               | Yes , No   => No
               | No  , Yes  => No
               | No  , No   => No
               end 
            | e1 :+: e2 => fun Heq =>
               match null e1 , null e2 with
               | Yes , Yes  => Yes
               | Yes , No   => Yes
               | No  , Yes  => Yes
               | No  , No   => No
               end
            | e1 ^* => fun Heq => Yes
            end (eq_refl e)) ; substs ; clear null ; crush ; eauto ; 
    repeat (match goal with
            | [H : _ <<- #0 |- _] => inverts* H
            | [H : "" <<- ($ _) |- _] => inverts* H
            | [H : "" <<- (_ @ _) |- _] => inverts* H
            | [H : "" = _ ++ _ |- _] =>
              apply empty_string_concat in H ; destruct* H ; crush
            | [H : "" <<- (_ :+: _) |- _] => inverts* H
            end).
Defined.

Inductive empty_regex : regex -> Prop :=
| Emp_Eps : empty_regex #1
| Emp_Cat : forall e e', empty_regex e ->
                    empty_regex e' ->
                    empty_regex (e @ e')
| Emp_Choice : forall e e', empty_regex e ->
                    empty_regex e' ->
                    empty_regex (e :+: e')
| Emp_Star : forall e, empty_regex e ->
                  empty_regex (e ^*).

Hint Constructors empty_regex.

Lemma empty_regex_sem : forall e, empty_regex e -> "" <<- e.
Proof.
  induction 1 ; crush ; eauto.
Qed.

Hint Resolve empty_regex_sem.

Theorem empty_regex_spec : forall e, empty_regex e -> e === #1.
Proof.
  induction e ; intros H ; inverts* H ; crush ;
    [ rewrite eps_cat    |
      rewrite eps_choice_eps |
      rewrite eps_star ] ; reflexivity.
Qed.

Definition empty : forall (e : regex), {empty_regex e} + {~ empty_regex e}.
  refine (fix empty e : {empty_regex e} + {~ empty_regex e} :=
            match e as e' return e = e' -> {empty_regex e} + {~ empty_regex e} with
            | #0 => fun Heq => No
            | #1 => fun Heq => Yes
            | $ a => fun Heq => No
            | e1 @ e2 => fun Heq =>
               match empty e1, empty e2 with
               | Yes , Yes => Yes
               | Yes , No  => No
               | No  , Yes => No
               | No  , No  => No
               end
            | e1 :+: e2 => fun Heq =>
               match empty e1, empty e2 with
               | Yes , Yes => Yes
               | Yes , No  => No
               | No  , Yes => No
               | No  , No  => No
               end
            | e1 ^* => fun Heq => 
              match empty e1 with
              | Yes => Yes
              | No  => No
              end
            end (eq_refl e)) ; clear empty ; substs ; eauto ; crush ;
            try (match goal with
                 | [H : empty_regex _ |- _] => inverts* H
                 end).
Defined.


(** problematic test *)


Inductive unproblematic : regex -> Prop :=
| UEmpty : unproblematic #0
| UEps   : unproblematic #1
| UChr   : forall c, unproblematic ($ c)
| UCat   : forall e e', unproblematic e ->
                   unproblematic e' ->
                   unproblematic (e @ e')
| UChoice : forall e e', unproblematic e ->
                    unproblematic e' ->
                    unproblematic (e :+: e')
| UStar : forall e, ~ ("" <<- e) -> unproblematic e -> unproblematic (Star e).

Hint Constructors unproblematic.
    
Definition problematic_dec : forall e, {unproblematic e} + {~ unproblematic e}.
  refine (fix prob_dec e : {unproblematic e} + {~ unproblematic e} :=
            match e as e'
                  return e = e' -> {unproblematic e'} + {~ unproblematic e'} with
            | #0 => fun _ => Yes
            | #1 => fun _ => Yes
            | $ _ => fun _ => Yes
            | e1 @ e2 => fun _ => 
                prob_dec e1 && prob_dec e2
            | e1 :+: e2 => fun _ => 
                prob_dec e1 && prob_dec e2
            | Star e1 => fun _ =>
                match null e1 with
                | Yes => No
                | No  =>
                  match prob_dec e1 with
                  | Yes => Yes
                  | No  => No
                  end
                end
            end (eq_refl e)) ; clear prob_dec ;
    eauto ; try solve [intro H ; inverts* H].
Defined.

Hint Rewrite eps_cat_left eps_cat_right eps_star star_involutive.

Definition unprob : forall (e : regex), {e' | e === e' /\ unproblematic e'}.
  refine (fix unprob e : {e' | e === e' /\ unproblematic e'} :=
            match e as e1 return e = e1 -> {e' | e1 === e' /\ unproblematic e'} with
            | #0 => fun Heq => [ #0 ]
            | #1 => fun Heq => [ #1 ]
            | $ a  => fun Heq => [ $ a ]
            | e2 @ e3 => fun Heq => 
              match unprob e2, unprob e3 with
              | [ e2' ] , [ e3' ] => [ e2' @ e3' ]
              end
            | e2 :+: e3 => fun Heq => 
              match unprob e2, unprob e3 with
              | [ e2' ] , [ e3' ] => [ e2' :+: e3' ]
              end
            | e2 ^* => fun Heq =>
                match null e2, empty e2 with
                | No  , _ =>
                  match unprob e2 with
                  | [ e2' ] => [ e2' ^* ]
                  end
                | _  , Yes => [ #1 ]
                | _  , _   =>
             match (fix unprob_rec
                       e2
                       (Hin : "" <<- e2)
                       (Hemp : ~ empty_regex e2)
                   : {e' | (e2 ^*) === (e' ^*) /\ ~ "" <<- e' /\ unproblematic e'} :=
                     match e2 as ex return e2 = ex ->
                       {e' | (e2 ^*) === (e' ^*) /\ ~ "" <<- e' /\
                                          unproblematic e'} with
                     | #0 => fun Heq => !
                     | #1 => fun Heq => !
                     | $ _ => fun Heq => !
                     | e1 @ e2 => fun Heq =>
                                   match null e1, empty e1, null e2, empty e2 with
                                   | _ , Yes, Yes , _ =>
                                     match unprob_rec e2 _ _ with
                                     | [ e2' ] => [ e2' ]
                                     end
                                   | _ , Yes , No , _ =>
                                     match unprob e2 with
                                     | [ e2' ] => [ e2' ]
                                     end
                                   | Yes , _ , _ , Yes =>
                                     match unprob_rec e1 _ _ with
                                     | [ e1' ] => [ e1' ]
                                     end
                                   | No , _ , _ , Yes =>
                                     match unprob e1 with
                                     | [ e1' ] => [ e1' ]
                                     end
                                   | No , _ , _ , No =>
                                     match unprob e1, unprob_rec e2 _ _ with
                                     | [ e1' ] , [ e2' ] => [ (e1' :+: e2') ]
                                     end
                                   | _ , No , No , _ =>
                                     match unprob_rec e1 _ _ , unprob e2 with
                                     | [ e1' ] , [ e2' ] => [ (e1' :+: e2') ]
                                     end 
                                   | _ , _ , _ , _ =>
                                     match unprob_rec e1 _ _ , unprob_rec e2 _ _ with
                                     | [ e1' ], [ e2' ] => [ (e1' :+: e2') ]
                                     end
                                   end
                     | e1 :+: e2 => fun Heq =>
                                     match null e1, empty e1, null e2, empty e2 with
                                     | _ , Yes, Yes , _ =>
                                       match unprob_rec e2 _ _ with
                                       | [ e2' ] => [ e2' ]
                                       end
                                     | _ , Yes , No , _ =>
                                       match unprob e2 with
                                       | [ e2' ] => [ e2' ]
                                       end
                                     | Yes , _ , _ , Yes =>
                                       match unprob_rec e1 _ _ with
                                       | [ e1' ] => [ e1' ]
                                       end
                                     | No , _ , _ , Yes =>
                                       match unprob e1 with
                                       | [ e1' ] => [ e1' ]
                                       end
                                     | No , _ , _ , No =>
                                       match unprob e1, unprob_rec e2 _ _ with
                                       | [ e1' ] , [ e2' ] => [ (e1' :+: e2') ]
                                       end
                                     | _ , No , No , _ =>
                                       match unprob_rec e1 _ _ , unprob e2 with
                                       | [ e1' ] , [ e2' ] => [ (e1' :+: e2') ]
                                       end 
                                     | _ , _ , _ , _ =>
                                       match unprob_rec e1 _ _ , unprob_rec e2 _ _ with
                                       | [ e1' ], [ e2' ] => [ (e1' :+: e2') ]
                                       end
                                     end
                     | e1 ^* => fun Heq => 
                                 match null e1 with
                                 | Yes => 
                                   match unprob_rec e1 _ _ with
                                   | [ e1' ] => [ e1' ]
                                   end
                                 | No =>
                                   match unprob e1 with
                                   | [ e1' ] => [ e1' ]
                                   end
                                 end
                     end (eq_refl e2)) e2 _ _ with
             | [  e2' ] => [ e2' ^* ]
             end
         end
      end (eq_refl e)) ; clear unprob ;
        try clear unprob_rec ; try split ; eauto ;
        try reflexivity. 
      crush.
      crush.
      crush.
      crush.
      apply empty_regex_spec in e0 ; crush.
      crush. inverts* Hin.
      crush.
      crush.
      inverts* Hin.
      crush.
      apply empty_regex_spec in e0 ; crush.
      apply empty_regex_spec in e0 ; crush.
      apply empty_regex_spec in e0 ; crush.
      crush. rewrite H in n0 ; crush.
      crush. apply empty_regex_spec in e0 ; crush.
      crush.

      crush.
      rewrite choice_star_cat_star ; eauto.
      rewrite choice_star_cat_star_star with (e1 := e1').
      rewrite <- H, <- H1.
      rewrite <- choice_star_cat_star_star.
      reflexivity.

      crush.
      crush. 
      inverts* H2.
      crush.
      crush.
      crush.
      inverts* Hin.
      apply empty_string_concat in H9 ; crush.
      crush.
      inverts* Hin.
      apply empty_string_concat in H10 ; crush.
      crush.
      crush.
      crush.
      crush.
      crush.
      inverts* Hin.
      apply empty_string_concat in H6 ; crush.
      crush.
      rewrite H in n0 ; crush.
      crush.
      inverts* Hin.
      apply empty_string_concat in H9 ; crush.
      crush.
      inverts* Hin.
      apply empty_string_concat in H10 ; crush.
      crush.
      crush. substs.
      inverts* Hin.
      apply empty_string_concat in H4 ; crush.
      crush.
      inverts* Hin.
      apply empty_string_concat in H9 ; crush.
      crush.
      inverts* Hin.
      apply empty_string_concat in H10 ; crush.
      crush.
      crush.
      inverts* Hin.
      apply empty_regex_spec in e0.
      rewrite e0.
      rewrite eps_choice_left_star. auto.
      apply empty_regex_spec in e0.
      rewrite e0.
      rewrite eps_choice_left_star. auto.
      crush. crush.
      rewrite <- H.
      apply empty_regex_spec in e0 ; rewrite e0.
      rewrite eps_choice_left_star ; auto.
      reflexivity. crush.
      rewrite <- H in H1. crush.
      crush.
      inverts* Hin.
      apply empty_regex_spec in e0 ; rewrite e0.
      rewrite eps_choice_right_star. auto.
      apply empty_regex_spec in e0 ; rewrite e0.
      rewrite eps_choice_right_star. auto.
      crush.
      crush.
      rewrite! choice_star_cat_star_star.
      rewrite H, H1 ; reflexivity.
      crush.
      inverts* H2.
      crush.
      crush.
      crush.
      rewrite H1 in Hin. inverts* Hin.
      rewrite choice_comm with (e1 := e1)(e2 := e2').
      rewrite choice_comm with (e1 := e1')(e2 := e2').
      rewrite! choice_star_cat_star_star.
      rewrite H. reflexivity.
      rewrite choice_comm with (e1 := e1)(e2 := e2').
      rewrite choice_comm with (e1 := e1')(e2 := e2').
      rewrite! choice_star_cat_star_star.
      rewrite H. reflexivity.
      crush.
      inverts* H0.
      rewrite <- H1 in H7 ; crush.
      crush.
      crush.
      crush.
      crush.
      crush.
      apply empty_regex_spec in e0 ; rewrite e0.
      rewrite eps_choice_right_star ; reflexivity.
      crush.
      rewrite <- H in H1 ; crush.
      crush. inverts* Hin. crush.
      rewrite choice_comm with (e1 := e1')(e2 := e2).
      rewrite choice_comm with (e1 := e1')(e2 := e2').
      rewrite! choice_star_cat_star_star.
      rewrite H1. reflexivity.
      crush.
      inverts* Hin ; crush.
      inverts* H2. rewrite <- H in H8 ; crush.
      crush.
      crush.
      substs.
      inverts* Hin.
      crush.
      crush.
      rewrite choice_comm with (e1 := e1')(e2 := e2).
      rewrite choice_comm with (e1 := e1')(e2 := e2').
      rewrite! choice_star_cat_star_star.
      rewrite H1. reflexivity.
      crush.
      inverts* Hin ; crush.
      crush.
      crush.
      crush.
      crush.
      crush.
      rewrite <- H in H1.
      crush.
      crush.
      crush.
      crush.
      crush.

      crush.
      rewrite H in n.
      crush.
Defined.