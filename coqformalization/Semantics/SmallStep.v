Set Implicit Arguments.

Require Import
        Arith_base
        Syntax.BitCodes
        Syntax.Context
        List
        Utils.Notations
        Relations.Relation_Operators
        Syntax.Regex
        Tactics.Tactics
        Utils.StringUtils.

Import ListNotations.

Inductive dir : Set :=
| B : dir | E : dir. 

Inductive conf : Set :=
  MkConf : dir -> regex -> ctx -> list bit -> string -> conf.

Notation "[[ d , e , c , b , s ]]" := (MkConf d e c b s)(at level 60).

Definition get_code (c : conf) : list bit :=
  match c with 
  | [[ _ , _ , _ , bs , _ ]] => bs
  end.

Definition finishing (c : conf) : bool :=
  match c with
  | [[ E , _ , _ , _ , _ ]] => true
  | _ => false
  end.

Definition is_init (c : conf) : bool :=
  match c with
  | [[ B , _ , [] , _ , _ ]] => true
  | _ => false  
  end.

(** small step semantics *)

Reserved Notation "c '==*>' c1" (at level 40). 

Inductive step : conf -> conf -> Prop :=
| SEps : forall c b s,
    [[ B , #1 , c , b , s ]] ==*> [[ E , #1 , c , b , s ]]
| SChar : forall c b s a,
    [[ B , $ a, c , b, (String a s) ]] ==*> [[ E, $ a, c, b, s ]]
| SLeftB : forall c b s e e' c' b',
    c' = LeftChoiceHole e' :: c ->
    b' = O :: b -> 
    [[ B , e :+: e', c, b, s ]] ==*> [[ B , e , c' , b', s ]]
| SRightB : forall c b s e e' c' b',
    c' = RightChoiceHole e :: c ->
    b' = I :: b -> 
    [[ B , e :+: e', c, b, s ]] ==*> [[ B , e' , c' , b', s ]]
| SCatB : forall c b s e e' c',
    c' = LeftCatHole e' :: c ->
    [[ B , e @ e' , c , b, s ]] ==*> [[ B, e , c' , b, s ]]
| SStar1 : forall c b s e c' b',
    c' = StarHole :: c ->
    b' = O :: b ->
    [[ B , e ^*, c , b, s ]] ==*> [[ B , e , c' , b' , s ]]
| SStar2 : forall c b s e b',
    b' = I :: b ->
    [[ B , e ^*, c , b, s ]] ==*> [[ E , e ^*, c, b', s ]]
| SCatEL : forall e e' s c b c' c1,
    c' = LeftCatHole e' :: c ->
    c1 = RightCatHole e :: c -> 
    [[ E , e , c', b, s ]] ==*> [[ B, e', c1, b, s ]]
| SCatER : forall e e' s c b c',
    c' = RightCatHole e :: c ->
    [[ E , e' , c', b, s ]] ==*> [[ E , e @ e', c, b, s ]]
| SLeftE : forall e e' c s b c' b',
    c' = LeftChoiceHole e' :: c ->
    b' = O :: b ->
    [[ E , e , c' , b , s ]] ==*> [[ E , e :+: e', c, b', s ]]
| SRightE : forall e e' c s b c' b',
    c' = RightChoiceHole e :: c ->
    b' = I :: b ->
    [[ E , e' , c' , b , s ]] ==*> [[ E , e :+: e', c, b', s ]]
| SStarE1 : forall e c s b c' b',
    c' = StarHole :: c ->
    b' = O :: b -> 
    [[ E , e , c', b, s ]] ==*> [[ B, e, c', b' , s ]]
| SStarE2 : forall e c s b c' b',
    c' = StarHole :: c ->
    b' = I :: b ->
    [[ E, e , c' , b , s ]] ==*> [[ E, e ^*, c , b', s]]
where "c '==*>' c1" := (step c c1).

Hint Constructors step.

Definition next (c : conf) : {cs : list conf | forall c', In c' cs -> c ==*> c'}.
  refine (match c with
          | [[ B, #1 , co , b, s ]] =>
            exist _ ([[ E, #1, co, b, s ]] :: nil) _
          | [[ B, $ a, co, b , (String a' s) ]] =>
            if ascii_dec a a' then 
              exist _ ([[ E , $ a, co, b, s ]] :: nil) _
            else exist _ (@nil conf) _
          | [[ B , e :+: e', c , b, s ]] =>
            exist _ ( [[ B, e , LeftChoiceHole e' :: c, O :: b, s ]] ::
                      [[ B , e' , RightChoiceHole e :: c, I :: b, s ]] :: nil) _
          | [[ B, e @ e', c , b, s ]] => 
            exist _ ( [[ B, e, LeftCatHole e' :: c, b, s ]] :: nil ) _

          | [[ B, e ^*, c, b, s ]] =>
            exist _ ( [[ B, e, StarHole :: c, O :: b, s ]] ::
                      [[ E, e ^*, c, I :: b, s ]] :: nil) _
          | [[ E, e, LeftCatHole e' :: c, b, s ]] =>
            exist _ ([[ B , e' , RightCatHole e :: c , b , s]] :: nil) _
          | [[ E, e', RightCatHole e :: c, b, s ]] =>
            exist _ ( [[ E , e @ e', c, b, s ]] :: nil ) _
          | [[ E, e, LeftChoiceHole e' :: c, b, s ]] =>
            exist _ ([[ E, e :+: e', c, O :: b, s ]] :: nil) _
          | [[ E, e', RightChoiceHole e :: c, b, s ]] =>
            exist _ ([[ E, e :+: e', c, I :: b, s ]] :: nil) _
          | [[ E, e , StarHole :: c, b, s ]] =>
            exist _ ([[ B, e, StarHole :: c, O :: b, s ]] ::
                     [[ E, e ^*, c, I :: b, s ]] :: nil) _
          | _                      => exist _ (@nil conf) _
          end) ; crush ; eauto.
Defined.

Definition multi_steps := @clos_refl_trans_1n conf step.

Notation "c '==*>*' c1" := (multi_steps c c1)(at level 50).

Lemma step_multi : forall c c', c ==*> c' -> c ==*>* c'.
Proof.
  intros c c' H ; unfolds ; repeat (econstructor ; eauto).
Qed.

Hint Resolve step_multi.

Definition nexts_type cs :=
  {cs' | forall c', In c' cs' -> exists c, In c cs /\ c ==*> c'} + {cs = []}.

Definition nexts : forall cs, nexts_type cs.
  unfold nexts_type.
  refine (fix nexts cs : {cs' | forall c', In c' cs' -> exists c, In c cs /\ c ==*> c'} +
                         {cs = []} :=
            match cs as cs1
                  return cs = cs1 ->
                         {cs' | forall c', In c' cs' -> exists c, In c cs /\ c ==*> c'} +
                         {cs = []} with
            | [] => fun _ => !!
            | c' :: cs' => fun _ =>
               match next c', nexts cs' with
               | (exist _ cs1 _), [|| cs2 ||] => [|| (cs1 ++ cs2)%list ||]
               | (exist _ cs1 _), !!        => [|| cs1 ||]
               end
            end (eq_refl cs)) ; clear nexts ; crush.
  +
    lets K : in_app_or H ; destruct K.
    lets J : s H0 ; exists c' ; splits*.
    lets J : e0 H0 ; destruct J. destruct H1.
    exists x ; splits*.
  +
    lets K : s H.
    exists* c'.
Defined.

Definition steps : forall (cs : list conf)(n : nat), 
    {css | forall c', In c' css -> exists c, In c cs /\ c ==*>* c'} + {cs = []}.
  refine (fix steps cs n : {css | forall c', In c' css -> exists c, In c cs /\ c ==*>* c'} +
                        {cs = []} :=
            match cs as cs'
                  return cs = cs' ->
                         {css | forall c', In c' css -> exists c, In c cs /\ c ==*>* c'} +
                         {cs = []} with
            | [] => fun _ => !!
            | c :: cs => fun _ =>
                match nexts (c :: cs), n with
                | !! , _ => !!
                | [|| cs1 ||], 0 => [|| cs1 ||]
                | [|| cs1 ||] , S n' =>
                  match steps cs1 n' with
                  | !! => [|| cs1 ||]
                  | [|| cs2 ||] => [|| (cs1 ++ cs2)%list ||]
                  end 
                end
            end (eq_refl cs)) ; clear steps ; crush.
  +
    lets J : e0 H.
    destruct J as [x Hx]. destruct Hx as [Hk Hs]. destruct Hk ; substs*.
  +
    lets K : in_app_or H. destruct K.
    lets J : e0 H0.
    destruct J as [c1 Hx]. destruct Hx. destruct H1 ; exists c1 ; crush.
    lets J : e1 H0.
    destruct J as [c1 Hx]. destruct Hx.
    lets L : e0 H1.
    destruct L as [y Hy]. destruct Hy. destruct H3 ; substs.
    exists y ; splits ; try left*.
    econstructor ; eauto.
    exists y ; splits ; try right ; auto.
    econstructor ; eauto.
Defined.
