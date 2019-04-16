Set Implicit Arguments.

Require Import
        Morphisms
        Utils.StringUtils.

(** Definition of regular expression syntax *)

Inductive regex : Set :=
| Empty  : regex
| Eps    : regex
| Chr    : ascii -> regex
| Cat    : regex -> regex -> regex
| Choice : regex -> regex -> regex
| Star   : regex -> regex.

Notation "'#0'" := Empty.
Notation "'#1'" := Eps.
Notation "'$' c" := (Chr c)(at level 40).
Notation "e '@' e1" := (Cat e e1)(at level 15, left associativity).
Notation "e ':+:' e1" := (Choice e e1)(at level 20, left associativity).
Notation "e '^*'" := (Star e)(at level 40).

(** Semantics of regular expressions *)

Reserved Notation "s '<<-' e" (at level 40).

Inductive in_regex : string -> regex -> Prop :=
| InEps
  : "" <<- #1
| InChr
  : forall c
  , String c "" <<- ($ c)
| InCat
  :  forall e e' s s' s1 
  ,  s <<- e
  -> s' <<- e'
  -> s1 = s ++ s' 
  -> s1 <<- (e @ e')
| InLeft
  :  forall s e e'
  ,  s <<- e
  -> s <<- (e :+: e')
| InRight
  :  forall s' e e'
  ,  s' <<- e'
  -> s' <<- (e :+: e')
| InStarLeft
  : forall e
  , EmptyString <<- (e ^*)
| InStarRight              
  : forall s s' e s1 
  , s <> ""  
  -> s <<- e
  -> s' <<- (e ^*)
  -> s1 = s ++ s'
  -> s1 <<- (e ^*)                          
where "s '<<-' e" := (in_regex s e).

Hint Constructors in_regex.

Definition regex_equiv (e e' : regex) : Prop :=
  forall s, s <<- e <-> s <<- e'.

Notation "e '===' e1" := (regex_equiv e e1)(at level 70, no associativity).

(** setoid rewriting stuff *)

Instance regex_equiv_PreOrder : PreOrder regex_equiv.
Proof.
  constructor ; hnf ; unfold regex_equiv.
  -
    crush.
  -
    intros x y z H1 H2 s ; splits ; crush.
    destruct (H1 s) as [H11 H12] ; crush.
    destruct (H2 s) as [H21 H22] ; crush.
Qed.

Instance regex_equiv_Equivalence : Equivalence regex_equiv.
Proof.
  constructor ; hnf ; firstorder.
Qed.

Instance regex_equiv_in_regex s : Proper (regex_equiv ==> iff) (in_regex s).
Proof.
  intros e e' H ; split ; intros H1.
  -
    destruct (H s) as [Hl Hr] ; eauto.
  -
    destruct (H s) as [Hl Hr] ; eauto. 
Qed.

Instance regex_equiv_Cat : Proper (regex_equiv ==> regex_equiv ==> regex_equiv) Cat.
Proof.
  intros e e' H ; hnf ; intros x y H1 s ; splits ; intros H2.
  -
    inverts H2.
    destruct (H s0) as [He He'].
    specialize (He H4). clear He'.
    destruct (H1 s') as [Hx Hy].
    specialize (Hx H6). eauto.
  -
    inverts H2.
    destruct (H s0) as [He He'].
    specialize (He' H4). clear He.
    destruct (H1 s') as [Hx Hy].
    specialize (Hy H6). eauto.
Qed.

Instance regex_equiv_Choice
  : Proper (regex_equiv ==> regex_equiv ==> regex_equiv) Choice.
Proof.
  intros e e' H ; hnf ; intros x y H1 s ; splits ; intros H2.
  -
    inverts H2.
    + 
      rewrite H in H4 ; eauto.
    +
      rewrite H1 in H4 ; eauto.
  - 
    inverts H2.
    + 
      rewrite <- H in H4 ; eauto.
    +
      rewrite <- H1 in H4 ; eauto.
Qed.

Instance regex_equiv_Star : Proper (regex_equiv ==> regex_equiv) Star.
Proof.
  intros e e' H s ; splits ; intros H1.
  - 
    remember (e ^*) as x.
    induction H1 ; try congruence ; eauto.
    +
      inverts Heqx.
      apply InStarRight with (s := s)(s' := s') ; auto.
      rewrite <- H ; auto.
  -
    remember (e' ^*) as x.
    induction H1 ; try congruence ; eauto.
    +
      inverts Heqx.
      apply InStarRight with (s := s)(s' := s') ; auto.
      rewrite H ; auto.
Qed.


