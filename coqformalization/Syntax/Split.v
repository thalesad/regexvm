Set Implicit Arguments.

Require Import
        Syntax.Regex
        String
        Tactics.Tactics.


Section SPLIT.

  Variable s : string.
  Variables e1 e2 : regex.

  Lemma split'
    : forall n, n <= length s ->
           (exists s1 s2, length s1 <= n /\ s1 ++ s2 = s /\ s1 <<- e1 /\ s2 <<- e2) \/
           (forall s1 s2, length s1 <= n -> s1 ++ s2 = s -> not_in_regex s1 e1 \/ not_in_regex s2 e2)