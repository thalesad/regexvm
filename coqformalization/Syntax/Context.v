Set Implicit Arguments.

Require Export
        Syntax.Regex.


(** contexts for REs *)

Inductive hole : Set :=
| LeftChoiceHole : regex -> hole
| RightChoiceHole : regex -> hole
| LeftCatHole : regex -> hole
| RightCatHole : regex -> hole
| StarHole : hole.

Definition ctx := list hole.