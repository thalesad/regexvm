From Coq Require Extraction.

Extraction Language Haskell.


(** built-in extraction configs for Haskell *)

Require Import
        Coq.extraction.ExtrHaskellBasic
        Coq.extraction.ExtrHaskellNatInt
        Coq.extraction.ExtrHaskellString.

(** More extraction configurations *)

Require Import
        Utils.Notations
        Semantics.Bigstep
        String.

Extraction "./Tool/regex-vm/src/Semantics.hs" interp.