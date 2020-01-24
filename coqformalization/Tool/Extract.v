(** built-in extraction configs for Haskell *)

Require Import
        Coq.extraction.ExtrHaskellBasic
        Coq.extraction.ExtrHaskellNatInt
        Coq.extraction.ExtrHaskellString.

Extraction Language Haskell.

(** More extraction configurations *)

Require Import
        Utils.Notations
        Semantics.Greedy
        String.

Extraction "./Tool/regex-vm/src/Semantics.hs" interp.
