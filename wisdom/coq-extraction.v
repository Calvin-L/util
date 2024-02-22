(* Make the extracted code nice. *)
Require Import ExtrHaskellBasic.
Require Import ExtrHaskellNatInteger.
Require Import ExtrHaskellNatNum.
Require Import ExtrHaskellString.
Require Import ExtrHaskellZInteger.
Require Import ExtrHaskellZNum.

Extraction Language Haskell.
Extraction "OutputFile.hs"
  term1
  term2
  etc
  .
