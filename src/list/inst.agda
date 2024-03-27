module list.inst where

open import Data.List

data Inst : Set where
  UNIT : Inst
  SKIP : Inst
  CAR : Inst
  CDR : Inst
  APP : Inst
  CUR : List Inst → Inst
  PUSH : Inst
  SWAP : Inst
  CONS : Inst
--- LIST OBJECT ---
  NIL : Inst
  C : Inst
  IT : List Inst → List Inst → Inst
