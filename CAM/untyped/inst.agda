module CAM.untyped.inst where

open import Data.List

data Inst : Set where
  FOLD : Inst
  UNFOLD : Inst
  CONS : Inst
  PUSH : Inst
  SWAP : Inst
  FST : Inst
  SND : Inst
  CUR : List Inst → Inst
  EV : Inst
