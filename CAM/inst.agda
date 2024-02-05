module CAM.inst where

open import Data.Nat using (ℕ)
open import Data.List

data Inst : Set where
  UNIT : Inst
  NAT : ℕ → Inst
  SKIP : Inst
  CAR : Inst
  CDR : Inst
  APP : Inst
  CUR : List Inst → Inst
  PUSH : Inst
  SWAP : Inst
  CONS : Inst
--- COPRODUCT ---
  INL : Inst
  INR : Inst
  CASE : List Inst → List Inst → Inst
