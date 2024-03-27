module config where

open import Data.List using (List)

record MakeConfig (Inst : Set) (Value : Set) : Set where
  constructor ⟨_∣_∣_⟩
  field
    inst : List Inst
    env : Value
    stack : List Value
