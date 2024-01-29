module CAM.config where

open import Data.List using (List)

open import CAM.inst public
open import CAM.value public

record Config : Set where
  constructor ⟨_∣_∣_⟩
  field
    inst : List Inst
    env : Value
    stack : List Value
