module CAM.value where

open import Data.Nat using (ℕ)
open import Data.List using (List)

open import CAM.inst using (Inst)

infixl 5 _,_
infix  9 `nat_

data Value : Set where
  `nat_ : ℕ → Value
  ⟨⟩ : Value
  _,_ : Value → Value → Value
  cur : List Inst → Value → Value
