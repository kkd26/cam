module CAM.value where

open import Data.Nat using (ℕ)
open import Data.List using (List)

open import CAM.inst using (Inst)
open import CAM.catComb using (CatComb)

infixl 5 _,_
infix  9 `nat_

data MachineValue : Set where
  ⟨⟩ : MachineValue
  `nat_ : ℕ → MachineValue
  _,_ : MachineValue → MachineValue → MachineValue
  cur : List Inst → MachineValue → MachineValue

data CatCombValue : Set where
  ⟨⟩ : CatCombValue
  `nat_ : ℕ → CatCombValue
  _,_ : CatCombValue → CatCombValue → CatCombValue
  cur : CatComb → CatCombValue → CatCombValue
