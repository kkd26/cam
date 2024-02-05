module CAM.value where

open import Data.Nat using (ℕ)
open import Data.List using (List)

open import CAM.inst using (Inst)
open import CAM.catComb using (CatComb)
open import CAM.term

infixl 5 _,_
infix  9 `nat_

data MachineValue : Set where
  ⟨⟩ : MachineValue
  `nat_ : ℕ → MachineValue
  _,_ : MachineValue → MachineValue → MachineValue
  cur : List Inst → MachineValue → MachineValue

data CatCombValue : Type → Set where
  ⟨⟩ : CatCombValue unit
  `nat_ : ℕ → CatCombValue nat
  _,_ : ∀ {A B} → CatCombValue A → CatCombValue B → CatCombValue (A × B)
  cur : ∀ {A B C} → CatComb ((A × B) ⇒ C) → CatCombValue A → CatCombValue (B ⇒ C)
