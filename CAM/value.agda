module CAM.value where

open import Data.Nat using (ℕ)
open import Data.List using (List)

open import CAM.catComb using (Type; CatComb) public
open import CAM.inst using (Inst)

open Type

infixl 5 _,_
infix  9 `nat_
infix  9 L_
infix  9 R_

data MachineValue : Set where
  ⟨⟩ : MachineValue
  `nat_ : ℕ → MachineValue
  _,_ : MachineValue → MachineValue → MachineValue
  cur : List Inst → MachineValue → MachineValue
--- COPRODUCT ---
  L_ : MachineValue → MachineValue
  R_ : MachineValue → MachineValue

data CatCombValue : Type → Set where
  ⟨⟩ : CatCombValue unit
  `nat_ : ℕ → CatCombValue nat
  _,_ : ∀ {A B} → CatCombValue A → CatCombValue B → CatCombValue (A × B)
  cur : ∀ {A B C} → CatComb (A × B) C → CatCombValue A → CatCombValue (B ⇒ C)
--- COPRODUCT ---
  L_ : ∀ {A B} → CatCombValue A → CatCombValue (A + B)
  R_ : ∀ {A B} → CatCombValue B → CatCombValue (A + B)
