module list.value where

open import Data.List using (List)

open import list.catComb public
open import list.inst
open import context (Type)

infixl 5 _,_
infixr 6 _⦂_

data MachineValue : Set where
  ⟨⟩ : MachineValue
  _,_ : MachineValue → MachineValue → MachineValue
  cur : List Inst → MachineValue → MachineValue
--- LIST OBJECT ---
  [] : MachineValue
  _⦂_ : MachineValue → MachineValue → MachineValue


data CatCombValue : Type → Set where
  ⟨⟩ : CatCombValue unit
  _,_ : ∀ {A B} → CatCombValue A → CatCombValue B → CatCombValue (A × B)
  cur : ∀ {A B C} → CatComb (A × B) C → CatCombValue A → CatCombValue (B ⇒ C)
--- LIST OBJECT ---
  [] : ∀ {A} → CatCombValue (list A)
  _⦂_ : ∀ {A} → CatCombValue A → CatCombValue (list A) → CatCombValue (list A)

data ValueOfContext : Context → Set where
  empty : ValueOfContext ∅
  cons : ∀ {Γ A} → ValueOfContext Γ → CatCombValue A → ValueOfContext (Γ , A)
