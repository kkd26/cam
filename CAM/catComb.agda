module CAM.catComb where

open import Data.Nat using (ℕ)

open import CAM.term using (Type) public

open Type

infixl 5 _∘_

data CatComb : Type → Type → Set where
  ! : ∀ {A} → CatComb A unit
  nat : ∀ {A} → ℕ → CatComb A nat
  id : ∀ {A} → CatComb A A
  _∘_ : ∀ {A B C} → CatComb B C → CatComb A B → CatComb A C
  ⟨_,_⟩ : ∀ {C A B} → CatComb C A → CatComb C B → CatComb C (A × B)
  p₁ : ∀ {A B} → CatComb (A × B) A
  p₂ : ∀ {A B} → CatComb (A × B) B
  cur : ∀ {A B C} → CatComb (A × B) C → CatComb A (B ⇒ C)
  app : ∀ {A B} → CatComb (A ⇒ B × A) B
