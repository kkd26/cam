module CAM.stlc.catComb where

open import Data.Nat using (ℕ)

open import CAM.stlc.type public

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
--- COPRODUCT ---
  [_,_] : ∀ {A B C D} → CatComb (A × B) D → CatComb (A × C) D → CatComb (A × (B + C)) D
  i1 : ∀ {A B} → CatComb A (A + B)
  i2 : ∀ {A B} → CatComb B (A + B)
