module untyped.catComb where

open import untyped.type

data CatComb : Type → Type → Set where
  fold : CatComb (U ⇒ U) U
  unfold : CatComb U (U ⇒ U)
  _∘_ : ∀ {A B C} → CatComb B C → CatComb A B → CatComb A C
  ⟨_,_⟩ : ∀ {A B C} → CatComb A B → CatComb A C → CatComb A (B × C)
  p₁ : ∀ {A B} → CatComb (A × B) A
  p₂ : ∀ {A B} → CatComb (A × B) B
  cur : ∀ {A B C} → CatComb (A × B) C → CatComb A (B ⇒ C)
  ev : ∀ {A B} → CatComb (A ⇒ B × A) B
