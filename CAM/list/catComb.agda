module CAM.list.catComb where

open import CAM.list.type public

data CatComb : Type → Type → Set where
  ! : ∀ {A} → CatComb A unit
  id : ∀ {A} → CatComb A A
  _∘_ : ∀ {A B C} → CatComb B C → CatComb A B → CatComb A C
  ⟨_,_⟩ : ∀ {C A B} → CatComb C A → CatComb C B → CatComb C (A × B)
  p₁ : ∀ {A B} → CatComb (A × B) A
  p₂ : ∀ {A B} → CatComb (A × B) B
  cur : ∀ {A B C} → CatComb (A × B) C → CatComb A (B ⇒ C)
  app : ∀ {A B} → CatComb (A ⇒ B × A) B
--- LIST OBJECT ---
  nil : ∀ {A} → CatComb unit (list A)
  cons : ∀ {A} → CatComb (A × list A) (list A)
  it : ∀ {A X P} → CatComb P X → CatComb (P × (A × X)) X → CatComb (list A × P) X
