module CAM.list.term where

open import CAM.list.type public
open import CAM.context (Type) public

ctxToType : Context → Type
ctxToType ∅ = unit
ctxToType (Γ , A) = ctxToType Γ × A

infix 4 _⊢_
infix  5 ƛ_
infixl 7 _·_
infix 9 `_
infixr 6 _⦂_

data _⊢_ : Context → Type → Set where
  ⟨⟩ : ∀ {Γ} → Γ ⊢ unit
  `_ : ∀ {Γ A} → Γ ∋ A → Γ ⊢ A
--- PRODUCT ---
  _,_ : ∀ {Γ A B} → Γ ⊢ A → Γ ⊢ B → Γ ⊢ A × B
  fst : ∀ {Γ A B} → Γ ⊢ A × B → Γ ⊢ A
  snd : ∀ {Γ A B} → Γ ⊢ A × B → Γ ⊢ B
--- EXPONENTIAL ---
  ƛ_ : ∀ {Γ A B} → Γ , A ⊢ B → Γ ⊢ A ⇒ B
  _·_ : ∀ {Γ A B} → Γ ⊢ A ⇒ B → Γ ⊢ A → Γ ⊢ B
--- LIST OBJECT ---
  [] : ∀ {Γ A} → Γ ⊢ list A
  _⦂_ : ∀ {Γ A} → Γ ⊢ A → Γ ⊢ list A → Γ ⊢ list A
  it : ∀ {Γ A X} → Γ ⊢ X → Γ , (A × X) ⊢ X → Γ ⊢ list A → Γ ⊢ X
