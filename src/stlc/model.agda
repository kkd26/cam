module stlc.model where

open import stlc.type public
open import context (Type) public
open import stlc.term using (_⊢_)

record CCModel (_⊢_ : Context → Type → Set) : Set where
  field
    t    : ∀ {Γ} → Γ ⊢ unit
    pair : ∀ {Γ A B} → Γ ⊢ A → Γ ⊢ B → Γ ⊢ (A × B)
    fst  : ∀ {Γ A B} → Γ ⊢ (A × B) → Γ ⊢ A
    snd  : ∀ {Γ A B} → Γ ⊢ (A × B) → Γ ⊢ B

record CCCModel (_⊢_ : Context → Type → Set) : Set where
  field
    CC : CCModel _⊢_
    var  : ∀ {Γ A} → Γ ∋ A → Γ ⊢ A
    lam  : ∀ {Γ A B} → (Γ , A) ⊢ B → Γ ⊢ (A ⇒ B)
    app  : ∀ {Γ A B} → Γ ⊢ (A ⇒ B) → Γ ⊢ A → Γ ⊢ B
  open CCModel public


x : CCCModel _⊢_
x = record
    { CC = record { t = _⊢_.⟨⟩ ; pair = _⊢_._,_ ; fst = _⊢_.fst ; snd = _⊢_.snd }
    ; var = _⊢_.`_
    ; lam = _⊢_.ƛ_
    ; app = _⊢_._·_
    }
