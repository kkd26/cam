module untyped.term where

open import untyped.type public
open import untyped.context public

infix 9 `_
infixl 8 _·_
infix 7 ƛ_

data UntypedTerm : Context → Set where
  `_ : ∀ {n Γ} → Γ ∋ n → UntypedTerm Γ
  _·_ : ∀ {Γ} → UntypedTerm Γ → UntypedTerm Γ → UntypedTerm Γ
  ƛ_ : ∀ {Γ} → UntypedTerm (suc Γ) → UntypedTerm Γ

infix 4 _⊢_

data _⊢_ : Context → Type → Set where
  `_ : ∀ {n Γ} → Γ ∋ n → Γ ⊢ U
  j : ∀ {Γ} → Γ ⊢ U → Γ ⊢ U → Γ ⊢ U
  i : ∀ {Γ} → Γ ⊢ U ⇒ U → Γ ⊢ U
  ƛ_ : ∀ {Γ} → suc Γ ⊢ U → Γ ⊢ U ⇒ U

_* : ∀ {Γ} → UntypedTerm Γ → Γ ⊢ U
(` x) * = ` x
(x₁ · x₂) * = j (x₁ *) (x₂ *)
(ƛ x) * = i (ƛ (x *))
