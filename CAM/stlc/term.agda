module CAM.stlc.term where

open import Data.Nat using (ℕ)

open import CAM.stlc.type public

open import CAM.context (Type) public

ctxToType : Context → Type
ctxToType ∅ = unit
ctxToType (Γ , A) = ctxToType Γ × A

infix  4 _⊢_
infix  5 ƛ_
infixl 7 _·_
infix  9 `_
infix  9 `nat_

data _⊢_ : Context → Type → Set where
  ⟨⟩ : ∀ {Γ} → Γ ⊢ unit
  `_ : ∀ {Γ A} → Γ ∋ A → Γ ⊢ A
--- PRODUCT ---
  _,_ : ∀ {Γ A B} → Γ ⊢ A → Γ ⊢ B → Γ ⊢ A × B
  fst : ∀ {Γ A B} → Γ ⊢ A × B → Γ ⊢ A
  snd : ∀ {Γ A B} → Γ ⊢ A × B → Γ ⊢ B
--- EXPONENTIAL ---
  ƛ_  : ∀ {Γ A B} → Γ , A ⊢ B → Γ ⊢ A ⇒ B
  _·_ : ∀ {Γ A B} → Γ ⊢ A ⇒ B → Γ ⊢ A → Γ ⊢ B
--- NATURAL NUMBERS ---
  `nat_ : ∀ {Γ} → ℕ → Γ ⊢ nat
--- COPRODUCT ---
  inl_ : ∀ {Γ A B} → Γ ⊢ A → Γ ⊢ A + B
  inr_ : ∀ {Γ A B} → Γ ⊢ B → Γ ⊢ A + B
  case_inl_inr_ : ∀ {Γ A B C} → Γ ⊢ A + B → Γ , A ⊢ C → Γ , B ⊢ C → Γ ⊢ C


module Utils where

  open import Data.Nat using (zero; suc; _<_; _≤?_; z≤n; s≤s)
  open import Relation.Nullary.Decidable using (True; toWitness)

  infix 9 #_

  ctxLen : Context → ℕ
  ctxLen ∅        =  zero
  ctxLen (Γ , _)  =  suc (ctxLen Γ)

  ctxLookup : {Γ : Context} → {n : ℕ} → (p : n < ctxLen Γ) → Type
  ctxLookup {(_ , A)} {zero}    (s≤s z≤n)  =  A
  ctxLookup {(Γ , _)} {(suc _)} (s≤s p)    =  ctxLookup p

  count : ∀ {Γ} → {n : ℕ} → (p : n < ctxLen Γ) → Γ ∋ ctxLookup p
  count {_ , _} {zero}    (s≤s z≤n)  =  Z
  count {Γ , _} {(suc _)} (s≤s p)    =  S (count p)

  #_ : ∀ {Γ}
    → (n : ℕ)
    → {n∈Γ : True (suc n ≤? ctxLen Γ)}
      --------------------------------
    → Γ ⊢ ctxLookup (toWitness n∈Γ)
  #_ x {n∈Γ}  = ` count (toWitness n∈Γ)
