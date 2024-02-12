module CAM.term where

open import Data.Nat using (ℕ)

infixl 5 _×_
infixr 7 _⇒_

data Type : Set where
  unit : Type
  _×_ : Type → Type → Type
  _⇒_ : Type → Type → Type
  nat : Type

infixl 5 _,_

data Context : Set where
  ∅ : Context
  _,_ : Context → Type → Context

ctxToType : Context → Type
ctxToType ∅ = unit
ctxToType (Γ , A) = ctxToType Γ × A

infix  4 _∋_
infix  9 S_

data _∋_ : Context → Type → Set where
  Z : ∀ {Γ A} → (Γ , A) ∋ A
  S_ : ∀ {Γ A B} → Γ ∋ A → (Γ , B) ∋ A

infix  4 _⊢_
infix  5 ƛ_
infixl 7 _·_
infix  9 `_
infix  9 `nat_

data _⊢_ : Context → Type → Set where
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
