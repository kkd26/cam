module untyped.context where

open import Data.Nat using (ℕ; suc; zero) public

open import untyped.type

Context = ℕ
Var = ℕ

infix 9 S_
infix 4 _∋_

data _∋_ : Context → Var → Set where
  Z : ∀ {Γ} → suc Γ ∋ zero
  S_ : ∀ {n Γ} → suc Γ ∋ n → suc (suc Γ) ∋ suc n

ctxToType : Context → Type
ctxToType zero = unit
ctxToType (suc x) = ctxToType x × U
