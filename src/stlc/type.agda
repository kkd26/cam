module stlc.type where

open import Data.Nat using (ℕ)

infixl 5 _×_
infixr 7 _⇒_

data Type : Set where
  unit : Type
  _×_ : Type → Type → Type
  _⇒_ : Type → Type → Type
  nat : Type
--- SUM TYPES ---
  _+_ : Type → Type → Type
