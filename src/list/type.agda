module list.type where

infixl 5 _×_
infixr 7 _⇒_

data Type : Set where
  unit : Type
  _×_ : Type → Type → Type
  _⇒_ : Type → Type → Type
--- LIST TYPE ---
  list : Type → Type
