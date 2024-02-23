module CAM.untyped.type where

infixl 6 _⇒_
infix 5 _×_

data Type : Set where
  U : Type
  unit : Type
  _×_ : Type → Type → Type
  _⇒_ : Type → Type → Type
