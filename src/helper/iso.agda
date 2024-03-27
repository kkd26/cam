module helper.iso where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_)

infix 0 _≃_
record _≃_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x
    to∘from : ∀ (y : B) → to (from y) ≡ y

infix 0 _⇔_
record _⇔_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A
