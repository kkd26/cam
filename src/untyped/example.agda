module untyped.example where

open import Data.List

open import untyped.term
open import untyped.compile
open import untyped.run

x : CatComb unit U
x = ⟦ ( (ƛ ` Z · ` Z) · (ƛ ` Z · ` Z)) * ⟧

y : Result
y = run 10 ⟨ code x ∣ ⟨⟩ ∣ [] ⟩
