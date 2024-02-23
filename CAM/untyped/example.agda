module CAM.untyped.example where

open import Data.List

open import CAM.untyped.term
open import CAM.untyped.compile
open import CAM.untyped.run

x : CatComb unit U
x = ⟦ ( (ƛ ` Z · ` Z) · (ƛ ` Z · ` Z)) * ⟧

y : Result
y = run 10 ⟨ code x ∣ ⟨⟩ ∣ [] ⟩
