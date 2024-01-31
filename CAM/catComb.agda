module CAM.catComb where

open import Data.Nat using (ℕ)

open import CAM.term

infix 5 _∘_

data CatComb : Set where
  nat : ℕ → CatComb
  id : CatComb
  _∘_ : CatComb → CatComb → CatComb
  ⟨_,_⟩ : CatComb → CatComb → CatComb
  p₁ : CatComb
  p₂ : CatComb
  cur : CatComb → CatComb
  app : CatComb
