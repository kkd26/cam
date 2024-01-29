module CAM.catComb where

open import CAM.term
open import Data.Nat using (ℕ)

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

⟦_⟧ : ∀ {Γ A} → Γ ⊢ A → CatComb
⟦ `nat x ⟧ = nat x
⟦ ` Z ⟧ = p₂
⟦ ` (S x) ⟧ = ⟦ ` x ⟧ ∘ p₁
⟦ ƛ M ⟧ = cur ⟦ M ⟧
⟦ M · N ⟧ = app ∘ ⟨ ⟦ M ⟧ , ⟦ N ⟧ ⟩ 
⟦ fst M ⟧ = p₁ ∘ ⟦ M ⟧
⟦ snd M ⟧ = p₂ ∘ ⟦ M ⟧
⟦ M , N ⟧ = ⟨ ⟦ M ⟧ , ⟦ N ⟧ ⟩
