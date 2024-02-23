module CAM.untyped.compile where

open import Data.List hiding (unfold)

open import CAM.untyped.term
open import CAM.untyped.context
open import CAM.untyped.catComb public
open import CAM.untyped.inst

⟦_⟧ : ∀ {Γ A} → Γ ⊢ A → CatComb (ctxToType Γ) A
⟦ ` Z ⟧ = p₂
⟦ ` S x ⟧ = ⟦ ` x ⟧ ∘ p₁
⟦ j x x₁ ⟧ = ev ∘ ⟨ unfold ∘ ⟦ x ⟧ , ⟦ x₁ ⟧ ⟩
⟦ i x ⟧ = fold ∘ ⟦ x ⟧
⟦ ƛ x ⟧ = cur ⟦ x ⟧

code : ∀ {A B} → CatComb A B → List Inst
code fold = [ FOLD ]
code unfold = [ UNFOLD ]
code (x₁ ∘ x₂) = code x₂ ++ code x₁
code ⟨ f , g ⟩ =  PUSH ∷ code f ++ [ SWAP ] ++ code g ++ [ CONS ]
code p₁ = [ FST ]
code p₂ = [ SND ]
code (cur x₁) = [ CUR (code x₁) ]
code ev = [ EV ]
