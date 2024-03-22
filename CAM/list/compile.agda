module CAM.list.compile where

open import Data.List

open import CAM.list.term
open import CAM.list.catComb public
open import CAM.list.inst

⟦_⟧ : ∀ {Γ A} → Γ ⊢ A → CatComb (ctxToType Γ) A
⟦ ⟨⟩ ⟧ = !
⟦ ` Z ⟧ = p₂
⟦ ` (S x) ⟧ = ⟦ ` x ⟧ ∘ p₁
⟦ ƛ M ⟧ = cur ⟦ M ⟧
⟦ M · N ⟧ = app ∘ ⟨ ⟦ M ⟧ , ⟦ N ⟧ ⟩
⟦ fst M ⟧ = p₁ ∘ ⟦ M ⟧
⟦ snd M ⟧ = p₂ ∘ ⟦ M ⟧
⟦ M , N ⟧ = ⟨ ⟦ M ⟧ , ⟦ N ⟧ ⟩
--- LIST OBJECT ---
⟦ [] ⟧ = nil ∘ !
⟦ h ⦂ t ⟧ = cons ∘ ⟨ ⟦ h ⟧ , ⟦ t ⟧ ⟩
⟦ it x r l ⟧  = it ⟦ x ⟧ ⟦ r ⟧ ∘ ⟨ ⟦ l ⟧ , id ⟩

code : ∀ {A B} → CatComb A B → List Inst
code ! = [ UNIT ]
code id = [ SKIP ]
code (g ∘ f) = code f ++ code g
code ⟨ f , g ⟩ = PUSH ∷ code f ++ [ SWAP ] ++ code g ++ [ CONS ]
code p₁ = [ CAR ]
code p₂ = [ CDR ]
code (cur f) = [ CUR (code f) ]
code app = [ APP ]
--- LIST OBJECT ---
code nil = [ NIL ]
code cons = [ C ]
code (it x r) = [ IT (code x) (code r) ]

compile : ∀ {Γ A} → Γ ⊢ A → List Inst
compile M = code ⟦ M ⟧
