module CAM.catComb.compile where

open import Data.List

open import CAM.term
open import CAM.value
open import CAM.catComb public
open import CAM.inst

⟦_⟧ : ∀ {Γ A} → Γ ⊢ A → CatComb (ctxToType Γ) A
⟦ `nat n ⟧ = nat n
⟦ ` Z ⟧ = p₂
⟦ ` (S x) ⟧ = ⟦ ` x ⟧ ∘ p₁
⟦ ƛ M ⟧ = cur ⟦ M ⟧
⟦ M · N ⟧ = app ∘ ⟨ ⟦ M ⟧ , ⟦ N ⟧ ⟩
⟦ fst M ⟧ = p₁ ∘ ⟦ M ⟧
⟦ snd M ⟧ = p₂ ∘ ⟦ M ⟧
⟦ M , N ⟧ = ⟨ ⟦ M ⟧ , ⟦ N ⟧ ⟩

code : ∀ {A B} → CatComb A B → List Inst
code (nat n) = [ NAT n ]
code id = [ SKIP ]
code (g ∘ f) = code f ++ code g
code ⟨ f , g ⟩ = PUSH ∷ code f ++ [ SWAP ] ++ code g ++ [ CONS ]
code p₁ = [ CAR ]
code p₂ = [ CDR ]
code (cur f) = [ CUR (code f) ]
code app = [ APP ]

compile : ∀ {Γ A} → Γ ⊢ A → List Inst
compile M = code ⟦ M ⟧

fromCatCombToMachineValue : ∀ {A} → CatCombValue A → MachineValue
fromCatCombToMachineValue (`nat n) = `nat n
fromCatCombToMachineValue ⟨⟩ = ⟨⟩
fromCatCombToMachineValue (s₁ , s₂) = fromCatCombToMachineValue s₁ , fromCatCombToMachineValue s₂
fromCatCombToMachineValue (cur f s) = cur (code f) (fromCatCombToMachineValue s)
