module CAM.stlc.catComb.compile where

open import Data.List

open import CAM.stlc.term
open import CAM.stlc.value
open import CAM.stlc.catComb public
open import CAM.stlc.inst
open import CAM.context

⟦_⟧ : ∀ {Γ A} → Γ ⊢ A → CatComb (ctxToType Γ) A
⟦ ⟨⟩ ⟧ = !
⟦ `nat n ⟧ = nat n
⟦ ` Z ⟧ = p₂
⟦ ` (S x) ⟧ = ⟦ ` x ⟧ ∘ p₁
⟦ ƛ M ⟧ = cur ⟦ M ⟧
⟦ M · N ⟧ = app ∘ ⟨ ⟦ M ⟧ , ⟦ N ⟧ ⟩
⟦ fst M ⟧ = p₁ ∘ ⟦ M ⟧
⟦ snd M ⟧ = p₂ ∘ ⟦ M ⟧
⟦ M , N ⟧ = ⟨ ⟦ M ⟧ , ⟦ N ⟧ ⟩
--- COPRODUCT ---
⟦ inl M ⟧ = i1 ∘ ⟦ M ⟧
⟦ inr M ⟧ = i2 ∘ ⟦ M ⟧
⟦ case M inl M₁ inr M₂ ⟧ = [_,_] ⟦ M₁ ⟧ ⟦ M₂ ⟧ ∘ ⟨ id , ⟦ M ⟧ ⟩

code : ∀ {A B} → CatComb A B → List Inst
code ! = [ UNIT ]
code (nat n) = [ NAT n ]
code id = [ SKIP ]
code (g ∘ f) = code f ++ code g
code ⟨ f , g ⟩ = PUSH ∷ code f ++ [ SWAP ] ++ code g ++ [ CONS ]
code p₁ = [ CAR ]
code p₂ = [ CDR ]
code (cur f) = [ CUR (code f) ]
code app = [ APP ]
code [ f , g ] = [ CASE (code f) (code g) ]
code i1 = [ INL ]
code i2 = [ INR ]

compile : ∀ {Γ A} → Γ ⊢ A → List Inst
compile M = code ⟦ M ⟧

catCombValueToMachineValue : ∀ {A} → CatCombValue A → MachineValue
catCombValueToMachineValue (`nat n) = `nat n
catCombValueToMachineValue ⟨⟩ = ⟨⟩
catCombValueToMachineValue (s₁ , s₂) = catCombValueToMachineValue s₁ , catCombValueToMachineValue s₂
catCombValueToMachineValue (cur f s) = cur (code f) (catCombValueToMachineValue s)
catCombValueToMachineValue (L x) = L catCombValueToMachineValue x
catCombValueToMachineValue (R x) = R catCombValueToMachineValue x

ctxToMachineValue : ∀ {Γ} → ValueOfContext Γ → MachineValue
ctxToMachineValue empty = ⟨⟩
ctxToMachineValue (cons x x₁) with ctxToMachineValue x | catCombValueToMachineValue x₁
... | z | w = z , w
