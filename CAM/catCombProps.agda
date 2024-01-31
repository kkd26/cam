module CAM.catCombProps where

open import Data.List

open import CAM.term
open import CAM.value
open import CAM.catComb
open import CAM.inst

data ⟨_∣_⟩=_ : CatComb → CatCombValue → CatCombValue → Set where
  ev-id : ∀ {s} → ⟨ id ∣ s ⟩= s
  ev-comp : ∀ {f g s s₁ s₂} → ⟨ f ∣ s ⟩= s₁ → ⟨ g ∣ s₁ ⟩= s₂ → ⟨ g ∘ f ∣ s ⟩= s₂
  ev-pair : ∀ {f g s s₁ s₂} → ⟨ f ∣ s ⟩= s₁ → ⟨ g ∣ s ⟩= s₂ → ⟨ ⟨ f , g ⟩ ∣ s ⟩= (s₁ , s₂)
  ev-p1 : ∀ {s₁ s₂} → ⟨ p₁ ∣ s₁ , s₂ ⟩= s₁
  ev-p2 : ∀ {s₁ s₂} → ⟨ p₂ ∣ s₁ , s₂ ⟩= s₂
  ev-cur : ∀ {f s} → ⟨ cur f ∣ s ⟩= cur f s
  ev-app : ∀ {f s t s₁} → ⟨ f ∣ s , t ⟩= s₁ → ⟨ app ∣ cur f s , t ⟩= s₁

⟦_⟧ : ∀ {Γ A} → Γ ⊢ A → CatComb
⟦ `nat n ⟧ = nat n
⟦ ` Z ⟧ = p₂
⟦ ` (S x) ⟧ = ⟦ ` x ⟧ ∘ p₁
⟦ ƛ M ⟧ = cur ⟦ M ⟧
⟦ M · N ⟧ = app ∘ ⟨ ⟦ M ⟧ , ⟦ N ⟧ ⟩ 
⟦ fst M ⟧ = p₁ ∘ ⟦ M ⟧
⟦ snd M ⟧ = p₂ ∘ ⟦ M ⟧
⟦ M , N ⟧ = ⟨ ⟦ M ⟧ , ⟦ N ⟧ ⟩

code : CatComb → List Inst
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

fromCatCombToMachineValue : CatCombValue → MachineValue
fromCatCombToMachineValue (`nat n) = `nat n
fromCatCombToMachineValue ⟨⟩ = ⟨⟩
fromCatCombToMachineValue (s₁ , s₂) = fromCatCombToMachineValue s₁ , fromCatCombToMachineValue s₂
fromCatCombToMachineValue (cur f s) = cur (code f) (fromCatCombToMachineValue s)
