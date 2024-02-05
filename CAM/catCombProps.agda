module CAM.catCombProps where

open import Data.List

open import CAM.term
open import CAM.value
open import CAM.catComb
open import CAM.inst

data ⟨_∣_⟩=_ : ∀ {A B} → CatComb (A ⇒ B) → CatCombValue A → CatCombValue B → Set where
  ev-nat : ∀ {A x} {s : CatCombValue A} → ⟨ nat x ∣ s ⟩= (`nat x)
  ev-id : ∀ {A} {s : CatCombValue A} → ⟨ id ∣ s ⟩= s
  ev-comp : ∀ {A B C s s₁ s₂} {f : CatComb (A ⇒ B)} {g : CatComb (B ⇒ C)} → ⟨ f ∣ s ⟩= s₁ → ⟨ g ∣ s₁ ⟩= s₂ → ⟨ g ∘ f ∣ s ⟩= s₂
  ev-pair : ∀ {A B C} {f : CatComb (A ⇒ B)} {g : CatComb (A ⇒ C)} {s s₁ s₂} → ⟨ f ∣ s ⟩= s₁ → ⟨ g ∣ s ⟩= s₂ → ⟨ ⟨ f , g ⟩ ∣ s ⟩= (s₁ , s₂)
  ev-p1 : ∀ {A B} {s₁ : CatCombValue A} {s₂ : CatCombValue B} → ⟨ p₁ ∣ s₁ , s₂ ⟩= s₁
  ev-p2 : ∀ {A B} {s₁ : CatCombValue A} {s₂ : CatCombValue B} → ⟨ p₂ ∣ s₁ , s₂ ⟩= s₂
  ev-cur : ∀ {A B C s} {f : CatComb ((A × B) ⇒ C)} → ⟨ cur f ∣ s ⟩= cur f s
  ev-app : ∀ {A B C s t s₁} {f : CatComb ((A × B) ⇒ C)} → ⟨ f ∣ s , t ⟩= s₁ → ⟨ app ∣ cur f s , t ⟩= s₁

ctxToType : Context → Type
ctxToType ∅ = unit
ctxToType (Γ , A) = ctxToType Γ × A

⟦_⟧ : ∀ {Γ A} → Γ ⊢ A → CatComb ((ctxToType Γ) ⇒ A)
⟦ `nat n ⟧ = nat n
⟦ ` Z ⟧ = p₂
⟦ ` (S x) ⟧ = ⟦ ` x ⟧ ∘ p₁
⟦ ƛ M ⟧ = cur ⟦ M ⟧
⟦ M · N ⟧ = app ∘ ⟨ ⟦ M ⟧ , ⟦ N ⟧ ⟩ 
⟦ fst M ⟧ = p₁ ∘ ⟦ M ⟧
⟦ snd M ⟧ = p₂ ∘ ⟦ M ⟧
⟦ M , N ⟧ = ⟨ ⟦ M ⟧ , ⟦ N ⟧ ⟩

code : ∀ {A} → CatComb A → List Inst
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
