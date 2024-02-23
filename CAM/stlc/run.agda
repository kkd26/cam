module CAM.stlc.run where

open import Data.Nat
open import Data.List

open import CAM.config
open import CAM.stlc.value public
open import CAM.stlc.inst public

Config = MakeConfig Inst MachineValue

data Result : Set where
  stuck : Result
  notFinished : Config → Result
  done  : MachineValue → Result

run : ℕ → Config → Result
run _ ⟨ [] ∣ env ∣ [] ⟩ = done env
run zero c = notFinished c
run (suc n) ⟨ UNIT ∷ inst ∣ e ∣ stack ⟩ = run n ⟨ inst ∣ ⟨⟩ ∣ stack ⟩
run (suc n) ⟨ NAT x ∷ inst ∣ e ∣ stack ⟩ = run n ⟨ inst ∣ `nat x ∣ stack ⟩
run (suc n) ⟨ SKIP ∷ inst ∣ env ∣ stack ⟩ = run n ⟨ inst ∣ env ∣ stack ⟩
run (suc n) ⟨ CAR ∷ inst ∣ env , _ ∣ stack ⟩ = run n ⟨ inst ∣ env ∣ stack ⟩
run (suc n) ⟨ CDR ∷ inst ∣ _ , env ∣ stack ⟩ = run n ⟨ inst ∣ env ∣ stack ⟩
run (suc n) ⟨ APP ∷ inst ∣ cur C s , t ∣ stack ⟩ = run n ⟨ C ++ inst ∣ s , t ∣ stack ⟩
run (suc n) ⟨ CUR C ∷ inst ∣ env ∣ stack ⟩ = run n ⟨ inst ∣ cur C env ∣ stack ⟩
run (suc n) ⟨ PUSH ∷ inst ∣ env ∣ stack ⟩ = run n ⟨ inst ∣ env ∣ env ∷ stack ⟩
run (suc n) ⟨ SWAP ∷ inst ∣ env ∣ s ∷ stack ⟩ = run n ⟨ inst ∣ s ∣ env ∷ stack ⟩
run (suc n) ⟨ CONS ∷ inst ∣ env ∣ s ∷ stack ⟩ = run n ⟨ inst ∣ s , env ∣ stack ⟩
run (suc n) ⟨ CASE i₁ i₂ ∷ i ∣ e₁ , L e₂ ∣ s ⟩ = run n ⟨ i₁ ++ i ∣ e₁ , e₂ ∣ s ⟩
run (suc n) ⟨ CASE i₁ i₂ ∷ i ∣ e₁ , R e₂ ∣ s ⟩ = run n ⟨ i₂ ++ i ∣ e₁ , e₂ ∣ s ⟩
run (suc n) ⟨ INL ∷ i ∣ e ∣ s ⟩ = run n ⟨ i ∣ L e ∣ s ⟩
run (suc n) ⟨ INR ∷ i ∣ e ∣ s ⟩ = run n ⟨ i ∣ R e ∣ s ⟩
run _ _ = stuck
