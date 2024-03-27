module list.run where

open import Data.Nat
open import Data.List

open import config public
open import list.inst public
open import list.value public

Config = MakeConfig Inst MachineValue

data Result : Set where
  stuck : Result
  notFinished : Config → Result
  done  : MachineValue → Result

run : ℕ → Config → Result
run _ ⟨ [] ∣ env ∣ [] ⟩ = done env
run zero c = notFinished c
run (suc n) ⟨ UNIT ∷ inst ∣ env ∣ stack ⟩ = run n ⟨ inst ∣ ⟨⟩ ∣ stack ⟩
run (suc n) ⟨ SKIP ∷ inst ∣ env ∣ stack ⟩ = run n ⟨ inst ∣ env ∣ stack ⟩
run (suc n) ⟨ CAR ∷ inst ∣ env , _ ∣ stack ⟩ = run n ⟨ inst ∣ env ∣ stack ⟩
run (suc n) ⟨ CDR ∷ inst ∣ _ , env ∣ stack ⟩ = run n ⟨ inst ∣ env ∣ stack ⟩
run (suc n) ⟨ APP ∷ inst ∣ cur I s , t ∣ stack ⟩ = run n ⟨ I ++ inst ∣ s , t ∣ stack ⟩
run (suc n) ⟨ CUR I ∷ inst ∣ env ∣ stack ⟩ = run n ⟨ inst ∣ cur I env ∣ stack ⟩
run (suc n) ⟨ PUSH ∷ inst ∣ env ∣ stack ⟩ = run n ⟨ inst ∣ env ∣ env ∷ stack ⟩
run (suc n) ⟨ SWAP ∷ inst ∣ env ∣ s ∷ stack ⟩ = run n ⟨ inst ∣ s ∣ env ∷ stack ⟩
run (suc n) ⟨ CONS ∷ inst ∣ env ∣ s ∷ stack ⟩ = run n ⟨ inst ∣ s , env ∣ stack ⟩
--- LIST OBJECT ---
run (suc n) ⟨ NIL ∷ inst ∣ env ∣ stack ⟩ = run n ⟨ inst ∣ [] ∣ stack ⟩
run (suc n) ⟨ C ∷ inst ∣ h , t ∣ stack ⟩ = run n ⟨ inst ∣ h ⦂ t ∣ stack ⟩
run (suc n) ⟨ IT x r ∷ inst ∣ [] , p ∣ stack ⟩ = run n ⟨ x ++ inst ∣ p ∣ stack ⟩
run (suc n) ⟨ IT x r ∷ inst ∣ h ⦂ t , p ∣ stack ⟩ = run n ⟨ IT x r ∷ CONS ∷ CONS ∷ r ++ inst ∣ t , p ∣ h ∷ p ∷ stack ⟩
run _ _ = stuck
