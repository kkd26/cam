module untyped.run where

open import Data.Nat
open import Data.List

open import config public
open import untyped.inst public
open import untyped.value public

Config = MakeConfig Inst MachineValue

data Result : Set where
  stuck : Result
  notFinished : Config → Result
  done  : MachineValue → Result

run : ℕ → Config → Result
run _ ⟨ [] ∣ env ∣ [] ⟩ = done env
run zero c = notFinished c
run (suc n) ⟨ FST ∷ inst ∣ env , _ ∣ stack ⟩ = run n ⟨ inst ∣ env ∣ stack ⟩
run (suc n) ⟨ SND ∷ inst ∣ _ , env ∣ stack ⟩ = run n ⟨ inst ∣ env ∣ stack ⟩
run (suc n) ⟨ EV ∷ inst ∣ cur C s , t ∣ stack ⟩ = run n ⟨ C ++ inst ∣ s , t ∣ stack ⟩
run (suc n) ⟨ CUR C ∷ inst ∣ env ∣ stack ⟩ = run n ⟨ inst ∣ cur C env ∣ stack ⟩
run (suc n) ⟨ PUSH ∷ inst ∣ env ∣ stack ⟩ = run n ⟨ inst ∣ env ∣ env ∷ stack ⟩
run (suc n) ⟨ SWAP ∷ inst ∣ env ∣ s ∷ stack ⟩ = run n ⟨ inst ∣ s ∣ env ∷ stack ⟩
run (suc n) ⟨ CONS ∷ inst ∣ env ∣ s ∷ stack ⟩ = run n ⟨ inst ∣ s , env ∣ stack ⟩
run (suc n) ⟨ FOLD ∷ inst ∣ env ∣ stack ⟩ = run n ⟨ inst ∣ env ∣ stack ⟩
run (suc n) ⟨ UNFOLD ∷ inst ∣ env ∣ stack ⟩ = run n ⟨ inst ∣ env ∣ stack ⟩
run _ _ = stuck
