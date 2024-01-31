module CAM.runNonTerminating where

open import Data.List

open import CAM.config

data Result : Set where
  stuck : Result
  done  : MachineValue → Result

{-# TERMINATING #-}
run : Config → Result
run ⟨ [] ∣ env ∣ [] ⟩ = done env
run ⟨ [] ∣ env ∣ _ ∷ _ ⟩ = stuck
run ⟨ NAT x ∷ inst ∣ ⟨⟩ ∣ stack ⟩ = run ⟨ inst ∣ `nat x ∣ stack ⟩
run ⟨ NAT x ∷ inst ∣ env ∣ stack ⟩ = run ⟨ inst ∣ env , `nat x ∣ stack ⟩
run ⟨ SKIP ∷ inst ∣ env ∣ stack ⟩ = run ⟨ inst ∣ env ∣ stack ⟩
run ⟨ CAR ∷ inst ∣ env , _ ∣ stack ⟩ = run ⟨ inst ∣ env ∣ stack ⟩
run ⟨ CDR ∷ inst ∣ _ , env ∣ stack ⟩ = run ⟨ inst ∣ env ∣ stack ⟩
run ⟨ APP ∷ inst ∣ cur C s , t ∣ stack ⟩ = run ⟨ C ++ inst ∣ s , t ∣ stack ⟩
run ⟨ CUR C ∷ inst ∣ env ∣ stack ⟩ = run ⟨ inst ∣ cur C env ∣ stack ⟩
run ⟨ PUSH ∷ inst ∣ env ∣ stack ⟩ = run ⟨ inst ∣ env ∣ env ∷ stack ⟩
run ⟨ SWAP ∷ inst ∣ env ∣ s ∷ stack ⟩ = run ⟨ inst ∣ s ∣ env ∷ stack ⟩
run ⟨ CONS ∷ inst ∣ env ∣ s ∷ stack ⟩ = run ⟨ inst ∣ s , env ∣ stack ⟩
run _ = stuck
