module CAM.example where

open import Data.List

open import CAM.term
open import CAM.config
open import CAM.catComb.compile
open import CAM.runNonTerminating

open Utils

ex1 : ∅ ⊢ nat × nat
ex1 = (ƛ ƛ (# 1 , # 0)) · `nat 3 · `nat 4

inst1 : List Inst
inst1 = compile ex1

x : Result
x = run ⟨ inst1 ∣ ⟨⟩ ∣ [] ⟩
