module CAM.stlc.example where

open import Data.List

open import CAM.stlc.term
open import CAM.config
open import CAM.stlc.catComb.compile
open import CAM.stlc.run

open Utils

ex1 : ∅ ⊢ nat × nat
ex1 = (ƛ ƛ (# 1 , # 0)) · `nat 3 · `nat 4

inst1 : List Inst
inst1 = compile ex1

x : Result
x = run 100 ⟨ inst1 ∣ ⟨⟩ ∣ [] ⟩

ex2 : ∅ ⊢ nat × nat
ex2 = case (inr (`nat 2)) inl (# 0 , `nat 4) inr (# 0 , `nat 3)

inst2 : List Inst
inst2 = compile ex2

x2 : Result
x2 = run 100 ⟨ inst2 ∣ ⟨⟩ ∣ [] ⟩
