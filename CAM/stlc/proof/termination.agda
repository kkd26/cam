module CAM.stlc.proof.termination where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong)
open import Data.List
open import Data.List.Properties

open import CAM.stlc.catComb.eval
open import CAM.stlc.catComb.compile renaming (catCombValueToMachineValue to toValue)
open import CAM.stlc.step
open import CAM.machine.eval (CAM→) hiding (Config)

appInstruction-step : ∀ {i e₁ e₂} → CAM→ ⟨ APP ∷ [] ∣ cur i e₁ , e₂ ∣ [] ⟩ ⟨ i ∣ e₁ , e₂ ∣ [] ⟩
appInstruction-step {i} {e₁} {e₂} rewrite sym (cong ⟨_∣ e₁ , e₂ ∣ [] ⟩ (++-identityʳ i)) = app-step

case1Instruction-step : ∀ {f g e₁ e₂} → CAM→ ⟨ CASE f g ∷ [] ∣ e₁ , L e₂ ∣ [] ⟩ ⟨ f ∣ e₁ , e₂ ∣ [] ⟩
case1Instruction-step {f = f} {e₁ = e₁} {e₂ = e₂} rewrite sym (cong ⟨_∣ e₁ , e₂ ∣ [] ⟩ (++-identityʳ f)) = case1-step

case2Instruction-step : ∀ {f g e₁ e₂} → CAM→ ⟨ CASE f g ∷ [] ∣ e₁ , R e₂ ∣ [] ⟩ ⟨ g ∣ e₁ , e₂ ∣ [] ⟩
case2Instruction-step {g = g} {e₁ = e₁} {e₂ = e₂} rewrite sym (cong ⟨_∣ e₁ , e₂ ∣ [] ⟩ (++-identityʳ g)) = case2-step

appendOneInstruction : ∀ {i i₁ i₂ e₁ e₂ s₁ s₂} → CAM→ ⟨ i₁ ∣ e₁ ∣ s₁ ⟩ ⟨ i₂ ∣ e₂ ∣ s₂ ⟩ → CAM→ ⟨ i₁ ++ [ i ] ∣ e₁ ∣ s₁ ⟩ ⟨ i₂ ++ [ i ] ∣ e₂ ∣ s₂ ⟩
appendOneInstruction unit-step = unit-step
appendOneInstruction nat-step = nat-step
appendOneInstruction skip-step = skip-step
appendOneInstruction car-step = car-step
appendOneInstruction cdr-step = cdr-step
appendOneInstruction push-step = push-step
appendOneInstruction swap-step = swap-step
appendOneInstruction cons-step = cons-step
appendOneInstruction cur-step = cur-step
appendOneInstruction {i} (app-step {i₁} {i₂}) rewrite ++-assoc i₂ i₁ [ i ] = app-step
--- SUM TYPE ---
appendOneInstruction inl-step = inl-step
appendOneInstruction inr-step = inr-step
appendOneInstruction {i₃} (case1-step {i₁} {i = i}) rewrite ++-assoc i₁ i [ i₃ ] = case1-step
appendOneInstruction {i₃} (case2-step {i₂ = i₂} {i}) rewrite ++-assoc i₂ i [ i₃ ] = case2-step

appendInstructions : ∀ {i₁ i₂ i' e₁ e₂ s₁ s₂} → CAM→ ⟨ i₁ ∣ e₁ ∣ s₁ ⟩ ⟨ i₂ ∣ e₂ ∣ s₂ ⟩ → CAM→ ⟨ i₁ ++ i' ∣ e₁ ∣ s₁ ⟩ ⟨ i₂ ++ i' ∣ e₂ ∣ s₂ ⟩
appendInstructions {i₁} {i₂} {[]} x rewrite ++-identityʳ i₁ | ++-identityʳ i₂ = x
appendInstructions {i₁} {i₂} {i ∷ i'} x rewrite sym (++-assoc i₁ [ i ] i') | sym (++-assoc i₂ [ i ] i') = appendInstructions (appendOneInstruction x)

splitInstructions : ∀ {i₁ i₂ i₃ e₁ e₂ e₃ s₁ s₂ s₃} → CAM→* ⟨ i₁ ∣ e₁ ∣ s₁ ⟩ ⟨ [] ∣ e₂ ∣ s₂ ⟩ → CAM→* ⟨ i₂ ∣ e₂ ∣ s₂ ⟩ ⟨ i₃ ∣ e₃ ∣ s₃ ⟩ → CAM→* ⟨ i₁ ++ i₂ ∣ e₁ ∣ s₁ ⟩ ⟨ i₃ ∣ e₃ ∣ s₃ ⟩
splitInstructions {[]} refl x = x
splitInstructions {_ ∷ _} (trans x xs) y = trans (splitInstructions x y) (appendInstructions xs)

stackAppendOneValue-step : ∀ {i₁ i₂ e₁ e₂ s₁ s₂ s'} → CAM→ ⟨ i₁ ∣ e₁ ∣ s₁ ⟩ ⟨ i₂ ∣ e₂ ∣ s₂ ⟩ → CAM→ ⟨ i₁ ∣ e₁ ∣ s₁ ++ [ s' ] ⟩ ⟨ i₂ ∣ e₂ ∣ s₂ ++ [ s' ] ⟩
stackAppendOneValue-step unit-step = unit-step
stackAppendOneValue-step nat-step = nat-step
stackAppendOneValue-step skip-step = skip-step
stackAppendOneValue-step car-step = car-step
stackAppendOneValue-step cdr-step = cdr-step
stackAppendOneValue-step push-step = push-step
stackAppendOneValue-step swap-step = swap-step
stackAppendOneValue-step cons-step = cons-step
stackAppendOneValue-step cur-step = cur-step
stackAppendOneValue-step app-step = app-step
--- SUM TYPE ---
stackAppendOneValue-step inl-step = inl-step
stackAppendOneValue-step inr-step = inr-step
stackAppendOneValue-step case1-step = case1-step
stackAppendOneValue-step case2-step = case2-step

stackAppendOneValue-tr : ∀ {i₁ i₂ e₁ e₂ s₁ s₂ s'} → CAM→* ⟨ i₁ ∣ e₁ ∣ s₁ ⟩ ⟨ i₂ ∣ e₂ ∣ s₂ ⟩ → CAM→* ⟨ i₁ ∣ e₁ ∣ s₁ ++ [ s' ] ⟩ ⟨ i₂ ∣ e₂ ∣ s₂ ++ [ s' ] ⟩
stackAppendOneValue-tr refl = refl
stackAppendOneValue-tr (trans x x₁) = trans (stackAppendOneValue-tr x) (stackAppendOneValue-step x₁)

stackAppendValues : ∀ {s₁ s₂ s' i₁ i₂ e₁ e₂} → CAM→* ⟨ i₁ ∣ e₁ ∣ s₁ ⟩ ⟨ i₂ ∣ e₂ ∣ s₂ ⟩ → CAM→* ⟨ i₁ ∣ e₁ ∣ s₁ ++ s' ⟩ ⟨ i₂ ∣ e₂ ∣ s₂ ++ s' ⟩
stackAppendValues {s₁} {s₂} {[]} x rewrite ++-identityʳ s₁ | ++-identityʳ s₂ = x
stackAppendValues {s₁} {s₂} {s ∷ s'} x rewrite sym (++-assoc s₁ [ s ] s') | sym (++-assoc s₂ [ s ] s') = stackAppendValues (stackAppendOneValue-tr x)

catCombEval→machineEval : ∀ {A B s t} {f : CatComb A B} → ⟨ f ∣ s ⟩= t → CAM→* ⟨ code f ∣ toValue s ∣ [] ⟩ ⟨ [] ∣ toValue t ∣ [] ⟩
catCombEval→machineEval ev-unit = trans refl unit-step
catCombEval→machineEval ev-nat = trans refl nat-step
catCombEval→machineEval ev-id = trans refl skip-step
catCombEval→machineEval (ev-comp f₁ f₂) with catCombEval→machineEval f₁ | catCombEval→machineEval f₂
... | x | y = splitInstructions x y
catCombEval→machineEval (ev-pair f₁ f₂) with catCombEval→machineEval f₁ | catCombEval→machineEval f₂
... | x | y = trans (splitInstructions (stackAppendValues x) (trans (splitInstructions (stackAppendValues y) (trans refl cons-step)) swap-step)) push-step
catCombEval→machineEval ev-p1 = trans refl car-step
catCombEval→machineEval ev-p2 = trans refl cdr-step
catCombEval→machineEval ev-cur = trans refl cur-step
catCombEval→machineEval (ev-app f) with catCombEval→machineEval f
... | x = trans x appInstruction-step
--- SUM TYPE ---
catCombEval→machineEval (ev-copair1 f) = trans (catCombEval→machineEval f) case1Instruction-step
catCombEval→machineEval (ev-copair2 f) = trans (catCombEval→machineEval f) case2Instruction-step
catCombEval→machineEval ev-i1 = trans refl inl-step
catCombEval→machineEval ev-i2 = trans refl inr-step
