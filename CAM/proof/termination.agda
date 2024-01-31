module CAM.proof.termination where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (sym; cong)
open import Data.List
open import Data.List.Properties

open import CAM.step
open import CAM.catComb
open import CAM.catCombProps renaming (fromCatCombToMachineValue to toValue)

appInstruction-step : ∀ {i e₁ e₂} → CAM-step ⟨ APP ∷ [] ∣ cur i e₁ , e₂ ∣ [] ⟩
      ⟨ i ∣ e₁ , e₂ ∣ [] ⟩
appInstruction-step {i} {e₁} {e₂} rewrite sym (cong ⟨_∣ e₁ , e₂ ∣ [] ⟩ (++-identityʳ i)) = app-red

appendOneInstruction : ∀ {i i₁ i₂ e₁ e₂ s₁ s₂} → CAM-step ⟨ i₁ ∣ e₁ ∣ s₁ ⟩ ⟨ i₂ ∣ e₂ ∣ s₂ ⟩ → CAM-step ⟨ i₁ ++ [ i ] ∣ e₁ ∣ s₁ ⟩ ⟨ i₂ ++ [ i ] ∣ e₂ ∣ s₂ ⟩
appendOneInstruction natE-red = natE-red
appendOneInstruction nat-red = nat-red
appendOneInstruction skip-red = skip-red
appendOneInstruction car-red = car-red
appendOneInstruction cdr-red = cdr-red
appendOneInstruction push-red = push-red
appendOneInstruction swap-red = swap-red
appendOneInstruction cons-red = cons-red
appendOneInstruction cur-red = cur-red
appendOneInstruction {i} (app-red {i₁} {i₂}) rewrite ++-assoc i₂ i₁ [ i ] = app-red

appendInstructions : ∀ {i₁ i₂ i' e₁ e₂ s₁ s₂} → CAM-step ⟨ i₁ ∣ e₁ ∣ s₁ ⟩ ⟨ i₂ ∣ e₂ ∣ s₂ ⟩ → CAM-step ⟨ i₁ ++ i' ∣ e₁ ∣ s₁ ⟩ ⟨ i₂ ++ i' ∣ e₂ ∣ s₂ ⟩
appendInstructions {i₁} {i₂} {[]} x rewrite ++-identityʳ i₁ | ++-identityʳ i₂ = x
appendInstructions {i₁} {i₂} {i ∷ i'} x rewrite sym (++-assoc i₁ [ i ] i') | sym (++-assoc i₂ [ i ] i') = appendInstructions (appendOneInstruction x)

splitInstructions : ∀ {i₁ i₂ i₃ e₁ e₂ e₃ s₁ s₂ s₃} → CAM-tr ⟨ i₁ ∣ e₁ ∣ s₁ ⟩ ⟨ [] ∣ e₂ ∣ s₂ ⟩ → CAM-tr ⟨ i₂ ∣ e₂ ∣ s₂ ⟩ ⟨ i₃ ∣ e₃ ∣ s₃ ⟩ → CAM-tr ⟨ i₁ ++ i₂ ∣ e₁ ∣ s₁ ⟩ ⟨ i₃ ∣ e₃ ∣ s₃ ⟩
splitInstructions {[]} refl x = x
splitInstructions {_ ∷ _} (trans x xs) y = trans (splitInstructions x y) (appendInstructions xs)

stackAppendOneValue-step : ∀ {i₁ i₂ e₁ e₂ s₁ s₂ s'} → CAM-step ⟨ i₁ ∣ e₁ ∣ s₁ ⟩ ⟨ i₂ ∣ e₂ ∣ s₂ ⟩ → CAM-step ⟨ i₁ ∣ e₁ ∣ s₁ ++ [ s' ] ⟩ ⟨ i₂ ∣ e₂ ∣ s₂ ++ [ s' ] ⟩
stackAppendOneValue-step natE-red = natE-red
stackAppendOneValue-step nat-red = nat-red
stackAppendOneValue-step skip-red = skip-red
stackAppendOneValue-step car-red = car-red
stackAppendOneValue-step cdr-red = cdr-red
stackAppendOneValue-step push-red = push-red
stackAppendOneValue-step swap-red = swap-red
stackAppendOneValue-step cons-red = cons-red
stackAppendOneValue-step cur-red = cur-red
stackAppendOneValue-step app-red = app-red

stackAppendOneValue-tr : ∀ {i₁ i₂ e₁ e₂ s₁ s₂ s'} → CAM-tr ⟨ i₁ ∣ e₁ ∣ s₁ ⟩ ⟨ i₂ ∣ e₂ ∣ s₂ ⟩ → CAM-tr ⟨ i₁ ∣ e₁ ∣ s₁ ++ [ s' ] ⟩ ⟨ i₂ ∣ e₂ ∣ s₂ ++ [ s' ] ⟩
stackAppendOneValue-tr refl = refl
stackAppendOneValue-tr (trans x x₁) = trans (stackAppendOneValue-tr x) (stackAppendOneValue-step x₁)

stackAppendValues : ∀ {s₁ s₂ s' i₁ i₂ e₁ e₂} → CAM-tr ⟨ i₁ ∣ e₁ ∣ s₁ ⟩ ⟨ i₂ ∣ e₂ ∣ s₂ ⟩ → CAM-tr ⟨ i₁ ∣ e₁ ∣ s₁ ++ s' ⟩ ⟨ i₂ ∣ e₂ ∣ s₂ ++ s' ⟩
stackAppendValues {s₁} {s₂} {[]} x rewrite ++-identityʳ s₁ | ++-identityʳ s₂ = x
stackAppendValues {s₁} {s₂} {s ∷ s'} x rewrite sym (++-assoc s₁ [ s ] s') | sym (++-assoc s₂ [ s ] s') = stackAppendValues (stackAppendOneValue-tr x)

proof : ∀ {f : CatComb} → {s t : CatCombValue} → ⟨ f ∣ s ⟩= t → CAM-tr ⟨ code f ∣ toValue s ∣ [] ⟩ ⟨ [] ∣ toValue t ∣ [] ⟩
proof ev-id = trans refl skip-red
proof (ev-comp f₁ f₂) with proof f₁ | proof f₂
... | x | y = splitInstructions x y
proof (ev-pair f₁ f₂) with proof f₁ | proof f₂
... | x | y = trans (splitInstructions (stackAppendValues x) (trans (splitInstructions (stackAppendValues y) (trans refl cons-red)) swap-red)) push-red
proof ev-p1 = trans refl car-red
proof ev-p2 = trans refl cdr-red
proof ev-cur = trans refl cur-red
proof (ev-app f) with proof f
... | x = trans x appInstruction-step
