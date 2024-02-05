module CAM.proof.termination where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong)
open import Data.List
open import Data.List.Properties

open import CAM.step
open import CAM.catComb
open import CAM.catCombProps renaming (fromCatCombToMachineValue to toValue)
open import CAM.term

appInstruction-step : ∀ {i e₁ e₂} → CAM-step ⟨ APP ∷ [] ∣ cur i e₁ , e₂ ∣ [] ⟩ ⟨ i ∣ e₁ , e₂ ∣ [] ⟩
appInstruction-step {i} {e₁} {e₂} rewrite sym (cong ⟨_∣ e₁ , e₂ ∣ [] ⟩ (++-identityʳ i)) = app-red

appendOneInstruction : ∀ {i i₁ i₂ e₁ e₂ s₁ s₂} → CAM-step ⟨ i₁ ∣ e₁ ∣ s₁ ⟩ ⟨ i₂ ∣ e₂ ∣ s₂ ⟩ → CAM-step ⟨ i₁ ++ [ i ] ∣ e₁ ∣ s₁ ⟩ ⟨ i₂ ++ [ i ] ∣ e₂ ∣ s₂ ⟩
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

terminate : ∀ {A B s t} {f : CatComb (A ⇒ B)} → ⟨ f ∣ s ⟩= t → CAM-tr ⟨ code f ∣ toValue s ∣ [] ⟩ ⟨ [] ∣ toValue t ∣ [] ⟩
terminate ev-nat = trans refl nat-red
terminate ev-id = trans refl skip-red
terminate (ev-comp f₁ f₂) with terminate f₁ | terminate f₂
... | x | y = splitInstructions x y
terminate (ev-pair f₁ f₂) with terminate f₁ | terminate f₂
... | x | y = trans (splitInstructions (stackAppendValues x) (trans (splitInstructions (stackAppendValues y) (trans refl cons-red)) swap-red)) push-red
terminate ev-p1 = trans refl car-red
terminate ev-p2 = trans refl cdr-red
terminate ev-cur = trans refl cur-red
terminate (ev-app f) with terminate f
... | x = trans x appInstruction-step

uniqueness : ∀ {A B s t t'} {f : CatComb (A ⇒ B)} → ⟨ f ∣ s ⟩= t → ⟨ f ∣ s ⟩= t' → t ≡ t'
uniqueness ev-nat ev-nat = refl
uniqueness ev-id ev-id = refl
uniqueness (ev-comp x x₁) (ev-comp y y₁) rewrite uniqueness x y = uniqueness x₁ y₁
uniqueness (ev-pair x x₁) (ev-pair {s₁ = s₁} y y₁) with uniqueness x y | uniqueness x₁ y₁
... | z | w rewrite z = cong (s₁ ,_) w
uniqueness ev-p1 ev-p1 = refl
uniqueness ev-p2 ev-p2 = refl
uniqueness ev-cur ev-cur = refl
uniqueness (ev-app x) (ev-app y) = uniqueness x y

deterministicStep : ∀ {a b c : Config} →  CAM-step a b → CAM-step a c → b ≡ c
deterministicStep nat-red nat-red = refl
deterministicStep skip-red skip-red = refl
deterministicStep car-red car-red = refl
deterministicStep cdr-red cdr-red = refl
deterministicStep push-red push-red = refl
deterministicStep swap-red swap-red = refl
deterministicStep cons-red cons-red = refl
deterministicStep cur-red cur-red = refl
deterministicStep app-red app-red = refl
