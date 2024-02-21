module CAM.proof.termination where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong)
open import Data.List
open import Data.List.Properties

open import CAM.step
open import CAM.catComb.eval
open import CAM.catComb.compile renaming (fromCatCombToMachineValue to toValue)

open Type

appInstruction-step : ∀ {i e₁ e₂} → CAM→ ⟨ APP ∷ [] ∣ cur i e₁ , e₂ ∣ [] ⟩ ⟨ i ∣ e₁ , e₂ ∣ [] ⟩
appInstruction-step {i} {e₁} {e₂} rewrite sym (cong ⟨_∣ e₁ , e₂ ∣ [] ⟩ (++-identityʳ i)) = app-step

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

stackAppendOneValue-tr : ∀ {i₁ i₂ e₁ e₂ s₁ s₂ s'} → CAM→* ⟨ i₁ ∣ e₁ ∣ s₁ ⟩ ⟨ i₂ ∣ e₂ ∣ s₂ ⟩ → CAM→* ⟨ i₁ ∣ e₁ ∣ s₁ ++ [ s' ] ⟩ ⟨ i₂ ∣ e₂ ∣ s₂ ++ [ s' ] ⟩
stackAppendOneValue-tr refl = refl
stackAppendOneValue-tr (trans x x₁) = trans (stackAppendOneValue-tr x) (stackAppendOneValue-step x₁)

stackAppendValues : ∀ {s₁ s₂ s' i₁ i₂ e₁ e₂} → CAM→* ⟨ i₁ ∣ e₁ ∣ s₁ ⟩ ⟨ i₂ ∣ e₂ ∣ s₂ ⟩ → CAM→* ⟨ i₁ ∣ e₁ ∣ s₁ ++ s' ⟩ ⟨ i₂ ∣ e₂ ∣ s₂ ++ s' ⟩
stackAppendValues {s₁} {s₂} {[]} x rewrite ++-identityʳ s₁ | ++-identityʳ s₂ = x
stackAppendValues {s₁} {s₂} {s ∷ s'} x rewrite sym (++-assoc s₁ [ s ] s') | sym (++-assoc s₂ [ s ] s') = stackAppendValues (stackAppendOneValue-tr x)

terminate : ∀ {A B s t} {f : CatComb A B} → ⟨ f ∣ s ⟩= t → CAM→* ⟨ code f ∣ toValue s ∣ [] ⟩ ⟨ [] ∣ toValue t ∣ [] ⟩
terminate ev-unit = trans refl unit-step
terminate ev-nat = trans refl nat-step
terminate ev-id = trans refl skip-step
terminate (ev-comp f₁ f₂) with terminate f₁ | terminate f₂
... | x | y = splitInstructions x y
terminate (ev-pair f₁ f₂) with terminate f₁ | terminate f₂
... | x | y = trans (splitInstructions (stackAppendValues x) (trans (splitInstructions (stackAppendValues y) (trans refl cons-step)) swap-step)) push-step
terminate ev-p1 = trans refl car-step
terminate ev-p2 = trans refl cdr-step
terminate ev-cur = trans refl cur-step
terminate (ev-app f) with terminate f
... | x = trans x appInstruction-step

uniqueness : ∀ {A B s t t'} {f : CatComb A B} → ⟨ f ∣ s ⟩= t → ⟨ f ∣ s ⟩= t' → t ≡ t'
uniqueness ev-unit ev-unit = refl
uniqueness ev-nat ev-nat = refl
uniqueness ev-id ev-id = refl
uniqueness (ev-comp x x₁) (ev-comp y y₁) rewrite uniqueness x y = uniqueness x₁ y₁
uniqueness (ev-pair x x₁) (ev-pair {s₁ = s₁} y y₁) with uniqueness x y | uniqueness x₁ y₁
... | z | w rewrite z = cong (s₁ ,_) w
uniqueness ev-p1 ev-p1 = refl
uniqueness ev-p2 ev-p2 = refl
uniqueness ev-cur ev-cur = refl
uniqueness (ev-app x) (ev-app y) = uniqueness x y

deterministicStep : ∀ {a b c : Config} →  CAM→ a b → CAM→ a c → b ≡ c
deterministicStep unit-step unit-step = refl
deterministicStep nat-step nat-step = refl
deterministicStep skip-step skip-step = refl
deterministicStep car-step car-step = refl
deterministicStep cdr-step cdr-step = refl
deterministicStep push-step push-step = refl
deterministicStep swap-step swap-step = refl
deterministicStep cons-step cons-step = refl
deterministicStep cur-step cur-step = refl
deterministicStep app-step app-step = refl
