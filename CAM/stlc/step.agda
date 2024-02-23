module CAM.stlc.step where

open import Data.List
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)

open import CAM.config
open import CAM.stlc.inst public
open import CAM.stlc.value public

Config = MakeConfig Inst MachineValue

data CAM→ : Config → Config → Set where
  unit-step : ∀ {i e s} →            CAM→ ⟨ UNIT ∷ i ∣ e ∣ s ⟩               ⟨ i ∣ ⟨⟩ ∣ s ⟩
  nat-step  : ∀ {i e s x} →          CAM→ ⟨ (NAT x) ∷ i ∣ e ∣ s ⟩            ⟨ i ∣ `nat x ∣ s ⟩
  skip-step : ∀ {i e s} →            CAM→ ⟨ SKIP ∷ i ∣ e ∣ s ⟩               ⟨ i ∣ e ∣ s ⟩
  car-step  : ∀ {i e₁ e₂ s} →        CAM→ ⟨ CAR ∷ i ∣ e₁ , e₂ ∣ s ⟩          ⟨ i ∣ e₁ ∣ s ⟩
  cdr-step  : ∀ {i e₁ e₂ s} →        CAM→ ⟨ CDR ∷ i ∣ e₁ , e₂ ∣ s ⟩          ⟨ i ∣ e₂ ∣ s ⟩
  push-step : ∀ {i e s} →            CAM→ ⟨ PUSH ∷ i ∣ e ∣ s ⟩               ⟨ i ∣ e ∣ e ∷ s ⟩
  swap-step : ∀ {i e₁ e₂ s} →        CAM→ ⟨ SWAP ∷ i ∣ e₁ ∣ e₂ ∷ s ⟩         ⟨ i ∣ e₂ ∣ e₁ ∷ s ⟩
  cons-step : ∀ {i e₁ e₂ s} →        CAM→ ⟨ CONS ∷ i ∣ e₂ ∣ e₁ ∷ s ⟩         ⟨ i ∣ e₁ , e₂ ∣ s ⟩
  cur-step  : ∀ {i₁ i₂ e s} →        CAM→ ⟨ CUR i₁ ∷ i₂ ∣ e ∣ s ⟩            ⟨ i₂ ∣ cur i₁ e ∣ s ⟩
  app-step  : ∀ {i₁ i₂ e₁ e₂ s} →    CAM→ ⟨ APP ∷ i₁ ∣ cur i₂ e₁ , e₂ ∣ s ⟩  ⟨ i₂ ++ i₁ ∣ e₁ , e₂ ∣ s ⟩
--- COPRODUCT ---
  inl-step  : ∀ {i e s} →            CAM→ ⟨ INL ∷ i ∣ e ∣ s ⟩                ⟨ i ∣ L e ∣ s ⟩
  inr-step  : ∀ {i e s} →            CAM→ ⟨ INR ∷ i ∣ e ∣ s ⟩                ⟨ i ∣ R e ∣ s ⟩
  case1-step : ∀ {i₁ i₂ i e₁ e₂ s} → CAM→ ⟨ CASE i₁ i₂ ∷ i ∣ e₁ , L e₂ ∣ s ⟩ ⟨ i₁ ++ i ∣ e₁ , e₂ ∣ s ⟩
  case2-step : ∀ {i₁ i₂ i e₁ e₂ s} → CAM→ ⟨ CASE i₁ i₂ ∷ i ∣ e₁ , R e₂ ∣ s ⟩ ⟨ i₂ ++ i ∣ e₁ , e₂ ∣ s ⟩

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
--- SUM TYPE ---
deterministicStep inl-step inl-step = refl
deterministicStep inr-step inr-step = refl
deterministicStep case1-step case1-step = refl
deterministicStep case2-step case2-step = refl
