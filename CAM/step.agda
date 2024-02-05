module CAM.step where

open import Data.List

open import CAM.inst public
open import CAM.config public

data CAM→ : Config → Config → Set where
  unit-step : ∀ {i e s} →         CAM→ ⟨ UNIT ∷ i ∣ e ∣ s ⟩              ⟨ i ∣ ⟨⟩ ∣ s ⟩
  nat-step  : ∀ {i e s x} →       CAM→ ⟨ (NAT x) ∷ i ∣ e ∣ s ⟩           ⟨ i ∣ `nat x ∣ s ⟩
  skip-step : ∀ {i e s} →         CAM→ ⟨ SKIP ∷ i ∣ e ∣ s ⟩              ⟨ i ∣ e ∣ s ⟩
  car-step  : ∀ {i e₁ e₂ s} →     CAM→ ⟨ CAR ∷ i ∣ e₁ , e₂ ∣ s ⟩         ⟨ i ∣ e₁ ∣ s ⟩
  cdr-step  : ∀ {i e₁ e₂ s} →     CAM→ ⟨ CDR ∷ i ∣ e₁ , e₂ ∣ s ⟩         ⟨ i ∣ e₂ ∣ s ⟩
  push-step : ∀ {i e s} →         CAM→ ⟨ PUSH ∷ i ∣ e ∣ s ⟩              ⟨ i ∣ e ∣ e ∷ s ⟩
  swap-step : ∀ {i e₁ e₂ s} →     CAM→ ⟨ SWAP ∷ i ∣ e₁ ∣ e₂ ∷ s ⟩        ⟨ i ∣ e₂ ∣ e₁ ∷ s ⟩
  cons-step : ∀ {i e₁ e₂ s} →     CAM→ ⟨ CONS ∷ i ∣ e₂ ∣ e₁ ∷ s ⟩        ⟨ i ∣ e₁ , e₂ ∣ s ⟩
  cur-step  : ∀ {i₁ i₂ e s} →     CAM→ ⟨ CUR i₁ ∷ i₂ ∣ e ∣ s ⟩           ⟨ i₂ ∣ cur i₁ e ∣ s ⟩
  app-step  : ∀ {i₁ i₂ e₁ e₂ s} → CAM→ ⟨ APP ∷ i₁ ∣ cur i₂ e₁ , e₂ ∣ s ⟩ ⟨ i₂ ++ i₁ ∣ e₁ , e₂ ∣ s ⟩
--- COPRODUCT ---
  inl-step  : ∀ {i e s} →         CAM→ ⟨ INL ∷ i ∣ e ∣ s ⟩               ⟨ i ∣ L e ∣ s ⟩
  inr-step  : ∀ {i e s} →         CAM→ ⟨ INR ∷ i ∣ e ∣ s ⟩               ⟨ i ∣ R e ∣ s ⟩
  case1-step : ∀ {i₁ i₂ i e₁ e₂ s} →  CAM→ ⟨ CASE i₁ i₂ ∷ i ∣ e₁ , L e₂ ∣ s ⟩      ⟨ i₁ ++ i ∣ e₁ , e₂ ∣ s ⟩
  case2-step : ∀ {i₁ i₂ i e₁ e₂ s} →  CAM→ ⟨ CASE i₁ i₂ ∷ i ∣ e₁ , R e₂ ∣ s ⟩      ⟨ i₂ ++ i ∣ e₁ , e₂ ∣ s ⟩

data CAM→* : Config → Config → Set where
  refl  : ∀ {M} → CAM→* M M
  trans : ∀ {L N M} → CAM→* M N → CAM→ L M → CAM→* L N

data Finished : Config → Set where
  empty : ∀ {e} → Finished ⟨ [] ∣ e ∣ [] ⟩

data Result (C : Config) : Set where
  done : Finished C → Result C
  stuck : Result C
