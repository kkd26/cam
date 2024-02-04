module CAM.step where

open import Data.List

open import CAM.inst public
open import CAM.config public
open import CAM.value public

data CAM-step : Config → Config → Set where
  nat-red :  ∀ {i e s x} →       CAM-step ⟨ (NAT x) ∷ i ∣ e ∣ s ⟩           ⟨ i ∣ e , `nat x ∣ s ⟩
  skip-red : ∀ {i e s} →         CAM-step ⟨ SKIP ∷ i ∣ e ∣ s ⟩              ⟨ i ∣ e ∣ s ⟩ 
  car-red  : ∀ {i e₁ e₂ s} →     CAM-step ⟨ CAR ∷ i ∣ e₁ , e₂ ∣ s ⟩         ⟨ i ∣ e₁ ∣ s ⟩
  cdr-red  : ∀ {i e₁ e₂ s} →     CAM-step ⟨ CDR ∷ i ∣ e₁ , e₂ ∣ s ⟩         ⟨ i ∣ e₂ ∣ s ⟩
  push-red : ∀ {i e s} →         CAM-step ⟨ PUSH ∷ i ∣ e ∣ s ⟩              ⟨ i ∣ e ∣ e ∷ s ⟩
  swap-red : ∀ {i e₁ e₂ s} →     CAM-step ⟨ SWAP ∷ i ∣ e₁ ∣ e₂ ∷ s ⟩        ⟨ i ∣ e₂ ∣ e₁ ∷ s ⟩
  cons-red : ∀ {i e₁ e₂ s} →     CAM-step ⟨ CONS ∷ i ∣ e₂ ∣ e₁ ∷ s ⟩        ⟨ i ∣ e₁ , e₂ ∣ s ⟩
  cur-red  : ∀ {i₁ i₂ e s} →     CAM-step ⟨ CUR i₁ ∷ i₂ ∣ e ∣ s ⟩           ⟨ i₂ ∣ cur i₁ e ∣ s ⟩
  app-red  : ∀ {i₁ i₂ e₁ e₂ s} → CAM-step ⟨ APP ∷ i₁ ∣ cur i₂ e₁ , e₂ ∣ s ⟩ ⟨ i₂ ++ i₁ ∣ e₁ , e₂ ∣ s ⟩

data CAM-tr : Config → Config → Set where
  refl  : ∀ {M} → CAM-tr M M
  trans : ∀ {L N M} → CAM-tr M N → CAM-step L M → CAM-tr L N 

data Finished : Config → Set where
  empty : ∀ {e} → Finished ⟨ [] ∣ e ∣ [] ⟩

data Result (C : Config) : Set where
  done : Finished C → Result C
  stuck : Result C
