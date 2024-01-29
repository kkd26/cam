module CAM.step where

open import Data.List

open import CAM.inst
open import CAM.config public
open import CAM.value

data CAM-step : Config → Config → Set where
  natE-red : ∀ {C S x} →      CAM-step ⟨ (NAT x) ∷ C ∣ ⟨⟩ ∣ S ⟩       ⟨ C ∣ `nat x ∣ S ⟩
  nat-red :  ∀ {C s S x} →    CAM-step ⟨ (NAT x) ∷ C ∣ s ∣ S ⟩        ⟨ C ∣ s , `nat x ∣ S ⟩
  skip-red : ∀ {C s S} →      CAM-step ⟨ SKIP ∷ C ∣ s ∣ S ⟩           ⟨ C ∣ s ∣ S ⟩ 
  car-red  : ∀ {C s₁ s₂ S} →  CAM-step ⟨ CAR ∷ C ∣ s₁ , s₂ ∣ S ⟩      ⟨ C ∣ s₁ ∣ S ⟩
  cdr-red  : ∀ {C s₁ s₂ S} →  CAM-step ⟨ CDR ∷ C ∣ s₁ , s₂ ∣ S ⟩      ⟨ C ∣ s₂ ∣ S ⟩
  push-red : ∀ {C s S} →      CAM-step ⟨ PUSH ∷ C ∣ s ∣ S ⟩           ⟨ C ∣ s ∣ s ∷ S ⟩
  swap-red : ∀ {C s₁ s₂ S} →  CAM-step ⟨ SWAP ∷ C ∣ s₁ ∣ s₂ ∷ S ⟩     ⟨ C ∣ s₂ ∣ s₁ ∷ S ⟩
  cons-red : ∀ {C s₁ s₂ S} →  CAM-step ⟨ CONS ∷ C ∣ s₂ ∣ s₁ ∷ S ⟩     ⟨ C ∣ s₁ , s₂ ∣ S ⟩
  cur-red  : ∀ {C C' s S} →   CAM-step ⟨ cur C ∷ C' ∣ s ∣ S ⟩         ⟨ C' ∣ cur C s ∣ S ⟩
  app-red  : ∀ {C C' s t S} → CAM-step ⟨ app ∷ C' ∣ cur C s , t ∣ S ⟩ ⟨ C ++ C' ∣ s , t ∣ S ⟩

data CAM-tr : Config → Config → Set where
  refl  : ∀ {M} → CAM-tr M M
  trans : ∀ {L N M} → CAM-tr M N → CAM-step L M → CAM-tr L N 

data Finished : Config → Set where
  empty : ∀ {env} → Finished ⟨ [] ∣ env ∣ [] ⟩

data Result (C : Config) : Set where
  done : Finished C → Result C
  stuck : Result C


