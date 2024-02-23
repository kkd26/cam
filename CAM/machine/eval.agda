open import CAM.config

module CAM.machine.eval {Inst Value} (CAM→ : MakeConfig Inst Value → MakeConfig Inst Value → Set) where

open import Data.List
open import CAM.config public

Config = MakeConfig Inst Value

data CAM→* : Config → Config → Set where
  refl  : ∀ {M} → CAM→* M M
  trans : ∀ {L N M} → CAM→* M N → CAM→ L M → CAM→* L N

data Finished : Config → Set where
  empty : ∀ {e} → Finished ⟨ [] ∣ e ∣ [] ⟩

data Result (C : Config) : Set where
  done : Finished C → Result C
  stuck : Result C

Steps = List Config

createSteps : ∀ {A B} → CAM→* A B → Steps
createSteps {B = B} refl = [ B ]
createSteps {A} (trans x _) = A ∷ (createSteps x)
