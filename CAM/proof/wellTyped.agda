module CAM.proof.wellTyped where

open import Data.Nat using (ℕ)

open import CAM.term
open import CAM.catComb
open import CAM.catCombProps
open import CAM.value
open import CAM.step

open import Data.Product using (Σ; ∃; Σ-syntax; ∃-syntax) renaming (_,_ to ⦅_,_⦆)

wellTypedExpressionTerminates : ∀ {Γ A} → (f : Γ ⊢ A) → (s : CatCombValue (ctxToType Γ)) → ∃[ t ] ⟨ ⟦ f ⟧ ∣ s ⟩= t
wellTypedExpressionTerminates = {!!}
