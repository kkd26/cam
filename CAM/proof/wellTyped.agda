module CAM.proof.wellTyped where

open import CAM.term
open import CAM.catComb
open import CAM.catCombProps
open import CAM.value

open import Data.Product using (Σ; ∃; Σ-syntax; ∃-syntax) renaming (_,_ to ⦅_,_⦆)
open import CAM.proof.logicalRelation

wellTypedExpressionTerminates : ∀ {Γ A} → (f : Γ ⊢ A) → (s : CatCombValue (ctxToType Γ)) → ∃[ t ] ⟨ ⟦ f ⟧ ∣ s ⟩= t
wellTypedExpressionTerminates f s with propA ⟦ f ⟧ (propB s)
... | ⦅ t , ⦅ fst₁ , snd₁ ⦆ ⦆ = ⦅ t , fst₁ ⦆
