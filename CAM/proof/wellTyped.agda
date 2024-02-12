module CAM.proof.wellTyped where

open import Data.Product using (Σ; ∃; Σ-syntax; ∃-syntax) renaming (_,_ to ⦅_,_⦆)

open import CAM.term using (_⊢_; ctxToType)
open import CAM.catComb.eval
open import CAM.catComb.compile
open import CAM.proof.logicalRelation

wellTypedExpressionTerminates : ∀ {Γ A} → (f : Γ ⊢ A) → (s : CatCombValue (ctxToType Γ)) → ∃[ t ] ⟨ ⟦ f ⟧ ∣ s ⟩= t
wellTypedExpressionTerminates f s with propA ⟦ f ⟧ (propB s)
... | ⦅ t , ⦅ x , _ ⦆ ⦆ = ⦅ t , x ⦆
