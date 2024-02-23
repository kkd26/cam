module CAM.stlc.proof.wellTyped where

open import Data.Product using (Σ; ∃; Σ-syntax; ∃-syntax) renaming (_,_ to ⦅_,_⦆)

open import CAM.stlc.term
open import CAM.stlc.catComb.properities
open import CAM.stlc.proof.termination
open import CAM.stlc.step public
open import CAM.machine.eval (CAM→)

wellTypedExpressionTerminates : ∀ {Γ A} → (f : Γ ⊢ A) → (s : CatCombValue (ctxToType Γ)) → ∃[ t ] ⟨ ⟦ f ⟧ ∣ s ⟩= t
wellTypedExpressionTerminates f s with propA ⟦ f ⟧ (propB s)
... | ⦅ t , ⦅ x , _ ⦆ ⦆ = ⦅ t , x ⦆

eval : ∀ {A} → (f : ∅ ⊢ A) → Steps
eval f with wellTypedExpressionTerminates f ⟨⟩
... | ⦅ t , e ⦆ with catCombEval→machineEval e
... | steps = createSteps steps
