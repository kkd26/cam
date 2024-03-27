module stlc.proof.wellTyped where

open import Data.Product using (Σ; ∃; Σ-syntax; ∃-syntax) renaming (_,_ to ⦅_,_⦆)

open import stlc.term
open import stlc.catComb.properities
open import stlc.proof.termination
open import stlc.step public
open import machine.eval (CAM→)

wellTypedExpressionTerminates : ∀ {Γ A} → (f : Γ ⊢ A) → (s : CatCombValue (ctxToType Γ)) → ∃[ t ] ⟨ ⟦ f ⟧ ∣ s ⟩= t
wellTypedExpressionTerminates f s with propA ⟦ f ⟧ (propB s)
... | ⦅ t , ⦅ x , _ ⦆ ⦆ = ⦅ t , x ⦆

eval : ∀ {A} → (f : ∅ ⊢ A) → Steps
eval f with wellTypedExpressionTerminates f ⟨⟩
... | ⦅ t , e ⦆ with catCombEval→machineEval e
... | steps = createSteps steps
