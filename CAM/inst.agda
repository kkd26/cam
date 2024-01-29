module CAM.inst where

open import Data.Nat using (ℕ)
open import Data.List
open import CAM.term using (_⊢_)
open import CAM.catComb

data Inst : Set where
  NAT : ℕ → Inst
  SKIP : Inst
  CAR : Inst
  CDR : Inst
  app : Inst
  cur : List Inst → Inst
  PUSH : Inst
  SWAP : Inst
  CONS : Inst

code : CatComb → List Inst
code (CatComb.nat n) = [ NAT n ]
code CatComb.id = [ SKIP ]
code (g ∘ f) = code f ++ code g
code ⟨ f , g ⟩ = PUSH ∷ code f ++ [ SWAP ] ++ code g ++ [ CONS ]
code p₁ = [ CAR ]
code p₂ = [ CDR ]
code (cur f) = [ cur (code f) ]
code CatComb.app = [ app ]

compile : ∀ {Γ A} → Γ ⊢ A → List Inst
compile t = code ⟦ t ⟧
