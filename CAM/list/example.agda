module CAM.list.example where

open import Data.Nat
open import Data.List

open import CAM.list.term
open import CAM.list.compile
open import CAM.list.run

nat : Type
nat = list unit

z : ∀ {Γ} → Γ ⊢ nat
z = []

infixr 7 s_

s_ : ∀ {Γ} → Γ ⊢ nat → Γ ⊢ nat
s x = ⟨⟩ ⦂ x

module Utils where
  len : MachineValue → ℕ
  len [] = zero
  len (⟨⟩ ⦂ t) = suc (len t)
  len _ = zero

  toNat : ∀ {Γ} → ℕ → Γ ⊢ nat
  toNat zero = z
  toNat (suc x) = s (toNat x)

  decode : Result → List ℕ
  decode (done []) = []
  decode (done (x₁ ⦂ x₂)) = len x₁ ∷ decode (done x₂)
  decode _ = []

  encode : List ℕ → ∅ ⊢ list nat
  encode l = foldr _⦂_ [] (map toNat l)

--- Example 1 - increment numbers in list ---
x : ∅ ⊢ list nat
x = []

r : ∅ , (nat × list nat) ⊢ list nat
r = s fst (` Z) ⦂ snd (` Z)

list012 : ∅ ⊢ list nat
list012 = Utils.encode (0 ∷ 1 ∷ 2 ∷ [])

map+1 : ∅ ⊢ list nat
map+1 = it x r list012

inst1 : List Inst
inst1 = compile map+1

result1 : Result
result1 = run 1000 ⟨ inst1 ∣ ⟨⟩ ∣ [] ⟩

res1 : List ℕ
res1 = Utils.decode result1

--- Example 2 - reverse list ---
xₐ : ∀ {Γ A} → Γ , (A × list A) ⊢ list A
xₐ = fst (` Z) ⦂ []

rₐ : ∀ {Γ A} → Γ , (A × list A) , (A × list A) ⊢ list A
rₐ = fst (` Z) ⦂ snd (` Z)

append : ∀ {Γ A} → Γ , (A × list A) ⊢ list A
append = it xₐ rₐ (snd (` Z))

x₁ : ∅ , list nat ⊢ list nat
x₁ = []

r₁ : ∅ , list nat , (nat × list nat) ⊢ list nat
r₁ = (ƛ append) · (` Z)

rev : ∅ , list nat ⊢ list nat
rev = it x₁ r₁ (` Z)

rev012 : ∅ ⊢ list nat
rev012 = (ƛ rev)  · list012

inst2 : List Inst
inst2 = compile rev012

result2 : Result
result2 = run 1000 ⟨ inst2 ∣ ⟨⟩ ∣ [] ⟩

res2 : List ℕ
res2 = Utils.decode result2
