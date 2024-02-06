module CAM.proof.logicalRelation where

open import CAM.catCombProps
open import CAM.catComb
open import CAM.term
open import CAM.value

open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; ∃; Σ-syntax; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⦅_,_⦆; _×_ to _⊗_)

infix 4 _⊩_
infix 4 _⊩'_

data _⊩_ : ∀ {A} → (f : CatCombValue A) → Type → Set
_⊩'_ : ∀ {A} → (f : CatCombValue A) → Type → Set

data _⊩_ where
  unit : ⟨⟩ ⊩ unit
  nat : ∀ {x} → `nat x ⊩ nat
  pair : ∀ {A B} {s : CatCombValue A} {t : CatCombValue B} → s ⊩ A ⊗ t ⊩ B → s , t ⊩ A × B
  cur : ∀ {A B₁ B₂ s} {f : CatComb ((A × B₁) ⇒ B₂)} → (∀ {s₁} → s₁ ⊩' B₁ → ∃[ t ] ⟨ f ∣ s , s₁ ⟩= t ⊗ t ⊩ B₂) → cur f s ⊩ B₁ ⇒ B₂

⟨⟩ ⊩' unit = ⊤
(`nat x) ⊩' nat = ⊤
(s , s₁) ⊩' (v × v₁) = s ⊩' v ⊗ s₁ ⊩' v₁
cur f s ⊩' (B₁ ⇒ B₂) = (∀ {s₁} → s₁ ⊩' B₁ → ∃[ t ] ⟨ f ∣ s , s₁ ⟩= t ⊗ t ⊩' B₂)
_ ⊩' _ = ⊥

sound' : ∀ {A} {s : CatCombValue A} → s ⊩ A → s ⊩' A
sound' {.unit} {⟨⟩} x = tt
sound' {.nat} {`nat x₁} x = tt
sound' {.(_ × _)} {s , s₁} (pair ⦅ fst₁ , snd₁ ⦆) = ⦅ sound' fst₁ , sound' snd₁ ⦆
sound' {.(_ ⇒ _)} {cur x₁ s} (cur x) x₂ with x x₂
... | ⦅ t , ⦅ fst₁ , snd₁ ⦆ ⦆ = ⦅ t , ⦅ fst₁ , (sound' snd₁) ⦆ ⦆

sound : ∀ {A} {s : CatCombValue A} → s ⊩' A → s ⊩ A
sound {.unit} {⟨⟩} x = unit
sound {.nat} {`nat x₁} x = nat
sound {.(_ × _)} {s , s₁} x = pair ⦅ sound (proj₁ x) , sound (proj₂ x) ⦆
sound {.(_ ⇒ _)} {cur x₁ s} x = cur λ x₂ → ⦅ proj₁ (x x₂) , ⦅ proj₁ (proj₂ (x x₂)) , sound (proj₂ (proj₂ (x x₂))) ⦆ ⦆

propA : ∀ {A B s} → (f : CatComb (A ⇒ B)) → s ⊩ A → ∃[ t ] ⟨ f ∣ s ⟩= t ⊗ t ⊩ B
propA (nat x) _ = ⦅ (`nat x) , ⦅ ev-nat , nat ⦆ ⦆
propA {s = s} id x = ⦅ s , ⦅ ev-id , x ⦆ ⦆
propA {s = s} (x ∘ x₁) x₂ with propA {s = s} x₁ x₂
... | ⦅ fst₁ , snd₁ ⦆ with propA {s = fst₁} x (proj₂ snd₁)
... | ⦅ fst₂ , snd₂ ⦆ = ⦅ fst₂ , (⦅ ev-comp (proj₁ snd₁) (proj₁ snd₂) , proj₂ snd₂ ⦆) ⦆
propA {s = s} ⟨ x , x₁ ⟩ y with propA {s = s} x y | propA {s = s} x₁ y
... | ⦅ fst₁ , snd₁ ⦆ | ⦅ fst₂ , snd₂ ⦆ = ⦅ (fst₁ , fst₂) , (⦅ ev-pair (proj₁ snd₁) (proj₁ snd₂) , pair ⦅ (proj₂ snd₁) , (proj₂ snd₂) ⦆ ⦆) ⦆
propA {s = s₁ , s₂} p₁ (pair ⦅ fst₁ , snd₁ ⦆) = ⦅ s₁ , ⦅ ev-p1 , fst₁ ⦆ ⦆
propA {s = s₁ , s₂} p₂ (pair ⦅ fst₁ , snd₁ ⦆) = ⦅ s₂ , ⦅ ev-p2 , snd₁ ⦆ ⦆
propA {s = s} (cur x) y = ⦅ (cur x s) , ⦅ ev-cur , cur (λ {s₁ → propA x (pair ⦅ y , (sound s₁) ⦆)} ) ⦆ ⦆
propA {s = cur x s , s₁} app (pair ⦅ cur x₁ , snd₁ ⦆) with x₁ (sound' snd₁)
... | ⦅ t , ⦅ fst₁ , snd₂ ⦆ ⦆ = ⦅ t , ⦅ ev-app fst₁ , snd₂ ⦆ ⦆

propB : ∀ {A} → (s : CatCombValue A) → s ⊩ A
propB ⟨⟩ = unit
propB (`nat x) = nat
propB {A₁ × A₂} (s₁ , s₂) = pair ⦅ propB s₁ , propB s₂ ⦆
propB {A ⇒ B} (cur x s) = cur λ { s₁ → propA x (pair ⦅ propB s , (sound s₁) ⦆) }
