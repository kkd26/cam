module CAM.proof.logicalRelation where

open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; ∃; Σ-syntax; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⦅_,_⦆; _×_ to _⊗_)

open import CAM.catComb.eval
open import CAM.catComb.compile
open import CAM.helper.iso using (_⇔_)

open Type
open CatCombValue

infix 4 _⊩_
infix 4 _⊩'_

data _⊩_ : ∀ (A : Type) → CatCombValue A → Set
_⊩'_ : ∀ (A : Type) → CatCombValue A → Set

data _⊩_ where
  unit : unit ⊩ ⟨⟩
  nat : ∀ {x} → nat ⊩ `nat x
  pair : ∀ {A B s t} → (A ⊩ s) ⊗ (B ⊩ t) → A × B ⊩ s , t
  cur : ∀ {A A₁ A₂ s} {f : CatComb (A × A₁) A₂} → (∀ {s₁} → A₁ ⊩' s₁ → ∃[ t ] ⟨ f ∣ s , s₁ ⟩= t ⊗ A₂ ⊩ t) → A₁ ⇒ A₂ ⊩ cur f s

unit ⊩' ⟨⟩ = ⊤
nat ⊩' `nat x = ⊤
(v × v₁) ⊩' (s , s₁) = (v ⊩' s) ⊗ (v₁ ⊩' s₁)
(A₁ ⇒ A₂) ⊩' cur f s = ∀ {s₁} → A₁ ⊩' s₁ → ∃[ t ] ⟨ f ∣ s , s₁ ⟩= t ⊗ (A₂ ⊩' t)

⊩⇔⊩' : ∀ {A s} → A ⊩ s ⇔ A ⊩' s
⊩⇔⊩' =
  record
    { to = to
    ; from = from
    }
  where
    to : ∀ {A s} → A ⊩ s → A ⊩' s
    to {.unit} {⟨⟩} _ = tt
    to {.nat} {`nat _} _ = tt
    to {.(_ × _)} {_ , _} (pair ⦅ x₁ , x₂ ⦆) = ⦅ to x₁ , to x₂ ⦆
    to {.(_ ⇒ _)} {cur _ _} (cur f) s with f s
    ... | ⦅ t , ⦅ s₁ , s₂ ⦆ ⦆ = ⦅ t , ⦅ s₁ , (to s₂) ⦆ ⦆

    from : ∀ {A s} → A ⊩' s → A ⊩ s
    from {.unit} {⟨⟩} _ = unit
    from {.nat} {`nat _} _ = nat
    from {.(_ × _)} {_ , _} x = pair ⦅ from (proj₁ x) , from (proj₂ x) ⦆
    from {.(_ ⇒ _)} {cur _ _} f = cur λ s → ⦅ proj₁ (f s) , ⦅ proj₁ (proj₂ (f s)) , from (proj₂ (proj₂ (f s))) ⦆ ⦆

propA : ∀ {A B s} → (f : CatComb A B) → A ⊩ s → ∃[ t ] ⟨ f ∣ s ⟩= t ⊗ (B ⊩ t)
propA ! _ = ⦅ ⟨⟩ , ⦅ ev-unit , unit ⦆ ⦆
propA (nat n) _ = ⦅ (`nat n) , ⦅ ev-nat , nat ⦆ ⦆
propA {s = s} id x = ⦅ s , ⦅ ev-id , x ⦆ ⦆
propA (f ∘ g) x with propA g x
... | ⦅ _ , ⦅ x₁ , x₂ ⦆ ⦆ with propA f x₂
... | ⦅ t , ⦅ y₁ , y₂ ⦆ ⦆ = ⦅ t , ⦅ ev-comp x₁ y₁ , y₂ ⦆ ⦆
propA ⟨ f , g ⟩ x with propA f x | propA g x
... | ⦅ t₁ , ⦅ x₁ , x₂ ⦆ ⦆ | ⦅ t₂ , ⦅ y₁ , y₂ ⦆ ⦆ = ⦅ (t₁ , t₂) , (⦅ ev-pair x₁ y₁ , pair ⦅ x₂ , y₂ ⦆ ⦆) ⦆
propA {s = s₁ , _} p₁ (pair ⦅ fst₁ , snd₁ ⦆) = ⦅ s₁ , ⦅ ev-p1 , fst₁ ⦆ ⦆
propA {s = _ , s₂} p₂ (pair ⦅ fst₁ , snd₁ ⦆) = ⦅ s₂ , ⦅ ev-p2 , snd₁ ⦆ ⦆
propA {s = s} (cur f) x = ⦅ (cur f s) , ⦅ ev-cur , cur (λ {s₁ → propA f (pair ⦅ x , _⇔_.from ⊩⇔⊩' s₁ ⦆)} ) ⦆ ⦆
propA app (pair ⦅ cur f , x ⦆) with f (_⇔_.to ⊩⇔⊩' x)
... | ⦅ t , ⦅ x₁ , x₂ ⦆ ⦆ = ⦅ t , ⦅ ev-app x₁ , x₂ ⦆ ⦆

propB : ∀ {A} → (s : CatCombValue A) → A ⊩ s
propB ⟨⟩ = unit
propB (`nat _) = nat
propB {A₁ × A₂} (s₁ , s₂) = pair ⦅ propB s₁ , propB s₂ ⦆
propB {A ⇒ B} (cur f s) = cur λ { s₁ → propA f (pair ⦅ propB s , (_⇔_.from ⊩⇔⊩' s₁) ⦆) }
