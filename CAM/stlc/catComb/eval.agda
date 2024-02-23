module CAM.stlc.catComb.eval where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong)

open import CAM.stlc.catComb public
open import CAM.stlc.value using (CatCombValue) public

open CatCombValue

data ⟨_∣_⟩=_ : ∀ {A B} → CatComb A B → CatCombValue A → CatCombValue B → Set where
  ev-unit : ∀ {A} {s : CatCombValue A} → ⟨ ! ∣ s ⟩= ⟨⟩
  ev-nat : ∀ {A x} {s : CatCombValue A} → ⟨ nat x ∣ s ⟩= (`nat x)
  ev-id : ∀ {A} {s : CatCombValue A} → ⟨ id ∣ s ⟩= s
  ev-comp : ∀ {A B C s s₁ s₂} {f : CatComb A B} {g : CatComb B C} → ⟨ f ∣ s ⟩= s₁ → ⟨ g ∣ s₁ ⟩= s₂ → ⟨ g ∘ f ∣ s ⟩= s₂
  ev-pair : ∀ {A B C} {f : CatComb A B} {g : CatComb A C} {s s₁ s₂} → ⟨ f ∣ s ⟩= s₁ → ⟨ g ∣ s ⟩= s₂ → ⟨ ⟨ f , g ⟩ ∣ s ⟩= (s₁ , s₂)
  ev-p1 : ∀ {A B} {s₁ : CatCombValue A} {s₂ : CatCombValue B} → ⟨ p₁ ∣ s₁ , s₂ ⟩= s₁
  ev-p2 : ∀ {A B} {s₁ : CatCombValue A} {s₂ : CatCombValue B} → ⟨ p₂ ∣ s₁ , s₂ ⟩= s₂
  ev-cur : ∀ {A B C s} {f : CatComb (A × B) C} → ⟨ cur f ∣ s ⟩= cur f s
  ev-app : ∀ {A B C s t s₁} {f : CatComb (A × B) C} → ⟨ f ∣ s , t ⟩= s₁ → ⟨ app ∣ cur f s , t ⟩= s₁
--- COPRODUCT ---
  ev-copair1 : ∀ {A B C D s₁ s₂ t} {f : CatComb (A × B) D} {g : CatComb (A × C) D} → ⟨ f ∣ s₁ , s₂ ⟩= t → ⟨ [_,_] f g ∣ s₁ , L s₂ ⟩= t
  ev-copair2 : ∀ {A B C D s₁ s₂ t} {f : CatComb (A × B) D} {g : CatComb (A × C) D} → ⟨ g ∣ s₁ , s₂ ⟩= t → ⟨ [_,_] f g ∣ s₁ , R s₂ ⟩= t
  ev-i1 : ∀ {A B} {s : CatCombValue A} → ⟨ i1 {A} {B} ∣ s ⟩= (L s)
  ev-i2 : ∀ {A B} {s : CatCombValue B} → ⟨ i2 {A} {B} ∣ s ⟩= (R s)

uniqueness : ∀ {A B s t t'} {f : CatComb A B} → ⟨ f ∣ s ⟩= t → ⟨ f ∣ s ⟩= t' → t ≡ t'
uniqueness ev-unit ev-unit = refl
uniqueness ev-nat ev-nat = refl
uniqueness ev-id ev-id = refl
uniqueness (ev-comp x x₁) (ev-comp y y₁) rewrite uniqueness x y = uniqueness x₁ y₁
uniqueness (ev-pair x x₁) (ev-pair {s₁ = s₁} y y₁) with uniqueness x y | uniqueness x₁ y₁
... | z | w rewrite z = cong (s₁ ,_) w
uniqueness ev-p1 ev-p1 = refl
uniqueness ev-p2 ev-p2 = refl
uniqueness ev-cur ev-cur = refl
uniqueness (ev-app x) (ev-app y) = uniqueness x y
--- COPRODUCT ---
uniqueness (ev-copair1 x) (ev-copair1 y) = uniqueness x y
uniqueness (ev-copair2 x) (ev-copair2 y) = uniqueness x y
uniqueness ev-i1 ev-i1 = refl
uniqueness ev-i2 ev-i2 = refl
