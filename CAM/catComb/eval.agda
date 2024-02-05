module CAM.catComb.eval where

open import CAM.catComb
open import CAM.value using (CatCombValue) public

open Type
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
