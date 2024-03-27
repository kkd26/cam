module list.eval where

open import list.catComb public
open import list.value using (CatCombValue) public

open CatCombValue

data ⟨_∣_⟩=_ : ∀ {A B} → CatComb A B → CatCombValue A → CatCombValue B → Set where
  ev-unit : ∀ {A} {s : CatCombValue A} → ⟨ ! ∣ s ⟩= ⟨⟩
  ev-id : ∀ {A} {s : CatCombValue A} → ⟨ id ∣ s ⟩= s
  ev-comp : ∀ {A B C s s₁ s₂} {f : CatComb A B} {g : CatComb B C} → ⟨ f ∣ s ⟩= s₁ → ⟨ g ∣ s₁ ⟩= s₂ → ⟨ g ∘ f ∣ s ⟩= s₂
  ev-pair : ∀ {A B C} {f : CatComb A B} {g : CatComb A C} {s s₁ s₂} → ⟨ f ∣ s ⟩= s₁ → ⟨ g ∣ s ⟩= s₂ → ⟨ ⟨ f , g ⟩ ∣ s ⟩= (s₁ , s₂)
  ev-p1 : ∀ {A B} {s₁ : CatCombValue A} {s₂ : CatCombValue B} → ⟨ p₁ ∣ s₁ , s₂ ⟩= s₁
  ev-p2 : ∀ {A B} {s₁ : CatCombValue A} {s₂ : CatCombValue B} → ⟨ p₂ ∣ s₁ , s₂ ⟩= s₂
  ev-cur : ∀ {A B C s} {f : CatComb (A × B) C} → ⟨ cur f ∣ s ⟩= cur f s
  ev-app : ∀ {A B C s t s₁} {f : CatComb (A × B) C} → ⟨ f ∣ s , t ⟩= s₁ → ⟨ app ∣ cur f s , t ⟩= s₁
--- LIST OBJECT ---
  ev-nil : ∀ {A} {s : CatCombValue A} → ⟨ nil {A} ∣ ⟨⟩ ⟩= []
  ev-cons : ∀ {A} {h : CatCombValue A} {t : CatCombValue (list A)} → ⟨ cons ∣ h , t ⟩= (h ⦂ t)
  ev-it-nil : ∀ {A X P p s} {x : CatComb P X} {r : CatComb (P × (A × X)) X} → ⟨ x ∣ p ⟩= s → ⟨ it x r ∣ [] , p ⟩= s
  ev-it-cons : ∀ {A X P p s s' h t} {x : CatComb P X} {r : CatComb (P × (A × X)) X} → ⟨ it x r ∣ t , p ⟩= s' →  ⟨ r ∣ p , (h , s') ⟩= s → ⟨ it x r ∣ h ⦂ t , p ⟩= s
