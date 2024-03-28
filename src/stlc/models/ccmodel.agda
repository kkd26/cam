module stlc.models.ccmodel where

open import stlc.type public
open import context (Type) public

open import stlc.term using (_⊢_)
open import stlc.catComb using (CatComb)
open import stlc.value using (CatCombValue; MachineValue)
open import stlc.catComb.eval using (⟨_∣_⟩=_)
open import stlc.inst

open import config

record Typing (_⊢_ : Context → Type → Set) : Set where
  field
    t    : ∀ {Γ} → Γ ⊢ unit
    pair : ∀ {Γ A B} → Γ ⊢ A → Γ ⊢ B → Γ ⊢ (A × B)
    fst  : ∀ {Γ A B} → Γ ⊢ (A × B) → Γ ⊢ A
    snd  : ∀ {Γ A B} → Γ ⊢ (A × B) → Γ ⊢ B

record CatCombSet (CatComb : Type → Type → Set) : Set where
  field
    !    : ∀ {A} → CatComb A unit
    id   : ∀ {A} → CatComb A A
    _∘_  : ∀ {A B C} → CatComb B C → CatComb A B → CatComb A C
    ⟨_,_⟩ : ∀ {C A B} → CatComb C A → CatComb C B → CatComb C (A × B)
    p₁   : ∀ {A B} → CatComb (A × B) A
    p₂   : ∀ {A B} → CatComb (A × B) B

open CatCombSet

record CatCombValues (CatCombValue : Type → Set) : Set where
  field
    ⟨⟩   : CatCombValue unit
    pair : ∀ {A B} → CatCombValue A → CatCombValue B → CatCombValue (A × B)

open CatCombValues

record CCModel : Set where
  field
    typing   : Typing _⊢_
    catCombs : CatCombSet CatComb
    catCombValues : CatCombValues CatCombValue

open CCModel

modelImpl : CCModel
modelImpl =
  record
    { typing = record { t = _⊢_.⟨⟩ ; pair = _⊢_._,_ ; fst = _⊢_.fst ; snd = _⊢_.snd }
    ; catCombs = record { ! = CatComb.! ; id = CatComb.id ; _∘_ = CatComb._∘_ ; ⟨_,_⟩ = CatComb.⟨_,_⟩ ; p₁ = CatComb.p₁ ; p₂ = CatComb.p₂ }
    ; catCombValues = record { ⟨⟩ = CatCombValue.⟨⟩ ; pair = CatCombValue._,_ }
    }

record Eval (⟨_∣_⟩=_ : ∀ {A B} → CatComb A B → CatCombValue A → CatCombValue B → Set) (model : CCModel) : Set where
  field
    ev-unit : ∀ {A} {s : CatCombValue A} → ⟨ ! (catCombs model) ∣ s ⟩= (⟨⟩ (catCombValues model))
    ev-id : ∀ {A} {s : CatCombValue A} → ⟨ id (catCombs model) ∣ s ⟩= s
    ev-comp : ∀ {A B C s s₁ s₂} {f : CatComb A B} {g : CatComb B C} → ⟨ f ∣ s ⟩= s₁ → ⟨ g ∣ s₁ ⟩= s₂ → ⟨ _∘_ (catCombs model) g f ∣ s ⟩= s₂
    ev-pair : ∀ {A B C} {f : CatComb A B} {g : CatComb A C} {s s₁ s₂} → ⟨ f ∣ s ⟩= s₁ → ⟨ g ∣ s ⟩= s₂ → ⟨ ⟨_,_⟩ (catCombs model) f g ∣ s ⟩= pair (catCombValues model) s₁ s₂
    ev-p1 : ∀ {A B} {s₁ : CatCombValue A} {s₂ : CatCombValue B} → ⟨ p₁ (catCombs model) ∣ pair (catCombValues model) s₁ s₂ ⟩= s₁
    ev-p2 : ∀ {A B} {s₁ : CatCombValue A} {s₂ : CatCombValue B} → ⟨ p₂ (catCombs model) ∣ pair (catCombValues model) s₁ s₂ ⟩= s₂

Config = MakeConfig Inst MachineValue

open import Data.List

record Step (CAM→ : Config → Config → Set) : Set where
  field
    unit-step : ∀ {i e s} →            CAM→ ⟨ UNIT ∷ i ∣ e ∣ s ⟩                     ⟨ i ∣ MachineValue.⟨⟩ ∣ s ⟩
    skip-step : ∀ {i e s} →            CAM→ ⟨ SKIP ∷ i ∣ e ∣ s ⟩                     ⟨ i ∣ e ∣ s ⟩
    car-step  : ∀ {i e₁ e₂ s} →        CAM→ ⟨ CAR ∷ i ∣ MachineValue._,_ e₁ e₂ ∣ s ⟩ ⟨ i ∣ e₁ ∣ s ⟩
    cdr-step  : ∀ {i e₁ e₂ s} →        CAM→ ⟨ CDR ∷ i ∣ MachineValue._,_ e₁ e₂ ∣ s ⟩ ⟨ i ∣ e₂ ∣ s ⟩
    push-step : ∀ {i e s} →            CAM→ ⟨ PUSH ∷ i ∣ e ∣ s ⟩                     ⟨ i ∣ e ∣ e ∷ s ⟩
    swap-step : ∀ {i e₁ e₂ s} →        CAM→ ⟨ SWAP ∷ i ∣ e₁ ∣ e₂ ∷ s ⟩               ⟨ i ∣ e₂ ∣ e₁ ∷ s ⟩
    cons-step : ∀ {i e₁ e₂ s} →        CAM→ ⟨ CONS ∷ i ∣ e₂ ∣ e₁ ∷ s ⟩               ⟨ i ∣ MachineValue._,_ e₁ e₂ ∣ s ⟩

open import Data.Product using (Σ; ∃; Σ-syntax; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⦅_,_⦆; _×_ to _⊗_)

record Logical (_⊩_ : ∀ (A : Type) → CatCombValue A → Set) (model : CCModel) : Set where
  field
    l-unit : unit ⊩ ⟨⟩ (catCombValues model)
    l-pair : ∀ {A B s t} → (A ⊩ s) ⊗ (B ⊩ t) → (A × B) ⊩ pair (catCombValues model) s t

record BiggerModel : Set where
  field
    eval : Eval (⟨_∣_⟩=_) modelImpl

record PropA : Set where
  field
    p-!    : ∀ {A} → CatComb A unit
    p-id   : ∀ {A} → CatComb A A
    p-_∘_  : ∀ {A B C} → CatComb B C → CatComb A B → CatComb A C
    p-⟨_,_⟩ : ∀ {C A B} → CatComb C A → CatComb C B → CatComb C (A × B)
    p-p₁   : ∀ {A B} → CatComb (A × B) A
    p-p₂   : ∀ {A B} → CatComb (A × B) B
