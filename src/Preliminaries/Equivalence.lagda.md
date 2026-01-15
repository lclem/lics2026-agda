---
title: Algebraic preliminaries 🚧
---

```
open import Agda.Primitive
open import Relation.Binary.Core
open import Relation.Binary.Structures
open import Relation.Binary.PropositionalEquality
    using (_≡_)
    renaming (refl to ≡-refl; sym to ≡-sym)

module Preliminaries.Equivalence {A : Set} {_≈_ : Rel A lzero} (isEq : IsEquivalence _≈_) where

open IsEquivalence isEq

module Eq where

    infix  1 begin_
    infixr 2 step-≈-∣ step-≈-⟩ step-≈-⟨ step-≈-⟨′ step-≡-⟩ step-≡-⟨
    infix  3 _∎

    ≡→≈ : ∀ {a b} → a ≡ b → a ≈ b
    ≡→≈ ≡-refl = refl

    begin_ : ∀ {f g : A} → f ≈ g → f ≈ g
    begin x≈y = x≈y

    step-≈-∣ : ∀ (f : A) {g : A} → f ≈ g → f ≈ g
    step-≈-∣ _ x≈y = x≈y

    step-≈-⟩ : ∀ (f : A) {g h : A} → g ≈ h → f ≈ g → f ≈ h
    step-≈-⟩ _ y≈z x≈y = trans x≈y y≈z

    step-≈-⟨ : (f : A) {g h : A} → g ≈ h → g ≈ f → f ≈ h
    step-≈-⟨ _ g≈h f≈g = trans (sym f≈g) g≈h

    step-≈-⟨′ = step-≈-⟨

    step-≡-⟩ : ∀ (f : A) {g h : A} → g ≈ h → f ≡ g → f ≈ h
    step-≡-⟩ _ g≈h ≡-refl = g≈h

    step-≡-⟨ : ∀ (f : A) {g h : A} → g ≈ h → g ≡ f → f ≈ h
    step-≡-⟨ _ g≈h ≡-refl = g≈h

    syntax step-≈-∣ x x≈y      =  x ≈⟨⟩ x≈y
    syntax step-≈-⟩ x y≈z x≈y  =  x ≈⟨ x≈y ⟩ y≈z
    syntax step-≈-⟨ x y≈z y≈x  =  x ≈⟨ y≈x ⟨ y≈z
    syntax step-≈-⟨′ x y≈z y≈x =  x ≈⟩ y≈x ⟩ y≈z
    syntax step-≡-⟩ x y≈z x≡y  =  x ≡⟨ x≡y ⟩ y≈z
    syntax step-≡-⟨ x y≈z x≡y  =  x ≡⟨ x≡y ⟨ y≈z

    _∎ : ∀ (f : A) → f ≈ f
    x ∎ = refl
```