---
title: "Special product rules"
---

```
{-# OPTIONS --guardedness --sized-types #-}

open import Preliminaries.Base
module Special.ProductRules (R : CommutativeRing) where

open import Preliminaries.Algebra R
open import General.Terms R
open import General.ProductRules R
open import Special.Polynomials R

open AlgebraicProperties
```

These are the axioms satisfied by special product rules.

```
record Special (P : ProductRule) : Set where

    field

        P-add :
            [ P ]⟨ x + y , x′ + y′ , z , z′ ⟩ ≈₆
            [ P ]⟨ x , x′ , z , z′ ⟩ + [ P ]⟨ y , y′ , z , z′ ⟩
        
        P-assoc :
            [ P ]⟨ x * y , [ P ]⟨ x , x′ , y , y′ ⟩ ,  z , z′ ⟩ ≈₆
            [ P ]⟨ x , x′ , y * z , [ P ]⟨ y , y′ , z , z′ ⟩ ⟩

        P-comm :
            [ P ]⟨ x , x′ , y , y′ ⟩ ≈₄
            [ P ]⟨ y , y′ , x , x′ ⟩

        P-compat : ∀ c →
            [ P ]⟨ c · x , c · x′ , y , y′ ⟩ ≈₄
            c · [ P ]⟨ x , x′ , y , y′ ⟩

open Special public
```
