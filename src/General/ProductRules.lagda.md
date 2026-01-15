---
title: Products of power series 🚧
---

```
{-# OPTIONS --guardedness --sized-types #-}
--  --allow-unsolved-metas

open import Preliminaries.Base

module General.ProductRules
    (R : CommutativeRing)
    where

open import Size
private variable i : Size

open import Preliminaries.Algebra R
open import Preliminaries.Vector
```

# Examples

```
module Examples (Σ : Set)  where

    open import General.Series R Σ
```

## Cauchy product

```
    infixr 7 _×_
    _×_ : A ⟪ Σ ⟫ i → A ⟪ Σ ⟫ i → A ⟪ Σ ⟫ i
    ν (f × g) = ν f *R ν g
    δ (f × g) a = δ f a × g + ν f · δ g a
```

## Hadamard product

```
    infixr 7 _⊙_
    _⊙_ : A ⟪ Σ ⟫ → A ⟪ Σ ⟫ → A ⟪ Σ ⟫
    ν (f ⊙ g) = ν f *R ν g
    δ (f ⊙ g) a = δ f a ⊙ δ g a
```

## Shuffle product

```
    infixr 7 _⧢_
    _⧢_ : A ⟪ Σ ⟫ i → A ⟪ Σ ⟫ i → A ⟪ Σ ⟫ i
    ν (f ⧢ g) = ν f *R ν g
    δ (f ⧢ g) a = δ f a ⧢ g + f ⧢ δ g a
```

## Infiltration product

```
    infixr 7 _↑_
    _↑_ : A ⟪ Σ ⟫ i → A ⟪ Σ ⟫ i → A ⟪ Σ ⟫ i
    ν (f ↑ g) = ν f *R ν g
    δ (f ↑ g) a = δ f a ↑ g + f ↑ δ g a + δ f a ↑ δ g a
```

```
open import General.Terms R
record ProductRule : Set where
    constructor mkProductRule
    field
        P : Term (Fin 4)
```

```
ruleZero : ProductRule
ruleZero = 
    record {
        P = 0T
    }
    
ruleConst : ProductRule
ruleConst = 
    record {
        P = x * y
    }

ruleHadamard : ProductRule
ruleHadamard =
    record {
        P = x′ * y′
    }

ruleShuffle : ProductRule
ruleShuffle =
    record {
        P = x′ * y + x * y′
    }

ruleInfiltration : ProductRule
ruleInfiltration =
    record {
        P = x′ * y + x * y′ + x′ * y′
    }
```