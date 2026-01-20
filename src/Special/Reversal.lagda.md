---
title: Reversal of formal series 🚧
---

```
{-# OPTIONS --guardedness --sized-types #-}
-- {-# OPTIONS --allow-unsolved-metas #-}

open import Preliminaries.Base hiding (_++_)
open import General.ProductRules

module Special.Reversal
    (R : CommutativeRing)
    (Σ : Set)
    (P : ProductRule R)
    where

open import Size
open import Preliminaries.Algebra R
open import Preliminaries.PolyExpr R
    using (PolyExpr; con)
    renaming (subst to P-subst; ⟦_⟧_ to P⟦_⟧_)

open import General.Series R Σ
open import General.Terms R renaming (_+_ to _[+]_; _*_ to _[*]_; _·_ to _[·]_) hiding (x; y)
open import General.Products R Σ
open import General.Reversal R Σ
open import General.ReversalEnd R Σ P

open Product P
-- open Reversal P

private variable
    i : Size
    n : ℕ
```

We show that the properties `P-Rev` and `U-Rev` can be decided
in the case of special products.

```





