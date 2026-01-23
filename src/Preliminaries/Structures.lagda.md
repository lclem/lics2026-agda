---
title: Auxiliary algebraic structures
---

```
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Structures using (IsEquivalence)

module Preliminaries.Structures
  {a ℓ} {A : Set a}  -- The underlying set
  (_≈_ : Rel A ℓ)    -- The underlying equality relation
  where

-- The file is divided into sections depending on the arities of the
-- components of the algebraic structure.

open import Algebra.Core using (Op₁; Op₂)
open import Algebra.Definitions _≈_
import Algebra.Consequences.Setoid as Consequences
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Level using (_⊔_)

open import Algebra.Structures (_≈_)

record IsCommutativeRingWithoutOne
  (+ * : Op₂ A) (- : Op₁ A) (0# : A) : Set (a ⊔ ℓ) where
  field
    isRingWithoutOne : IsRingWithoutOne + * - 0#
    *-comm : Commutative *

  open IsRingWithoutOne isRingWithoutOne public

open IsCommutativeRingWithoutOne public

--   isCommutativeSemiring : IsCommutativeSemiring + * 0# 1#
--   isCommutativeSemiring = record
--     { isSemiring = isSemiring
--     ; *-comm = *-comm
--     }
```