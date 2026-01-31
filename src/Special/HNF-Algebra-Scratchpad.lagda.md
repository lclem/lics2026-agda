---
title: Completeness of equivalence algorithm
---

```
{-# OPTIONS --guardedness --sized-types #-}
{-# OPTIONS --allow-unsolved-metas #-}

open import Preliminaries.Base
import Preliminaries.Algebra

module Special.HNF-Algebra-Scratchpad
    (R : CommutativeRing)
    (1≉0 : let open Preliminaries.Algebra R in ¬ (1R ≈R 0R))
    (no-zero-divisors : let open Preliminaries.Algebra R in
        ∀ {a b} → a *R b ≈R 0R → a ≈R 0R ⊎ b ≈R 0R)
    (_≟R_ : let open Preliminaries.Algebra R in Decidable _≈R_)
    where

open Preliminaries.Algebra R
open import General.Terms R hiding (x)
open import Special.Polynomials R
open import Special.HNF R
open import Special.DecidableEquivalence R _≟R_
open import Special.AuxiliaryLemmas R
open import Special.HNF-Normalised R 1≉0 _≟R_

open import Special.HNF-Algebra R 1≉0 no-zero-divisors _≟R_

private variable
    k : ℕ


```
