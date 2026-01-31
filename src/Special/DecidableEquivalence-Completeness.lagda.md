---
title: Completeness of equivalence algorithm
---

```
{-# OPTIONS --guardedness --sized-types #-}
{-# OPTIONS --allow-unsolved-metas #-}

open import Preliminaries.Base
import Preliminaries.Algebra

module Special.DecidableEquivalence-Completeness
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

open import Special.AuxiliaryLemmas R
open import Special.DecidableEquivalence R _≟R_
open import Special.HNF-Algebra R 1≉0 no-zero-divisors _≟R_
open import Special.HNF-Normalised R 1≉0 _≟R_

private variable
    X Y Z : Set
    m n k : ℕ

```


```

complete :
    {p q : Term′ k} →
    p ≈ q →
    --------------------------
    normalise p ≈N normalise q

complete ≈-refl = ≈N-refl
complete (≈-sym p≈q) = ≈N-sym (complete p≈q)
complete (≈-trans p≈q q≈r) = ≈N-trans (complete p≈q) (complete q≈r)
complete (·-cong c≈d p≈q) = ·N-cong c≈d (complete p≈q)
complete (·-one p) = ·N-one p
complete (·-+-distrib _ _ _) = ·-+-distribN _ _ _
complete (+-·-distrib _ _ _) = +-·-distribN _ _ _
complete (·-*-distrib _ _ _) = ·-*-distribN _ _ _
complete (*-·-distrib _ _ _) = *-·-distribN _ _ _
complete (+-cong p₀≈p₁ q₀≈q₁) = +N-cong (complete p₀≈p₁) (complete q₀≈q₁)
complete (+-zeroʳ _) = +N-zeroʳ _
complete (+-assoc p q r) = +N-assoc (normalised p) (normalised q) (normalised r)
complete (+-comm _ _) = +N-comm _ _
complete {p = p} {q} (+-invʳ p₁) = {!   !}
complete {p = p} {q} (*-cong p≈q p≈q₁) = {!   !}
complete {p = p} {q} (*-assoc p₁ q₁ r) = {!   !}
complete {p = p} {q} (*-comm p₁ q₁) = {!   !}
complete {p = p} {q} (*-distribʳ p₁ q₁ r) = {!   !}

```
