---
title: Reversal of formal series
---

This was used to automatically prove the reversal homomorphism property for simple product rules

```
{-# OPTIONS --guardedness --sized-types #-}

open import Preliminaries.Base hiding (_++_)

module Special.ReversalCalc where -- (R : CommutativeRing) where

open import General.Terms ringℤ hiding (x; y; t)

open import Special.Polynomials ringℤ
open import Special.HNF ringℤ hiding (x)
open import Special.DecidableEquivalence ringℤ _≟ℤ_

data Σ : Set where
    a b : Σ

data Σ′ : Set where
    ε a b : Σ′

data X : Set where
    _x_ _y_ : Σ′ → Σ′ → X
    α β γ : X

Δˡ Δʳ : Σ → X → Term X
Δˡ a (ε x c) = var (a x c)
Δˡ a (ε y c) = var (a y c)
Δˡ _ _ = 0T -- unused cases

Δʳ b (c x ε) = var (c x b)
Δʳ b (c y ε) = var (c y b)
Δʳ _ _ = 0T -- unused cases

infix 20 _↑_
_↑_ : (Δ : Subst X X) → Term X → Term X
Δ ↑ 0T = 0T
Δ ↑ (var z) = Δ z
Δ ↑ (c · q) = c · Δ ↑ q
Δ ↑ (p + q) = Δ ↑ p + Δ ↑ q
Δ ↑ (var α * p) = var α * Δ ↑ p -- treat α, β, γ as parameters (unspecified scalar constants)
Δ ↑ (var β * p) = var β * Δ ↑ p
Δ ↑ (var γ * p) = var γ * Δ ↑ p
Δ ↑ (p * q) = var α * p * q + var β * (Δ ↑ p * q + p * Δ ↑ q) + var γ * Δ ↑ p * Δ ↑ q

Y = Var 12

ϱ : Subst X Y
ϱ (ε x ε) = mkVar 0
ϱ (a x ε) = mkVar 1
ϱ (ε x b) = mkVar 2
ϱ (a x b) = mkVar 3
ϱ (ε y ε) = mkVar 4
ϱ (a y ε) = mkVar 5
ϱ (ε y b) = mkVar 6
ϱ (a y b) = mkVar 7
ϱ α = mkVar 8
ϱ β = mkVar 9
ϱ γ = mkVar 10
ϱ _ = mkVar 11 -- unused cases

t left right : Term X
t = var (ε x ε) * var (ε y ε)
left  = Δʳ b ↑ (Δˡ a ↑ t)
right = Δˡ a ↑ (Δʳ b ↑ t)

reversal-hom-lemma :
   ∃ λ proof →
   (subst ϱ left ≟ subst ϱ right) ≡ just proof
reversal-hom-lemma = _ ,, refl

```
