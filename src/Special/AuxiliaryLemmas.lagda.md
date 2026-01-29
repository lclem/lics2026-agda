---
title: Auxiliary lemmas
---

```
{-# OPTIONS --guardedness --sized-types #-}
{-# OPTIONS --allow-unsolved-metas #-}

open import Preliminaries.Base
import Preliminaries.Algebra

module Special.AuxiliaryLemmas
    (R : CommutativeRing)
    where

open Preliminaries.Algebra R
open import General.Terms R
open import Special.Polynomials R

private variable
    X Y Z : Set
    m n k : ℕ

-- these lemmas could be generalised over an arbitrary ring...

+-cong₃ :
    ∀ {p q p′ q′ r r′ : Term X} →
    p ≈ p′ →
    q ≈ q′ →
    r ≈ r′ →
    -----------------------------
    p + q + r ≈ p′ + q′ + r′

+-cong₃ = {!   !}

+-zero₃-mid :
    ∀ (p q : Term X) →
    ----------------------
    p + 0T + q ≈ p + q

+-zero₃-mid p q = {!   !}

+-≈zero₃-mid :
    ∀ {p q r : Term X} →
    q ≈ 0T →
    ----------------------
    p + q + r ≈ p + r

+-≈zero₃-mid = {!   !}

+-zero₃ :
    ∀ (p : Term X) →
    ----------------------
    0T + 0T + p ≈ p

+-zero₃ p = {!   !}

+-≈zero₃ :
    ∀ {p q r : Term X} →
    p ≈ 0T →
    q ≈ 0T →
    ----------------------
    p + q + r ≈ r

+-≈zero₃ = {!   !}

+-≈zeroˡ :
    ∀ {p q : Term X} →
    p ≈ 0T →
    ---------------
    p + q ≈ q

+-≈zeroˡ = {!   !}

+-≈zeroˡʳ :
    ∀ {p q : Term X} →
    p ≈ 0T →
    q ≈ 0T →
    ---------------
    p + q ≈ 0T

+-≈zeroˡʳ = {!   !}

+-≈zero₃ˡʳ :
    ∀ {p q r : Term X} →
    p ≈ 0T →
    r ≈ 0T →
    ---------------
    p + q + r ≈ q

+-≈zero₃ˡʳ = {!   !}

*+-zeroˡ :
    ∀ {p q : Term X} →
    ------------------
    0T * p + q ≈ q

*+-zeroˡ = {!   !}

·-≈zero :
    ∀ {p : Term X} {c} →
    c ≈R 0R →
    --------------------
    c · p ≈ 0T

·-≈zero = {!   !}

·+-≈zeroˡ :
    ∀ {p q : Term X} {c} →
    c ≈R 0R →
    ------------------------
    c · p + q ≈ q

·+-≈zeroˡ c≈0 = {! (+-≈zeroˡ (·-≈zero c≈0))  !}

·-+-distrib₃ :
    ∀ c (p q r : Term X) →
    ---------------------------------------
    c · (p + q + r) ≈ c · p + c · q + c · r

·-+-distrib₃ c p q r = {!   !}

x+-cong :
    ∀ {p q r : Term X} →
    p ≈ q →
    -----------------------
    r + p ≈ r + q

x+-cong p≈q = ≈-refl ⟨ +-cong ⟩ p≈q

*x-cong :
    ∀ {p q r : Term X} →
    p ≈ q →
    -----------------------
    p * r ≈ q * r

*x-cong p≈q = p≈q ⟨ *-cong ⟩ ≈-refl

x*-cong :
    ∀ {p q r : Term X} →
    p ≈ q →
    -----------------------
    r * p ≈ r * q

x*-cong p≈q = ≈-refl ⟨ *-cong ⟩ p≈q

*x+-cong : 
    ∀ {p q r s t : Term X} →
    p ≈ q →
    s ≈ t →
    -----------------------
    p * r + s ≈ q * r + t

*x+-cong = {!   !}

·*-comm : 
    ∀ c (p q : Term X) →
    -------------------------
    (c · p) * q ≈ p * (c · q)

·*-comm = {!   !}

lemma₀ :
    ∀ (p₀ p₁ q₀ q₁ r₀ r₁ : Term X) →
    (p₀ + p₁) + (q₀ + q₁) + (r₀ + r₁) ≈
    (p₀ + q₀ + r₀) + (p₁ + q₁ + r₁)

lemma₀ = {!   !}

lemma₁ :
    ∀ {p q r s : Term X} {c} →
    p ≈ 0T →
    c ≈R 0R →
    s ≈ 0T →
    ------------------
    p * q + c · r + s ≈ 0T

lemma₁ = {!   !}

lemma₂ :
    ∀ (a b c d : Term X) →
    ------------------------------------
    (a * b) * c + a * d ≈ a * (b * c + d)

lemma₂ = {!   !} 

-- use ·*-comm here
lemma₃ : 
    ∀ (a b d e : Term X) c →
    (a * b + c · a) * d + a * e ≈ a * (b * d + c · d + e)

lemma₃ = {!   !}

lemma₃′ : 
    ∀ (a b d e : Term X) c →
    ----------------------------
    (a * b + c · b) * d + e * b ≈ (a * d + c · d + e) * b

lemma₃′ = {!   !}

lemma₄ :
    ∀ (p q r s : Term X) →
    -----------------------
    (p * q) * r + s * q ≈ (p * r + s) * q
            
lemma₄ = {!   !}

lemma₅ :
    ∀ (p q r s : Term X) →
    -----------------------
    p + q + (r + s) ≈ (p + q + r) + s

lemma₅ = {!   !}

lemma₆ :
    ∀ (p q r : Term X) →
    -----------------------
    0T * q + 0R · r + p ≈ p

lemma₆ = {!   !}

*-distrib₃ʳ :
    ∀ (p q r s : Term X) →
    ---------------------------------------
    (p + q + r) * s ≈ p * s + q * s + r * s

*-distrib₃ʳ p q r s = {!   !}

*-distrib₂ :
    ∀ (p₁ p₂ q₁ q₂ : Term X) →
    ---------------------------------
    (p₁ + p₂) * (q₁ + q₂) ≈
    p₁ * q₁ + p₁ * q₂ +
    p₂ * q₁ + p₂ * q₂

*-distrib₂ = {!   !} 

*-distrib₃ :
    ∀ (p₁ p₂ p₃ q₁ q₂ q₃ : Term X) →
    ---------------------------------
    (p₁ + p₂ + p₃) * (q₁ + q₂ + q₃) ≈
    p₁ * q₁ + p₁ * q₂ + p₁ * q₃ +
    p₂ * q₁ + p₂ * q₂ + p₂ * q₃ +
    p₃ * q₁ + p₃ * q₂ + p₃ * q₃

*-distrib₃ = {!   !}

lemma₇ : 
    ∀ (p₁ p₂ p₃ p₄ p₅ : Term X) (c₁ c₂ : A) →
    ------------------------------------------------
    (((p₁ * p₂ + c₂ · p₁ + c₁ · p₂) * p₅ + (c₁ *R c₂) · p₅ + c₁ · p₃ + c₂ · p₄) + p₁ * p₃ + p₄ * p₂) * p₅ + p₄ * p₃
        ≈
    (p₁ * p₅ + c₁ · p₅ + p₄) * (p₂ * p₅ + c₂ · p₅ + p₃)

lemma₇ = {!   !}
```
