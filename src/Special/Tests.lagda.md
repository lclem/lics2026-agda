---
title: Decidability of equivalence of polynomial expressions
---

```
{-# OPTIONS --guardedness --sized-types #-}
{-# OPTIONS --allow-unsolved-metas #-}

open import Preliminaries.Base
import Preliminaries.Algebra

module Special.Tests where

-- open Preliminaries.Algebra Z
open import General.Terms ringℤ --  hiding (x)
open import Special.Polynomials ringℤ
open import Special.HNF ringℤ hiding (x)
open import Special.DecidableEquivalence ringℤ _≟ℤ_

_ : ∃ λ proof → ((var {X = Fin 5} zero ≟ var zero) ≡ just proof)
_ = _ ,, refl

_ : (var {X = Fin 5} (suc zero) ≟ var zero) ≡ nothing
_ = refl

_ : ∃ λ proof → ((var {X = Fin 5} (suc zero) ≟ var (suc zero)) ≡ just proof)
_ = _ ,, refl

_ : ∃ λ proof → ((x {n = 2026} + x′ ≟ x′ + x) ≡ just proof)
_ = _ ,, refl

-- 1ℤ = Int.1ℤ
2ℤ = 1ℤ +ℤ 1ℤ
3ℤ = 2ℤ +ℤ 1ℤ
4ℤ = 3ℤ +ℤ 1ℤ
5ℤ = 4ℤ +ℤ 1ℤ

_ : ∃ λ proof → ((2ℤ · x {n = 2026} ≟ x + x) ≡ just proof)
_ = _ ,, refl

_ : ∃ λ proof → ((x {n = 10} ≟ 0T + x) ≡ just proof)
_ = _ ,, refl

_ : ∃ λ proof → ((x {n = 10} - x ≟ 0T) ≡ just proof)
_ = _ ,, refl

_ : ∃ λ proof → ((x {n = 10} * x - y * y ≟ (x + y) * (x - y)) ≡ just proof)
_ = _ ,, refl

_ : ∃ λ proof → (((2ℤ · x {n = 10} + 3ℤ · y) * (x + y) 
                  ≟ 2ℤ · x * x + 5ℤ · x * y + 3ℤ · y * y ) ≡ just proof)
_ = _ ,, refl

_ : ∃ λ proof → (((x {n = 10} + y) * (x + y) * (x + y)
                  ≟ x * x * x + 3ℤ · x * x * y + 3ℤ · x * y * y + y * y * y ) ≡ just proof)
_ = _ ,, refl

_ : ∃ λ proof → (((x {n = 10} + y) * (x + y) ≟ x * x + 2ℤ · x * y + y * y) ≡ just proof)
_ = _ ,, refl

```
