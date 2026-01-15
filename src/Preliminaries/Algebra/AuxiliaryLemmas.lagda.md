---
title: Auxiliary lemmas 🚧
---

```
-- {-# OPTIONS --allow-unsolved-metas #-}

open import Preliminaries.Base hiding (refl; sym; trans)
module Preliminaries.Algebra.AuxiliaryLemmas (R : CommutativeRing) where

open import Algebra
open CommutativeRing R
open import Preliminaries.Equivalence isEquivalence
open Eq

lemma₀ : ∀ a b c x →
        (a + b) * x + c ≈ a * x + (b * x + c)
lemma₀ a b c x = begin
    (a + b) * x + c ≈⟨ distribʳ _ _ _ ⟨ +-cong ⟩ refl ⟩
    (a * x + b * x) + c ≈⟨ +-assoc _ _ _ ⟩
    a * x + (b * x + c)
    ∎

lemma₁ : ∀ a b c d x →
        (a + b) * x + (c + d) ≈ (a * x + c) + (b * x + d)
lemma₁ a b c d x = begin
    (a + b) * x + (c + d)      ≈⟨ lemma₀ _ _ _ _ ⟩
    a * x + (b * x + (c + d))  ≈⟨ refl ⟨ +-cong ⟩ sym (+-assoc _ _ _) ⟩
    a * x + ((b * x + c) + d)  ≈⟨ refl ⟨ +-cong ⟩ (+-comm _ _ ⟨ +-cong ⟩ refl) ⟩
    a * x + ((c + b * x) + d)  ≈⟨ refl ⟨ +-cong ⟩ +-assoc _ _ _ ⟩
    a * x + (c + (b * x + d))  ≈⟨ sym $ +-assoc _ _ _ ⟩
    (a * x + c) + (b * x + d)  ∎

lemma₂ : ∀ a b c x → a * c * x + b * c ≈ (a * x + b) * c
lemma₂ a b c x = begin
  a * c * x + b * c  ≈⟨ lem ⟨ +-cong ⟩ refl ⟩
  a * x * c + b * c  ≈⟨ sym $ distribʳ _ _ _ ⟩
  (a * x + b) * c    ∎
  where
  lem = begin
    a * c * x    ≈⟨ *-assoc _ _ _ ⟩
    a * (c * x)  ≈⟨ refl ⟨ *-cong ⟩ *-comm _ _ ⟩
    a * (x * c)  ≈⟨ sym $ *-assoc _ _ _ ⟩
    a * x * c    ∎

lemma₃ : ∀ a b c x → a * b * x + a * c ≈ a * (b * x + c)
lemma₃ a b c x = begin
  a * b * x + a * c    ≈⟨ *-assoc _ _ _ ⟨ +-cong ⟩ refl ⟩
  a * (b * x) + a * c  ≈⟨ sym $ distribˡ _ _ _ ⟩
  a * (b * x + c)      ∎

lemma₄ : ∀ a b c d x →
         (a * c * x + (a * d + b * c)) * x + b * d ≈
         (a * x + b) * (c * x + d)
lemma₄ a b c d x = begin
  (a * c * x + (a * d + b * c)) * x + b * d              ≈⟨ distribʳ _ _ _ ⟨ +-cong ⟩ refl ⟩
  (a * c * x * x + (a * d + b * c) * x) + b * d          ≈⟨ refl ⟨ +-cong ⟩ ((refl ⟨ +-cong ⟩ refl) ⟨ *-cong ⟩ refl) ⟨ +-cong ⟩ refl ⟩
  (a * c * x * x + (a * d + b * c) * x) + b * d          ≈⟨ +-assoc _ _ _  ⟩
  a * c * x * x + ((a * d + b * c) * x + b * d)          ≈⟨ lem₁ ⟨ +-cong ⟩ (lem₂ ⟨ +-cong ⟩ refl) ⟩
  a * x * (c * x) + (a * x * d + b * (c * x) + b * d)    ≈⟨ refl ⟨ +-cong ⟩ +-assoc _ _ _ ⟩
  a * x * (c * x) + (a * x * d + (b * (c * x) + b * d))  ≈⟨ sym $ +-assoc _ _ _ ⟩
  a * x * (c * x) + a * x * d + (b * (c * x) + b * d)    ≈⟨ sym $ distribˡ _ _ _ ⟨ +-cong ⟩ distribˡ _ _ _ ⟩
  a * x * (c * x + d) + b * (c * x + d)                  ≈⟨ sym $ distribʳ _ _ _ ⟩
  (a * x + b) * (c * x + d)                              ∎
  where
  lem₁′ = begin
    a * c * x    ≈⟨ *-assoc _ _ _ ⟩
    a * (c * x)  ≈⟨ refl ⟨ *-cong ⟩ *-comm _ _ ⟩
    a * (x * c)  ≈⟨ sym $ *-assoc _ _ _ ⟩
    a * x * c    ∎

  lem₁ = begin
    a * c * x * x    ≈⟨ lem₁′ ⟨ *-cong ⟩ refl ⟩
    a * x * c * x    ≈⟨ *-assoc _ _ _ ⟩
    a * x * (c * x)  ∎

  lem₂ = begin
    (a * d + b * c) * x        ≈⟨ distribʳ _ _ _ ⟩
    a * d * x + b * c * x      ≈⟨ *-assoc _ _ _ ⟨ +-cong ⟩ *-assoc _ _ _ ⟩
    a * (d * x) + b * (c * x)  ≈⟨ (refl ⟨ *-cong ⟩ *-comm _ _) ⟨ +-cong ⟩ refl ⟩
    a * (x * d) + b * (c * x)  ≈⟨ sym $ *-assoc _ _ _ ⟨ +-cong ⟩ refl ⟩
    a * x * d + b * (c * x)    ∎

lemma₅ : ∀ x → (0# * x + 1#) * x + 0# ≈ x
lemma₅ x = begin
  (0# * x + 1#) * x + 0#   ≈⟨ ((zeroˡ _ ⟨ +-cong ⟩ refl) ⟨ *-cong ⟩ refl) ⟨ +-cong ⟩ refl ⟩
  (0# + 1#) * x + 0#       ≈⟨ (+-identityˡ _ ⟨ *-cong ⟩ refl) ⟨ +-cong ⟩ refl ⟩
  1# * x + 0#              ≈⟨ +-identityʳ _ ⟩
  1# * x                   ≈⟨ *-identityˡ _ ⟩
  x                        ∎

lemma₆ : ∀ a x → 0# * x + a ≈ a
lemma₆ a x = begin
  0# * x + a    ≈⟨ zeroˡ _ ⟨ +-cong ⟩ refl ⟩
  0# + a        ≈⟨ +-identityˡ _ ⟩
  a             ∎

lemma₇ : ∀ a b c → a + (b + c) ≈ b + (a + c)
lemma₇ a b c = begin
  a + (b + c)    ≈⟩ +-assoc _ _ _ ⟩
  (a + b) + c    ≈⟨ (+-comm _ _ ⟨ +-cong ⟩ refl) ⟩
  (b + a) + c    ≈⟨ +-assoc _ _ _ ⟩
  b + (a + c)    ∎
```