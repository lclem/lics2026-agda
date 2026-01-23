---
title: 
---

```
-- {-# OPTIONS --allow-unsolved-metas #-}

open import Preliminaries.Base
import Preliminaries.Algebra

module Preliminaries.Naturals (R : CommutativeRing) where

open import Preliminaries.Algebra R
open import Data.Nat.Base
--     using (ℕ; suc; zero; _∸_)
--     renaming (_+_ to _+_; _*_ to _+_; _≥_ to _≥ℕ_)
-- open import Data.Nat
--     using ()
--     renaming (_<?_ to _<ℕ?_)

open import Preliminaries.Equivalence isEquivalence

φ : ℕ → A
φ zero = 0R
φ (suc zero) = 1R
φ (suc n @ (suc _)) = 1R +R φ n

φ-suc : ∀ n → φ (suc n) ≈R 1R +R φ n
φ-suc zero = R-sym $ +R-identityʳ _
φ-suc (suc n) = R-refl

+-hom-φ : ∀ a b → φ (a + b) ≈R φ a +R φ b
+-hom-φ zero b = R-sym (+R-identityˡ _)
+-hom-φ (suc zero) zero = R-sym (+R-identityʳ _)
+-hom-φ (suc zero) b @ (suc _) = R-refl
+-hom-φ (suc a @ (suc _)) b =
    begin
        1R +R φ (a + b)
            ≈⟨ +R-cong R-refl (+-hom-φ a b) ⟩
        1R +R (φ a +R φ b)
            ≈⟨ +R-assoc _ _ _ ⟨
        1R +R φ a +R φ b
    ∎ where open Eq

∸-hom-φ :
    ∀ {m n} → m ≥ n →
    --------------------------
    φ (m ∸ n) ≈R φ m +R -R φ n

∸-hom-φ {m} {n} z≤n = R-sym $ a+-0≈a _
∸-hom-φ {suc m} {suc n} (s≤s m≥n) =
    begin
        φ (m ∸ n) ≈⟨ ∸-hom-φ m≥n ⟩
        φ m -R φ n ≈⟨ one-plus-lem _ _ ⟨
        (1R +R φ m) -R (1R +R φ n) ≈⟩ φ-suc m ⟨ +R-cong ⟩ -R‿cong (φ-suc n) ⟩
        φ (suc m) -R φ (suc n)
    ∎ where open Eq
    
    --  {!∸-hom-φ m≥n  !}

-- φℕ (m ∸ n) ≈R φℕ m +R -R φℕ n

*-hom-φ : ∀ a b → φ (a * b) ≈R φ a *R φ b
*-hom-φ zero b = R-sym (R-zeroˡ _)
*-hom-φ (suc a) b = 
    begin
        φ (b + a * b)
            ≈⟨ +-hom-φ b _ ⟩
        φ b +R φ (a * b)
            ≈⟨ R-refl ⟨ +R-cong ⟩ *-hom-φ a _ ⟩
        φ b +R φ a *R φ b
            ≈⟨ gather _ _ ⟩
        (1R +R φ a) *R φ b
            ≈⟨ +-hom-φ 1 a ⟨ *R-cong ⟩ R-refl ⟨
        φ (1 + a) *R φ b
            ≈⟨⟩
        φ (suc a) *R φ b
    ∎ where open Eq
```