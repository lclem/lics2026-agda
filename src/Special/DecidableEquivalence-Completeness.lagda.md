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
    (_≟R_ : let open Preliminaries.Algebra R in WeaklyDecidable _≈R_)
    where

open Preliminaries.Algebra R
open import General.Terms R hiding (x)
open import Special.Polynomials R
open import Special.HNF R

open import Special.AuxiliaryLemmas R
open import Special.DecidableEquivalence R _≟R_

private variable
    X Y Z : Set
    m n k : ℕ

```


```
mutual
    ·H-zero : (p : HNF (suc k)) → (0R ·H p) ≈H 0H
    ·H-zero _ with 0R ≟R 0R
    ... | just _ = ∅
    ·H-zero _ | nothing = {!   !} -- find a contradiction
    -- ·H-zero (p *x+ c ·x+ n) | nothing
    --     with ·H-zero p | R-zeroˡ c | ·N-zero n 
    -- ... | a | b | c = {!   !}
    
    ·N-zero : (n : Normal k) → (0R ·N n) ≈N 0N
    ·N-zero zero = zero
    ·N-zero (poly p) = poly (·H-zero p)

mutual
    ·H-one : (p : HNF (suc k)) → (1R ·H p) ≈H p
    ·H-one _ with 1R ≟R 0R in eq
    ... | just _ = {!   !} -- find a contradiction
    ·H-one ∅ | nothing = ∅
    ·H-one (p *x+ c ·x+ n) | nothing = ·H-one p *x+ *R-identity .fst c ·x+ ·N-one n
    
    ·N-one : (n : Normal k) → (1R ·N n) ≈N n
    ·N-one zero = zero
    ·N-one (poly p) = poly (·H-one p)

mutual

    ·H-cong :
        {c₁ c₂ : A} {p₁ p₂ : HNF (suc k)} →
        c₁ ≈R c₂ →
        p₁ ≈H p₂ →
        -----------------------------------
        (c₁ ·H p₁) ≈H (c₂ ·H p₂)

    ·H-cong {c₁ = c₁} {c₂} c≈d _
        with c₁ ≟R 0R | c₂ ≟R 0R
    ... | just _ | just _ = ∅
    ·H-cong c≈d ∅ | nothing | just _ = ∅
    ·H-cong c≈d ∅ | just _ | nothing = ∅
    ·H-cong c≈d ∅ | nothing | nothing = ∅
    ·H-cong {c₁ = c₁} {c₂} c₁≈c₂ (_*x+_·x+_ {c₁ = c₃} {c₄} p₁≈p₂ c₃≈c₄ x₂) | just c₁≈0 | nothing = {!   !} -- need to find a contradiction
    --     with c₂ ≟R 0R
    -- ·H-cong c₁≈c₃ (_*x+_·x+_ {c₁ = c₃} p₁≈p₂ x₁ x₂) | just _ | nothing | just _ = {! ·H-cong (R-trans (R-sym c₁≈c₃) c₁≈0) p₁≈p₂  !}
    -- ·H-cong c₁≈c₃ (_*x+_·x+_ {c₁ = c₃} p₁≈p₂ x₁ x₂) | just _ | nothing | nothing = {!   !}
    ·H-cong c≈d (p₁≈p₂ *x+ x₁ ·x+ x₂) | nothing | just _ = {!   !}
    ·H-cong c≈d (p₁≈p₂ *x+ x₁ ·x+ x₂) | nothing | nothing = ·H-cong c≈d p₁≈p₂ *x+ *R-cong c≈d x₁ ·x+ ·N-cong c≈d x₂
    
    ·N-cong : 
        {c₁ c₂ : A} {p₁ p₂ : Normal k} →
        c₁ ≈R c₂ →
        p₁ ≈N p₂ →
        --------------------------------
        (c₁ ·N p₁) ≈N (c₂ ·N p₂)

    ·N-cong c≈d zero = zero
    ·N-cong c≈d (poly p≈q) = poly (·H-cong c≈d p≈q)

mutual
    +H-cong :
        {p₁ p₂ q₁ q₂ : HNF (suc k)} →
        p₁ ≈H p₂ →
        q₁ ≈H q₂ →
        -----------------------------
        (p₁ +H q₁) ≈H (p₂ +H q₂)

    +H-cong ∅ ∅ = ∅
    +H-cong ∅ eq@(_ *x+ _ ·x+ _) = eq
    +H-cong eq@(_ *x+ _ ·x+ _) ∅ = eq
    +H-cong (p₁≈p₂ *x+ x₁ ·x+ x₂) (q₁≈q₂ *x+ x₃ ·x+ x₄)
        = {!   !} -- +H-cong p₁≈p₂ q₁≈q₂ *x+ +R-cong x₁ x₃ ·x+ +N-cong x₂ x₄

    +N-cong :
        {p₁ p₂ q₁ q₂ : Normal k} →
        p₁ ≈N p₂ →
        q₁ ≈N q₂ →
        --------------------------
        (p₁ +N q₁) ≈N (p₂ +N q₂)
    
    +N-cong zero zero = zero
    +N-cong (poly x₁) (poly x₂) = poly (+H-cong x₁ x₂)

mutual
    +H-comm :
        (p q : HNF (suc k)) →
        ---------------------
        (p +H q) ≈H (q +H p)

    +H-comm ∅ ∅ = ≈H-refl
    +H-comm ∅ (_ *x+ _ ·x+ _) = ≈H-refl
    +H-comm (_ *x+ _ ·x+ _) ∅ = ≈H-refl
    +H-comm (p *x+ _ ·x+ _) (q *x+ _ ·x+ _)
        = {!   !} -- +H-comm p q *x+ +R-comm _ _ ·x+ +N-comm _ _

    +N-comm :
        (p q : Normal k) →
        ------------------
        (p +N q) ≈N (q +N p)

    +N-comm zero zero = zero
    +N-comm (poly p) (poly q) = poly (+H-comm p q)
```

```
mutual 
    ·-+-distribH :
        (c : A) (p q : HNF (suc k)) →
        ----------------------------------------
        (c ·H (p +H q)) ≈H ((c ·H p) +H (c ·H q))

    ·-+-distribH c p q with c ≟R 0R
    ... | just _ = ∅
    ·-+-distribH _ ∅ ∅ | nothing = ∅
    ·-+-distribH _ ∅ _ | nothing = ≈H-refl
    ·-+-distribH _ (_ *x+ _ ·x+ _) ∅ | nothing = ≈H-refl
    ·-+-distribH c′ (p *x+ c ·x+ m) (q *x+ d ·x+ n) | nothing
        = {!   !} -- ·-+-distribH _ _ _ *x+ R-distribˡ _ _ _ ·x+ ·-+-distribN _ _ _

    ·-+-distribN :
        (c : A) (m n : Normal k) →
        ----------------------------------------
        (c ·N (m +N n)) ≈N ((c ·N m) +N (c ·N n))

    ·-+-distribN c zero zero = zero
    ·-+-distribN c (poly p) (poly q) = poly (·-+-distribH c p q)

```
complete :
    {p q : Term′ k} →
    p ≈ q →
    --------------------------
    normalise p ≈N normalise q

complete ≈-refl = ≈N-refl
complete (≈-sym p≈q) = ≈N-sym (complete p≈q)
complete (≈-trans p≈q q≈r) = ≈N-trans (complete p≈q) (complete q≈r)

complete {p = p} {q} (·-cong c≈d p≈q) = ·N-cong c≈d (complete p≈q)
complete (·-one _) = ·N-one _
complete (·-+-distrib _ _ _) = ·-+-distribN _ _ _
complete (+-·-distrib _ _ _) = {!   !}
complete (·-*-distrib _ _ _) = {!   !}
complete (*-·-distrib _ _ _) = {!   !}
complete (+-cong p₀≈p₁ q₀≈q₁) = +N-cong (complete p₀≈p₁) (complete q₀≈q₁)
complete {p = p} {q} (+-zeroʳ .q) = {!   !}
complete {p = p} {q} (+-assoc p₁ q₁ r) = {!   !}
complete (+-comm _ _) = +N-comm _ _
complete {p = p} {q} (+-invʳ p₁) = {!   !}
complete {p = p} {q} (*-cong p≈q p≈q₁) = {!   !}
complete {p = p} {q} (*-assoc p₁ q₁ r) = {!   !}
complete {p = p} {q} (*-comm p₁ q₁) = {!   !}
complete {p = p} {q} (*-distribʳ p₁ q₁ r) = {!   !}

```
