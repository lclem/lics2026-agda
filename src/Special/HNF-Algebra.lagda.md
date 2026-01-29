---
title: Completeness of equivalence algorithm
---

```
{-# OPTIONS --guardedness --sized-types #-}
{-# OPTIONS --allow-unsolved-metas #-}

open import Preliminaries.Base
import Preliminaries.Algebra

module Special.HNF-Algebra
    (R : CommutativeRing)
    (_≟R_ : let open Preliminaries.Algebra R in Decidable _≈R_)
    where

open Preliminaries.Algebra R
open import General.Terms R hiding (x)
open import Special.Polynomials R
open import Special.HNF R
open import Special.DecidableEquivalence R _≟R_
open import Special.AuxiliaryLemmas R

private variable
    X Y Z : Set
    m n k : ℕ
```

```
mutual
    ·H-zero : (p : HNF (suc k)) → (0R ·H p) ≈H 0H
    ·H-zero _ with 0R ≟R 0R
    ... | yes _ = ∅
    ·H-zero ∅ | no _ = ∅
    ·H-zero (p *x+ c ·x+ n) | no _ = {!   !}
    --     with ·H-zero p | R-zeroˡ c | ·N-zero n 
    -- ... | a | b | c = {!   !}
    
    ·N-zero : (n : Normal k) → (0R ·N n) ≈N 0N
    ·N-zero zero = zero
    ·N-zero (poly p) = poly (·H-zero p)

mutual
    ·H-one : (p : HNF (suc k)) → (1R ·H p) ≈H p
    ·H-one _ with 1R ≟R 0R in eq
    ... | yes _ = {!   !} -- find a contradiction
    ·H-one ∅ | no _ = ∅
    ·H-one (p *x+ c ·x+ n) | no _ = {!   !} -- ·H-one p *x+ *R-identity .fst c ·x+ ·N-one n
    
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

    ·H-cong {c₁ = c₁} {c₂} c≈d p≈q = {!   !}
    --     with c₁ ≟R 0R | c₂ ≟R 0R
    -- ... | yes _ | yes _ = ∅
    -- ·H-cong c≈d ∅ | no _ | yes _ = ∅
    -- ·H-cong c≈d ∅ | yes _ | no _ = ∅
    -- ·H-cong c≈d ∅ | no _ | no _ = ∅
    -- ·H-cong {c₁ = c₁} {c₂} c₁≈c₂ (_*x+_·x+_ {c₁ = c₃} {c₄} p₁≈p₂ c₃≈c₄ x₂) | just c₁≈0 | nothing = {!   !} -- need to find a contradiction
    -- --     with c₂ ≟R 0R
    -- -- ·H-cong c₁≈c₃ (_*x+_·x+_ {c₁ = c₃} p₁≈p₂ x₁ x₂) | just _ | nothing | just _ = {! ·H-cong (R-trans (R-sym c₁≈c₃) c₁≈0) p₁≈p₂  !}
    -- -- ·H-cong c₁≈c₃ (_*x+_·x+_ {c₁ = c₃} p₁≈p₂ x₁ x₂) | just _ | nothing | nothing = {!   !}
    -- ·H-cong c≈d (p₁≈p₂ *x+ x₁ ·x+ x₂) | nothing | just _ = {!   !}
    -- ·H-cong c≈d (p₁≈p₂ *x+ x₁ ·x+ x₂) | nothing | nothing = {!   !} -- ·H-cong c≈d p₁≈p₂ *x+ *R-cong c≈d x₁ ·x+ ·N-cong c≈d x₂
    
    ·N-cong : 
        {c₁ c₂ : A} {p₁ p₂ : Normal k} →
        c₁ ≈R c₂ →
        p₁ ≈N p₂ →
        --------------------------------
        (c₁ ·N p₁) ≈N (c₂ ·N p₂)

    ·N-cong c≈d zero = zero
    ·N-cong c≈d (poly p≈q) = poly (·H-cong c≈d p≈q)

mutual
    ·x+HN-cong :
        {p q : HNF (suc k)} {c d : A} {m n : Normal k} →
        p ≈H q →
        c ≈R d →
        m ≈N n →
        ----------------------------------
        p *x+ c ·x+HN m ≈H q *x+ d ·x+HN n
    
    ·x+HN-cong {c = c} {d} {m} {n} ∅ c≈d m≈n
        with c ≟R 0R | d ≟R 0R
    ·x+HN-cong {c = c} {d} {m} {n} ∅ c≈d zero
        | yes c≈0 | yes d≈0 = ∅
    ·x+HN-cong {c = c} {d} {m} {n} ∅ c≈d (poly ∅)
        | yes c≈0 | yes d≈0 = ∅
    ·x+HN-cong {c = c} {d} {m} {n} ∅ c≈d eq@(poly (_ *x+ _ ·x+ _))
        | yes c≈0 | yes d≈0 = ∅ *x+ c≈d ·x+ eq
    ... | no _ | no _ = ∅ *x+ c≈d ·x+ m≈n
    ... | yes c≈0 | no _ = {!   !} -- there should be a contradiction here
    ... | no _ | yes d≈0 = {!   !} -- there should be a contradiction here

    ·x+HN-cong p≈q c≈d m≈n = {!   !}
    
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
        = ·x+HN-cong (+H-comm p q) (+R-comm _ _) (+N-comm _ _)

    +N-comm :
        (p q : Normal k) →
        ------------------
        (p +N q) ≈N (q +N p)

    +N-comm zero zero = zero
    +N-comm (poly p) (poly q) = poly (+H-comm p q)

mutual
    +H-zeroʳ : (p : HNF (suc k)) → p +H 0H ≈H p
    +H-zeroʳ ∅ = ∅
    +H-zeroʳ (p *x+ c ·x+ n) = ≈H-refl

    +N-zeroʳ : (n : Normal k) → n +N 0N ≈N n
    +N-zeroʳ zero = zero
    +N-zeroʳ (poly p) = poly (+H-zeroʳ p)

mutual
    +H-zeroˡ : (p : HNF (suc k)) → 0H +H p ≈H p
    +H-zeroˡ ∅ = ∅
    +H-zeroˡ (p *x+ c ·x+ n) = ≈H-refl

    +N-zeroˡ : (n : Normal k) → 0N +N n ≈N n
    +N-zeroˡ zero = zero
    +N-zeroˡ (poly p) = poly (+H-zeroˡ p)

mutual

    +H-assoc :
        (p q r : HNF (suc k)) →
        -----------------------------
        (p +H q) +H r ≈H p +H (q +H r)

    +H-assoc p q r = {!   !}

    +N-assoc :
        (p q r : Normal k) →
        -----------------------------
        (p +N q) +N r ≈N p +N (q +N r)

    +N-assoc zero zero zero =
        begin
            (zero +N zero) +N zero
                ≈⟨ +N-zeroʳ _ ⟨ +N-cong ⟩ ≈N-refl ⟩
            zero +N zero
                ≈⟨ +N-zeroˡ _ ⟩
            zero +N zero +N zero
        ∎ where open EqN
    +N-assoc (poly p) (poly q) (poly r) = poly (+H-assoc p q r)

mutual 
    ·-+-distribH :
        (c : A) (p q : HNF (suc k)) →
        ----------------------------------------
        (c ·H (p +H q)) ≈H ((c ·H p) +H (c ·H q))

    ·-+-distribH c p q with c ≟R 0R
    ... | yes _ = ∅
    ·-+-distribH _ ∅ ∅ | no _ = ∅
    ·-+-distribH _ ∅ _ | no _ = ≈H-refl
    ·-+-distribH _ (_ *x+ _ ·x+ _) ∅ | no _ = {!   !} -- ≈H-refl
    ·-+-distribH c′ (p *x+ c ·x+ m) (q *x+ d ·x+ n) | no _
        = {!   !} -- ·-+-distribH _ _ _ *x+ R-distribˡ _ _ _ ·x+ ·-+-distribN _ _ _

    ·-+-distribN :
        (c : A) (m n : Normal k) →
        ----------------------------------------
        (c ·N (m +N n)) ≈N ((c ·N m) +N (c ·N n))

    ·-+-distribN c zero zero = zero
    ·-+-distribN c (poly p) (poly q) = poly (·-+-distribH c p q)

mutual

    +-·-distribN :
        ∀ (n : Normal k) c d →
        -----------------------------
        (c +R d) ·N n ≈N c ·N n +N d ·N n

    +-·-distribN = {!   !}

mutual
    ·-*-distribN :
        ∀ c (m n : Normal k) →
        -------------------------
        (c ·N m) *N n ≈N c ·N (m *N n)

    ·-*-distribN = {!   !}

mutual
    *-·-distribN :
        ∀ c d (n : Normal k) →
        --------------------------
        (c *R d) ·N n ≈N c ·N (d ·N n)

    *-·-distribN = {!   !}

```
