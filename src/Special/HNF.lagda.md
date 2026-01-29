---
title: Horner normal form
---

```
{-# OPTIONS --guardedness --sized-types #-}
{-# OPTIONS --allow-unsolved-metas #-}

open import Preliminaries.Base
import Preliminaries.Algebra

module Special.HNF
    (R : CommutativeRing)
    -- (_≟R_ : let open Preliminaries.Algebra R in WeaklyDecidable _≈R_)
    where

open Preliminaries.Algebra R
open import General.Terms R hiding (x)
open import Special.Polynomials R

private variable
    X Y Z : Set
    m n k : ℕ

mutual
    data HNF : ℕ → Set where
        ∅     : HNF (suc n)
        _*x+_·x+_ : HNF (suc n) → A → Normal n → HNF (suc n)

    data Normal : ℕ → Set where
        zero  : Normal zero
        poly : HNF (suc n) → Normal (suc n)

0H : HNF (suc n)
0H = ∅

0N : Normal n
0N {zero}  = zero
0N {suc n} = poly 0H
```

```
infix 50 _↑
_↑ : Term′ n → Term′ (suc n)
0T ↑ = 0T
(var x) ↑ = var (suc x)
(c · p) ↑ = c · p ↑
(p + q) ↑ = p ↑ + q ↑
(p * q) ↑ = p ↑ * q ↑
```

Semantics of normal forms.

```
x : Term′ (suc n)
x = var zero

mutual
    ⟦_⟧H : HNF (suc n) → Term′ (suc n)
    ⟦ ∅       ⟧H = 0T
    ⟦ p *x+ c ·x+ q ⟧H = ⟦ p ⟧H * x + c · x + ⟦ q ⟧N ↑

    ⟦_⟧N : Normal n → Term′ n
    ⟦ zero  ⟧N = 0T
    ⟦ poly p ⟧N = ⟦ p ⟧H
```

Equality of normal forms

```
infix 4 _≈H_ _≈N_
mutual
    data _≈H_ : HNF n → HNF n → Set where
        ∅     : _≈H_ {suc n} ∅ ∅
        _*x+_·x+_ : {c₁ c₂ : A} {p₁ p₂ : HNF (suc n)} {n₁ n₂ : Normal n} →
            p₁ ≈H p₂ → c₁ ≈R c₂ → n₁ ≈N n₂ → (p₁ *x+ c₁ ·x+ n₁) ≈H (p₂ *x+ c₂ ·x+ n₂)

    data _≈N_ : Normal n → Normal n → Set where
        zero : zero ≈N zero
        poly : {p₁ p₂ : HNF (suc n)} → p₁ ≈H p₂ → poly p₁ ≈N poly p₂

mutual
    ≈H-refl : ∀ {p : HNF (suc k)} → p ≈H p
    ≈H-refl {p = ∅} = ∅
    ≈H-refl {p = _ *x+ _ ·x+ _} = ≈H-refl *x+ R-refl ·x+ ≈N-refl
    
    ≈N-refl : ∀ {n : Normal k} → n ≈N n
    ≈N-refl {n = zero} = zero
    ≈N-refl {n = poly _} = poly ≈H-refl

mutual
    ≈H-sym : ∀ {p q : HNF (suc k)} → p ≈H q → q ≈H p
    ≈H-sym ∅ = ∅
    ≈H-sym (p≈q *x+ c₁≈c₂ ·x+ n₁≈n₂) =
        ≈H-sym p≈q *x+ R-sym c₁≈c₂ ·x+ ≈N-sym n₁≈n₂

    ≈N-sym : ∀ {p q : Normal k} → p ≈N q → q ≈N p
    ≈N-sym zero = zero
    ≈N-sym (poly p≈q) = poly (≈H-sym p≈q)

mutual
    ≈H-trans : ∀ {p q r : HNF (suc k)} → p ≈H q → q ≈H r → p ≈H r
    ≈H-trans ∅ ∅ = ∅
    ≈H-trans (p≈q *x+ c₁≈c₂ ·x+ n₁≈n₂) (q≈r *x+ c₂≈c₃ ·x+ n₂≈n₃) =
        ≈H-trans p≈q q≈r *x+ R-trans c₁≈c₂ c₂≈c₃ ·x+ ≈N-trans n₁≈n₂ n₂≈n₃

    ≈N-trans : ∀ {p q r : Normal k} → p ≈N q → q ≈N r → p ≈N r
    ≈N-trans zero zero = zero
    ≈N-trans (poly p≈q) (poly q≈r) = poly (≈H-trans p≈q q≈r)

≈H-isEquivalence : IsEquivalence (_≈H_ {suc k})
≈H-isEquivalence = record { refl = ≈H-refl ; sym = ≈H-sym ; trans = ≈H-trans }

module EqH {k} where
    open import Preliminaries.Equivalence (≈H-isEquivalence {suc k})
    open Eq public

≈N-isEquivalence : IsEquivalence (_≈N_ {k})
≈N-isEquivalence = record { refl = ≈N-refl ; sym = ≈N-sym ; trans = ≈N-trans }

module EqN {k} where
    open import Preliminaries.Equivalence (≈N-isEquivalence {k})
    open Eq public
```

The semantics respects the equality relations.

```
≈-↑ : ∀ {p q : Term′ n} → p ≈ q → p ↑ ≈ q ↑
≈-↑ ≈-refl = ≈-refl
≈-↑ (≈-sym p≈q) = ≈-sym (≈-↑ p≈q)
≈-↑ (≈-trans p≈q q≈r) = ≈-trans (≈-↑ p≈q) (≈-↑ q≈r)
≈-↑ (·-cong c≈d p≈q) = ·-cong c≈d (≈-↑ p≈q)
≈-↑ (·-one p) = ·-one (p ↑)
≈-↑ (·-+-distrib c p q) = ·-+-distrib c (p ↑) (q ↑)
≈-↑ (+-·-distrib p c d) = +-·-distrib (p ↑) c d
≈-↑ (·-*-distrib c p q) = ·-*-distrib c (p ↑) (q ↑)
≈-↑ (*-·-distrib c d p) = *-·-distrib c d (p ↑)
≈-↑ (+-cong p≈q q≈qr) = +-cong (≈-↑ p≈q) (≈-↑ q≈qr)
≈-↑ (+-zeroʳ p) = +-zeroʳ (p ↑)
≈-↑ (+-assoc p q r) = +-assoc (p ↑) (q ↑) (r ↑)
≈-↑ (+-comm p q) = +-comm (p ↑) (q ↑)
≈-↑ (+-invʳ p) = +-invʳ (p ↑)
≈-↑ (*-cong p≈q p≈q₁) = *-cong (≈-↑ p≈q) (≈-↑ p≈q₁)
≈-↑ (*-assoc p q r) = *-assoc (p ↑) (q ↑) (r ↑)
≈-↑ (*-comm p q) = *-comm (p ↑) (q ↑)
≈-↑ (*-distribʳ p q r) = *-distribʳ (p ↑) (q ↑) (r ↑)
```

```
*x+·x-cong :
    ∀ {p q p′ q′ : Term′ (suc k)} {c c′} →
    p ≈ p′ →
    c ≈R c′ →
    q ≈ q′ →
    ---------------------------------------
    p * x + c · x + q ≈ p′ * x + c′ · x + q′

*x+·x-cong = {!   !}
    --     ⟦ p ⟧H * x + lift ⟦ c ⟧N
    --         ≈⟨ +-cong (*-cong (reflectH p≈Hq) ≈-refl) (≈-lift (reflectN c≈Nd)) ⟩
    --     ⟦ q ⟧H * x + lift ⟦ d ⟧N

mutual
    ⟦_⟧H-cong :
        {p₁ p₂ : HNF (suc n)} →
        p₁ ≈H p₂ →
        -----------------------
        ⟦ p₁ ⟧H ≈ ⟦ p₂ ⟧H

    ⟦ ∅ ⟧H-cong = ≈-refl
    ⟦_⟧H-cong
        {p₁ = p₁ *x+ c₁ ·x+ n₁}
        {p₂ = p₂ *x+ c₂ ·x+ n₂}
        (p₁≈p₂ *x+ c₁≈c₂ ·x+ n₁≈n₂) =
        begin
            ⟦ p₁ *x+ c₁ ·x+ n₁ ⟧H
                ≈⟨⟩
            ⟦ p₁ ⟧H * x + c₁ · x + ⟦ n₁ ⟧N ↑
                ≈⟨ *x+·x-cong ⟦ p₁≈p₂ ⟧H-cong c₁≈c₂ (≈-↑ ⟦ n₁≈n₂ ⟧N-cong) ⟩
            ⟦ p₂ ⟧H * x + c₂ · x + ⟦ n₂ ⟧N ↑
                ≈⟨⟩
            ⟦ p₂ *x+ c₂ ·x+ n₂ ⟧H
        ∎ where open EqP

    ⟦_⟧N-cong :
        {p₁ p₂ : Normal n} →
        p₁ ≈N p₂ →
        --------------------
        ⟦ p₁ ⟧N ≈ ⟦ p₂ ⟧N

    ⟦ zero  ⟧N-cong = ≈-refl
    ⟦ poly p₁≈p₂ ⟧N-cong = ⟦ p₁≈p₂ ⟧H-cong

```

```
0N-hom : ∀ {n} → ⟦ 0N {n} ⟧N ≈ 0T
0N-hom {zero} = ≈-refl
0N-hom {suc _} = ≈-refl

0N-hom↑ : ∀ {n} → ⟦ 0N {n} ⟧N ↑ ≈ 0T
0N-hom↑ = ≈-↑ 0N-hom

⟦0⟧≈H0 : {p : HNF (suc n)} → p ≈H 0H → ⟦ p ⟧H ≈ 0T
⟦0⟧≈H0 ∅ = {!   !}

⟦0⟧≈N0 : {m : Normal n} → m ≈N 0N → ⟦ m ⟧N ≈ 0T
⟦0⟧≈N0 {m = m} m≈0 = begin
  ⟦ m  ⟧N   ≈⟨ ⟦ m≈0 ⟧N-cong ⟩
  ⟦ 0N ⟧N   ≈⟨ 0N-hom ⟩
  0T        ∎ where open EqP

0≈N⟦0⟧ : {m : Normal n} → m ≈N 0N → 0T ≈ ⟦ m ⟧N
0≈N⟦0⟧ = ≈-sym ∘ ⟦0⟧≈N0
```

```
mutual
    reflectH :
        {p q : HNF (suc k)} →
        p ≈H q →
        ---------------------
        ⟦ p ⟧H ≈ ⟦ q ⟧H

    reflectH ∅ = ≈-refl
    reflectH
        {p = p *x+ c ·x+ m} {q *x+ d ·x+ n}
        (p≈q *x+ c≈d ·x+ m≈n) =
        begin
            ⟦ p ⟧H * x + c · x + ⟦ m ⟧N ↑
                ≈⟨ *x+·x-cong (reflectH p≈q) c≈d (≈-↑ (reflectN m≈n)) ⟩
            ⟦ q ⟧H * x + d · x + ⟦ n ⟧N ↑
        ∎ where open EqP

    reflectN :
        {p q : Normal k} →
        p ≈N q →
        ------------------
        ⟦ p ⟧N ≈ ⟦ q ⟧N

    reflectN zero = ≈-refl
    reflectN (poly p) = reflectH p
```
