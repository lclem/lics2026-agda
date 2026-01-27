---
title: Decidability of equivalence of polynomial expressions
---

```
{-# OPTIONS --guardedness --sized-types #-}
{-# OPTIONS --allow-unsolved-metas #-}

open import Preliminaries.Base
import Preliminaries.Algebra

module Special.DecidableEquivalence
    (R : CommutativeRing)
    (_≟R_ : let open Preliminaries.Algebra R in WeaklyDecidable _≈R_)
    where

open Preliminaries.Algebra R
open import General.Terms R hiding (x)
open import Special.Polynomials R

private variable
    X Y Z : Set
    m n : ℕ

```

```
mutual
    -- infix _*x+_·x+_
    data HNF : ℕ → Set where
        ∅     : HNF (suc n)
        -- con : A → HNF (suc n)
        _*x+_·x+_ : HNF (suc n) → A → Normal n → HNF (suc n)

    data Normal : ℕ → Set where
        zero  : Normal zero
        -- con  : A → Normal (suc zero)
        poly : HNF (suc n) → Normal (suc n)
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
private x : Term′ (suc n)
x = var zero

mutual
    ⟦_⟧H : HNF (suc n) → Term′ (suc n)
    ⟦ ∅       ⟧H = 0T
    -- ⟦ con c   ⟧H = c · x
    ⟦ p *x+ c ·x+ q ⟧H = ⟦ p ⟧H * x + c · x + ⟦ q ⟧N ↑

    ⟦_⟧N : Normal n → Term′ n
    ⟦ zero  ⟧N = 0T
    -- ⟦ con c ⟧N = c · var zero
    ⟦ poly p ⟧N = ⟦ p ⟧H
```

Equality of normal forms

```
mutual
    data _≈H_ : HNF n → HNF n → Set where
        ∅     : _≈H_ {suc n} ∅ ∅
        -- con : {c₁ c₂ : A} → c₁ ≈R c₂ → _≈H_ {suc n} (con c₁) (con c₂)
        -- _*x+_ : {p₁ p₂ : HNF (suc n)} {n₁ n₂ : Normal n} →
        --         p₁ ≈H p₂ → n₁ ≈N n₂ → (p₁ *x+ n₁) ≈H (p₂ *x+ n₂)
        _*x+_·x+_ : {c₁ c₂ : A} {p₁ p₂ : HNF (suc n)} {n₁ n₂ : Normal n} →
            p₁ ≈H p₂ → c₁ ≈R c₂ → n₁ ≈N n₂ → (p₁ *x+ c₁ ·x+ n₁) ≈H (p₂ *x+ c₂ ·x+ n₂)

    data _≈N_ : Normal n → Normal n → Set where
        zero : zero ≈N zero
        -- con : {c₁ c₂ : A} → c₁ ≈R c₂ → con c₁ ≈N con c₂
        poly : {p₁ p₂ : HNF (suc n)} → p₁ ≈H p₂ → poly p₁ ≈N poly p₂
```

The semantics respect the equality relations.

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

mutual
    ⟦_⟧H-cong :
        {p₁ p₂ : HNF (suc n)} →
        p₁ ≈H p₂ →
        -----------------------
        ⟦ p₁ ⟧H ≈ ⟦ p₂ ⟧H

    ⟦ ∅ ⟧H-cong = ≈-refl
    -- ⟦ con c₁≈c₂ ⟧H-cong = c₁≈c₂ ⟨ ·-cong ⟩ ≈-refl
    ⟦ p₁≈p₂ *x+ c₁≈c₂ ·x+ n₁≈n₂ ⟧H-cong = {!   !}
        -- (⟦ p₁≈p₂ ⟧H-cong ⟨ *-cong ⟩ ≈-refl)
        --     ⟨ +-cong ⟩
        -- (≈-↑ ⟦ n₁≈n₂ ⟧N-cong)

    ⟦_⟧N-cong :
        {p₁ p₂ : Normal n} →
        p₁ ≈N p₂ →
        --------------------
        ⟦ p₁ ⟧N ≈ ⟦ p₂ ⟧N

    ⟦ zero  ⟧N-cong = ≈-refl
    -- ⟦ con c₁≈c₂ ⟧N-cong = c₁≈c₂ ⟨ ·-cong ⟩ ≈-refl
    ⟦ poly p₁≈p₂ ⟧N-cong = ⟦ p₁≈p₂ ⟧H-cong

-- -- Equality of normal forms is weakly decidable.

mutual
    infix 4 _≟H_ _≟N_

    _≟H_ : WeaklyDecidable (_≈H_ {n = n})
    _≟H_ = {!   !}
--     ∅           ≟H ∅           = just ∅
--     ∅           ≟H (_ *x+ _)   = nothing
--     (_ *x+ _)   ≟H ∅           = nothing
--     (p₁ *x+ c₁) ≟H (p₂ *x+ c₂) with p₁ ≟H p₂ | c₁ ≟N c₂
--     ... | just p₁≈p₂ | just c₁≈c₂ = just (p₁≈p₂ *x+ c₁≈c₂)
--     ... | _          | nothing    = nothing
--     ... | nothing    | _          = nothing

    _≟N_ : WeaklyDecidable (_≈N_ {n = n})
    _≟N_ = {!   !}
--     con c₁ ≟N con c₂ with c₁ R≟ c₂
--     ... | just c₁≈c₂ = just (con c₁≈c₂)
--     ... | nothing    = nothing
--     poly p₁ ≟N poly p₂ with p₁ ≟H p₂
--     ... | just p₁≈p₂ = just (poly p₁≈p₂)
--     ... | nothing    = nothing

0H : HNF (suc n)
0H = ∅

0N : Normal n
0N {zero}  = zero
0N {suc n} = poly 0H

-- A simplifying variant of `_*x+_`.

_*x+HN_ : HNF (suc n) → Normal n → HNF (suc n)
∅ *x+HN n with n ≟N 0N
... | just _  = 0H
... | nothing = 0H *x+ 0R ·x+ n
p *x+HN n = p *x+ 0R ·x+ n

_*x+_·x+HN_ : HNF (suc n) → A → Normal n → HNF (suc n)
∅ *x+ c ·x+HN n
    with c ≟R 0R | n ≟N 0N
... | just _ | just _  = 0H
... | nothing | just _  = {!   !}
... | _ | nothing = 0H *x+ c ·x+ n
p *x+ c ·x+HN n = p *x+ c ·x+ n


-- Addition of normal forms.

mutual
    _+H_ : HNF (suc n) → HNF (suc n) → HNF (suc n)
    ∅ +H p = p
    p +H ∅ = p
    (p₁ *x+ c₁ ·x+ n₁) +H (p₂ *x+ c₂ ·x+ n₂) = (p₁ +H p₂) *x+ (c₁ +R c₂) ·x+HN (n₁ +N n₂)

    _+N_ : Normal n → Normal n → Normal n
    zero +N zero = zero
    -- con c₁ +N con c₂ = con (c₁ +R c₂)
    poly p₁ +N poly p₂ = poly (p₁ +H p₂)

-- -- Multiplication of normal forms

-- _*x+H_ : HNF (suc n) → HNF (suc n) → HNF (suc n)
-- p₁         *x+H (p₂ *x+ n) = (p₁ +H p₂) *x+HN n
-- -- ∅          *x+H ∅          = ∅
-- -- (p₁ *x+ n) *x+H ∅          = (p₁ *x+ n) *x+ 0N
-- -- con c₁ *x+H con c₂ = con (c₁ *R c₂)
-- _ *x+H con c₂ = {!   !}

-- mutual

--     _*NH_ : Normal n → HNF (suc n) → HNF (suc n)
--     c *NH ∅          = 0H
--     c *NH (p *x+ c′) with c ≟N 0N
--     ... | just c≈0 = 0H
--     ... | nothing  = (c *NH p) *x+ (c *N c′)

--     _*HN_ : HNF (suc n) → Normal n → HNF (suc n)
--     ∅          *HN c = 0H
--     (p *x+ c′) *HN c with c ≟N 0N
--     ... | just _ = 0H
--     ... | nothing = (p *HN c) *x+ (c′ *N c)

--     _*H_ : HNF (suc n) → HNF (suc n) → HNF (suc n)
--     ∅           *H _           = 0H
--     (_ *x+ _)   *H ∅           = 0H
--     (p₁ *x+ n₁) *H (p₂ *x+ n₂) =
--         ((p₁ *H p₂) *x+H ((p₁ *HN n₂) +H (n₁ *NH p₂))) *x+HN (n₁ *N n₂)

--     _*N_ : Normal n → Normal n → Normal n
--     con c₁  *N con c₂  = con (c₁ *R c₂)
--     poly p₁ *N poly p₂ = poly (p₁ *H p₂)
```