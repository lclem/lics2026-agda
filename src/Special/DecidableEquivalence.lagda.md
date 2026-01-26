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
    (_R≟_ : let open Preliminaries.Algebra R in WeaklyDecidable _≈R_)
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
    data HNF : ℕ → Set where
        ∅     : HNF (suc n)
        _*x+_ : HNF (suc n) → Normal n → HNF (suc n)

    data Normal : ℕ → Set where
        zero  : Normal zero
        con : A → HNF (suc n) → Normal (suc n)
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
    ⟦ p *x+ q ⟧H = ⟦ p ⟧H * x + ⟦ q ⟧N ↑

    ⟦_⟧N : Normal n → Term′ n
    ⟦ zero  ⟧N = 0T
    ⟦ con c p ⟧N = c · ⟦ p ⟧H
```

Equality of normal forms

```
mutual
    data _≈H_ : HNF n → HNF n → Set where
        ∅     : _≈H_ {suc n} ∅ ∅
        _*x+_ : {p₁ p₂ : HNF (suc n)} {n₁ n₂ : Normal n} →
                p₁ ≈H p₂ → n₁ ≈N n₂ → (p₁ *x+ n₁) ≈H (p₂ *x+ n₂)

    data _≈N_ : Normal n → Normal n → Set where
        zero : zero ≈N zero
        con : {c₁ c₂ : A} {p₁ p₂ : HNF (suc n)} → c₁ ≈R c₂ → p₁ ≈H p₂ → con c₁ p₁ ≈N con c₂ p₂
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
  ⟦ p₁≈p₂ *x+ n₁≈n₂ ⟧H-cong =
        (⟦ p₁≈p₂ ⟧H-cong ⟨ *-cong ⟩ ≈-refl)
            ⟨ +-cong ⟩
        (≈-↑ ⟦ n₁≈n₂ ⟧N-cong)

  ⟦_⟧N-cong :
    {p₁ p₂ : Normal n} →
    p₁ ≈N p₂ →
    --------------------
    ⟦ p₁ ⟧N ≈ ⟦ p₂ ⟧N

  ⟦ zero  ⟧N-cong = ≈-refl
  ⟦ con c₁≈c₂ p₁≈p₂ ⟧N-cong = c₁≈c₂ ⟨ ·-cong ⟩ ⟦ p₁≈p₂ ⟧H-cong
```

Equality of normal forms is weakly decidable.

```
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
```

```
0H : HNF (suc n)
0H = ∅

0N : Normal n
0N {zero}  = zero
0N {suc n} = con 0R 0H
```

A simplifying variant of `_*x+_`.

```
_*x+HN_ : HNF (suc n) → Normal n → HNF (suc n)
(p *x+ n′) *x+HN n = (p *x+ n′) *x+ n
∅          *x+HN n with n ≟N 0N
... | just _  = 0H
... | nothing = 0H *x+ n
```

Addition of normal forms.

```
mutual
    _+H_ : HNF (suc n) → HNF (suc n) → HNF (suc n)
    ∅ +H p = p
    (p₁ *x+ n₁) +H ∅ = p₁ *x+ n₁
    (p₁ *x+ n₁) +H (p₂ *x+ n₂) = (p₁ +H p₂) *x+HN (n₁ +N n₂)

    _+N_ : Normal n → Normal n → Normal n
    zero +N zero = zero -- con (c₁ +R c₂)
    con c₁ p₁ +N con c₂ p₂ = con (c₁ +R c₂) (p₁ +H p₂)

```