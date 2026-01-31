---
title: Completeness of equivalence algorithm
---

```
{-# OPTIONS --guardedness --sized-types #-}
{-# OPTIONS --allow-unsolved-metas #-}

open import Preliminaries.Base
import Preliminaries.Algebra

module Special.HNF-Normalised
    (R : CommutativeRing)
    (1≉0 : let open Preliminaries.Algebra R in ¬ (1R ≈R 0R))
    -- (no-zero-divisors : let open Preliminaries.Algebra R in
    --     ∀ {a b} → a *R b ≈R 0R → a ≈R 0R ⊎ b ≈R 0R)
    (_≟R_ : let open Preliminaries.Algebra R in Decidable _≈R_)
    where

open Preliminaries.Algebra R
open import General.Terms R hiding (x)
open import Special.Polynomials R
open import Special.HNF R
open import Special.DecidableEquivalence R _≟R_
open import Special.AuxiliaryLemmas R

private variable
    k : ℕ
    p q : HNF (suc k)
    c : A
    m n : Normal k
```

```
mutual

    data Because {k} : HNF (suc k) → A → Normal k → Set where
        norm₀ : ¬ (p ≈H 0H) → Because p c n
        norm₁ : ¬ (c ≈R 0R) → Because p c n
        norm₂ : ¬ (n ≈N 0N) → Because p c n

    data Normalised-HNF {k} : HNF (suc k) → Set where
        ∅ : Normalised-HNF ∅
        _*x+_·x+_by_ :
            Normalised-HNF p → (c : A) → Normalised n → Because p c n → Normalised-HNF (p *x+ c ·x+ n)

    data Normalised : Normal k → Set where
        zero : Normalised zero
        poly : {p : HNF (suc k)} → Normalised-HNF p → Normalised (poly p) 

infix 10 _*x+_·x+HN′_
_*x+_·x+HN′_ :
    Normalised-HNF p →
    (c : A) →
    Normalised n →
    --------------------------------------------
    Normalised-HNF (p *x+ c ·x+HN n)

_*x+_·x+HN′_ ∅ c _
    with c ≟R 0R
_*x+_·x+HN′_ {p = ∅} {n = zero} _ _ _ | yes _ = ∅
_*x+_·x+HN′_ {p = ∅} {n = poly ∅} _ _ _ | yes _ = ∅
_*x+_·x+HN′_ {p = ∅} {n = poly (_ *x+ _ ·x+ _)} _ c n | yes c≈0 = ∅ *x+ c ·x+ n by norm₂ λ { (poly ()) }
_*x+_·x+HN′_ {p = ∅} _ c n | no ¬c≈0 = ∅ *x+ c ·x+ n by norm₁ ¬c≈0
_*x+_·x+HN′_ {p = _ *x+ _ ·x+ _} p c n = p *x+ c ·x+ n by norm₀ λ { () }

normalised-0N : Normalised (0N {k})
normalised-0N {k = zero} = zero
normalised-0N {k = suc k} = poly ∅

normalised-var : (x : Var k) → Normalised (normalise-var x)
normalised-var zero = poly (∅ *x+ 1R ·x+ normalised-0N by norm₁ 1≉0)
normalised-var (suc k) = poly (∅ *x+ 0R ·x+ normalised-var k by norm₂ (normalise-var-zero k))

```

# Scalar multiplication

```
mutual
    _·H′_ :
        (c : A) → 
        Normalised-HNF p →
        -----------------------
        Normalised-HNF (c ·H p)
        
    c ·H′ np with c ≟R 0R
    ...     | yes c≈0 = ∅
    _ ·H′ ∅ | no _ = ∅
    c ·H′ (p *x+ d ·x+ n by _) | no _ = (c ·H′ p) *x+ (c *R d) ·x+HN′ (c ·N′ n)

    _·N′_ :
        (c : A) → 
        Normalised n →
        -------------------
        Normalised (c ·N n)

    c ·N′ zero = zero
    c ·N′ poly p = poly (c ·H′ p)
```

# Addition

```
mutual
    infixr 9 _+H′_ _+N′_
    _+H′_ :
        Normalised-HNF p →
        Normalised-HNF q →
        -----------------------
        Normalised-HNF (p +H q)

    ∅ +H′ q = q
    p@(_ *x+ _ ·x+ _ by _) +H′ ∅ = p
    (p *x+ c ·x+ m by _) +H′ (q *x+ d ·x+ n by _)
        = (p +H′ q) *x+ _ ·x+HN′ (m +N′ n)

    _+N′_ :
        Normalised m →
        Normalised n →
        -------------------
        Normalised (m +N n)

    zero +N′ zero = zero
    poly np +N′ poly nq = poly (np +H′ nq)

_*x+HN′_ : Normalised-HNF p → Normalised n → Normalised-HNF (p *x+HN n)
_*x+HN′_ {p = ∅} {n = n} np nn with n ≟N 0N
... | yes _  = ∅
... | no ¬n≈0 = ∅ *x+ 0R ·x+ nn by norm₂ ¬n≈0
_*x+HN′_ {p = p@(_ *x+ _ ·x+ _)} {n = n} np nn = np *x+ 0R ·x+ nn by norm₀ λ { () }

infixr 9 _+HN′_
_+HN′_ : Normalised-HNF p → Normalised n → Normalised-HNF (p +HN n)
_+HN′_ {p = ∅} {n = n} _ nn = ∅ *x+ 0R ·x+HN′ nn
_+HN′_ {p = p *x+ c ·x+ m} (np *x+ .c ·x+ nm by _) nn = np *x+ c ·x+HN′ (nm +N′ nn)
```

# Product

```
mutual
    infixr 10 _*H′_ _*N′_ _*HN′_ _*NH′_

    _*NH′_ : Normalised n → Normalised-HNF p → Normalised-HNF (n *NH p)
    _*NH′_ {p = ∅} _ _ = ∅
    _*NH′_ {n = n} {p = p *x+ c ·x+ n′} nn (np *x+ .c ·x+ nn′ by _)
        with n ≟N 0N
    ... | yes _ = ∅
    ... | no _
        with c ≟R 0R
    ... | yes _ = (nn *NH′ np) *x+HN′ (nn *N′ nn′)
    ... | no _ = ((nn *NH′ np) +HN′ (c ·N′ nn)) *x+HN′ (nn *N′ nn′)

    _*HN′_ : Normalised-HNF p → Normalised n → Normalised-HNF (p *HN n)
    _*HN′_ {p = ∅} _ _ = ∅
    _*HN′_ {p = p *x+ c ·x+ n} {n = n′} (np *x+ .c ·x+ nn by _) nn′
        with n′ ≟N 0N
    ... | yes _ = ∅
    ... | no _
        with c ≟R 0R
    ... | yes _ = (np *HN′ nn′) *x+HN′ (nn *N′ nn′)
    ... | no _ = ((np *HN′ nn′) +HN′ (c ·N′ nn′)) *x+HN′ (nn *N′ nn′)

    _*H′_ :
        Normalised-HNF p →
        Normalised-HNF q →
        -----------------------
        Normalised-HNF (p *H q)

    ∅ *H′ q = ∅
    p@(_ *x+ _ ·x+ _ by _) *H′ ∅ = ∅
    (p₁ *x+ c₁ ·x+ n₁ by _) *H′ (p₂ *x+ c₂ ·x+ n₂ by _) =
        ((p₁ *H′ p₂ +H′ c₂ ·H′ p₁ +H′ c₁ ·H′ p₂) *x+ c₁ *R c₂ ·x+HN′ (c₁ ·N′ n₂ +N′ c₂ ·N′ n₁) +H′ p₁ *HN′ n₂ +H′ n₁ *NH′ p₂) *x+HN′ (n₁ *N′ n₂)

    _*N′_ :
        Normalised m →
        Normalised n →
        -------------------
        Normalised (m *N n)

    zero *N′ zero = zero
    poly p *N′ poly q = poly (p *H′ q)

normalised : (p : Term′ k) → Normalised (normalise p)
normalised 0T = normalised-0N
normalised (var x) = normalised-var x
normalised (c · p) = c ·N′ normalised p
normalised (p + q) = normalised p +N′ normalised q
normalised (p * q) = normalised p *N′ normalised q

normalised-*x+·x+HN :
    Normalised-HNF (p *x+ c ·x+ n) →
    --------------------------------
    p *x+ c ·x+ n ≡ p *x+ c ·x+HN n

normalised-*x+·x+HN {p = ∅} (_ *x+ _ ·x+ _ by norm₀ ¬p≈0) = ⊥-elim (¬p≈0 ∅)
normalised-*x+·x+HN {p = _ *x+ _ ·x+ _} (_ *x+ _ ·x+ _ by norm₀ _) = refl

normalised-*x+·x+HN {p = ∅} {c} (_ *x+ _ ·x+ _ by norm₁ ¬c≈0)
    with c ≟R 0R
... | yes c≈0 = ⊥-elim (¬c≈0 c≈0)
... | no _ = refl
normalised-*x+·x+HN {p = (_ *x+ _ ·x+ _)} _ = refl

normalised-*x+·x+HN {p = ∅} {n = zero} (_ *x+ _ ·x+ _ by norm₂ ¬n≈0) = ⊥-elim (¬n≈0 zero)
normalised-*x+·x+HN {p = ∅} {n = poly ∅} (_ *x+ _ ·x+ _ by norm₂ ¬n≈0) = ⊥-elim (¬n≈0 (poly ∅))
normalised-*x+·x+HN {p = ∅} {c = c} {n = poly (_ *x+ _ ·x+ _)} (_ *x+ _ ·x+ _ by norm₂ ¬n≈0)
    with c ≟R 0R
... | yes c≈0 = refl
... | no _ = refl
```
