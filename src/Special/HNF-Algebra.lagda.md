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
    (1≉0 : let open Preliminaries.Algebra R in ¬ (1R ≈R 0R))
    (no-zero-divisors : let open Preliminaries.Algebra R in
        ∀ {a b} → a *R b ≈R 0R → a ≈R 0R ⊎ b ≈R 0R)
    (_≟R_ : let open Preliminaries.Algebra R in Decidable _≈R_)
    where

open Preliminaries.Algebra R
open import General.Terms R hiding (x)
open import Special.Polynomials R
open import Special.HNF R
open import Special.DecidableEquivalence R _≟R_
open import Special.AuxiliaryLemmas R
open import Special.HNF-Normalised R 1≉0 _≟R_

private variable
    X Y Z : Set
    m n k : ℕ

zero-nonzero :
    {c₁ c₂ : A} {B : Set} →
    c₁ ≈R 0R → c₁ ≈R c₂ → ¬ c₂ ≈R 0R → B

zero-nonzero c₁≈0 c₁≈c₂ ¬c₂≈0 = ⊥-elim $ ¬c₂≈0 $ R-sym c₁≈c₂ ⟨ R-trans ⟩ c₁≈0

zero-nonzero′ :
    {c₁ c₂ : A} {B : Set} →
    c₂ ≈R 0R → c₁ ≈R c₂ → ¬ c₁ ≈R 0R → B

zero-nonzero′ c₂≈0 c₁≈c₂ ¬c₁≈0 = ⊥-elim $ ¬c₁≈0 $ c₁≈c₂ ⟨ R-trans ⟩ c₂≈0

no-zero-divisors-conv :
    {a b : A} →
    ¬ (a ≈R 0R) → ¬ (b ≈R 0R) → ¬ (a *R b ≈R 0R)

no-zero-divisors-conv ¬a≈0 ¬b≈0 a*b≈0
    with no-zero-divisors a*b≈0
... | inj₁ a≈0 = ¬a≈0 a≈0
... | inj₂ b≈0 = ¬b≈0 b≈0
```

# Scalar multiplication

```
mutual
    0·p≡0H : (p : HNF (suc k)) → 0R ·H p ≡ 0H
    0·p≡0H _ with 0R ≟R 0R
    ... | yes _ = refl
    0·p≡0H _ | no ¬0≈0 = ⊥-elim (¬0≈0 R-refl)
    
    0·n≡0N : (n : Normal k) → 0R ·N n ≡ 0N
    0·n≡0N zero = refl
    0·n≡0N (poly p) = {!   !} -- poly (0·p≡0H p)

c≈0→c·p≡0H : ∀ {c} {p : HNF (suc k)} → c ≈R 0R → c ·H p ≡ 0H
c≈0→c·p≡0H {c = c} c≈0 with c ≟R 0R
... | yes _ = refl
... | no c≉0 = ⊥-elim (c≉0 c≈0)

c≈0→c·n≡0N : ∀ {c} {n : Normal k} → c ≈R 0R → c ·N n ≡ 0N
c≈0→c·n≡0N {c = c} c≈0 with c ≟R 0R
c≈0→c·n≡0N {n = zero} _ | yes _ = refl
c≈0→c·n≡0N {n = poly _} c≈0 | yes _ = cong poly (c≈0→c·p≡0H c≈0)
... | no c≉0 = ⊥-elim (c≉0 c≈0)

mutual
    ·H-zero : (p : HNF (suc k)) → 0R ·H p ≈H 0H
    ·H-zero _ with 0R ≟R 0R
    ... | yes _ = ∅
    ·H-zero _ | no ¬0≈0 = ⊥-elim (¬0≈0 R-refl)
    
    ·N-zero : (n : Normal k) → 0R ·N n ≈N 0N
    ·N-zero zero = zero
    ·N-zero (poly p) = poly (·H-zero p)

c·0≈0H : ∀ {c} → c ·H 0H ≈H 0H {k}
c·0≈0H {k} {c} with c ≟R 0R
... | yes _ = ∅
... | no _ = ∅

p≈0→c·p≈0H : ∀ {c} {p : HNF (suc k)} → p ≈H 0H → c ·H p ≈H 0H {k}
p≈0→c·p≈0H ∅ = c·0≈0H

p≉0,c≉0→c·p≉0H : ∀ {c} {p : HNF (suc k)} → ¬ (c ≈R 0R) → ¬ (p ≈H 0H) → ¬ (c ·H p ≈H 0H)
p≉0,c≉0→c·p≉0H = {!   !}

c·0≡0H : ∀ {c} → c ·H 0H ≡ 0H {k}
c·0≡0H {k} {c} with c ≟R 0R
... | yes _ = refl
... | no _ = refl

p≈0→c·p≡0H : ∀ {c} {p : HNF (suc k)} → p ≈H 0H → c ·H p ≡ 0H {k}
p≈0→c·p≡0H ∅ = c·0≡0H

c·0≈0N : ∀ {c} → c ·N 0N ≈N 0N {k}
c·0≈0N {zero} = zero
c·0≈0N {suc k} = poly c·0≈0H

n≈0→c·n≈0N : ∀ {c} {n : Normal k} → n ≈N 0N → c ·N n ≈N 0N {k}
n≈0→c·n≈0N {c = c} zero = c·0≈0N {c = c}
n≈0→c·n≈0N (poly ∅) = c·0≈0N

n≉0,c≉0→c·n≉0N : ∀ {c} {n : Normal k} → ¬ (c ≈R 0R) → ¬ (n ≈N 0N) → ¬ (c ·N n ≈N 0N)
n≉0,c≉0→c·n≉0N = {!   !}
```

# Simplifying constructor

```
*x+·x+HN-cong :
    {p₁ p₂ : HNF (suc k)} {c₁ c₂ : A} {n₁ n₂ : Normal k} →
    p₁ ≈H p₂ →
    c₁ ≈R c₂ →
    n₁ ≈N n₂ →
    --------------------------------------------
    p₁ *x+ c₁ ·x+HN n₁ ≈H p₂ *x+ c₂ ·x+HN n₂

*x+·x+HN-cong {c₁ = c₁} {c₂} ∅ c₁≈c₂ n₁≈n₂
    with c₁ ≟R 0R | c₂ ≟R 0R
... | yes c₁≈0 | no ¬c₂≈0 = zero-nonzero c₁≈0 c₁≈c₂ ¬c₂≈0
... | no ¬c₁≈0 | yes c₂≈0 = zero-nonzero′ c₂≈0 c₁≈c₂ ¬c₁≈0
... | no _ | no _ = ∅ *x+ c₁≈c₂ ·x+ n₁≈n₂
*x+·x+HN-cong {c₁ = _} {_} ∅ c₁≈c₂ zero | yes _ | yes _ = ∅
*x+·x+HN-cong {c₁ = _} {_} ∅ c₁≈c₂ (poly ∅) | yes _ | yes _ = ∅
*x+·x+HN-cong {c₁ = c₁} {c₂} ∅ c₁≈c₂ eq@(poly (p₁≈p₂ *x+ c₃≈c₄ ·x+ n₁≈n₂)) | yes _ | yes _ = ∅ *x+ c₁≈c₂ ·x+ eq

*x+·x+HN-cong {c₁ = c₁} {c₂} (p₁≈p₂ *x+ x₁ ·x+ x₂) c₁≈c₂ n₁≈n₂ = (p₁≈p₂ *x+ x₁ ·x+ x₂) *x+ c₁≈c₂ ·x+ n₁≈n₂
```

```
+HN-cong :
    {p q : HNF (suc n)} {m n : Normal n} →
    p ≈H q →
    m ≈N n →
    -------------------------------
    p +HN m ≈H q +HN n

+HN-cong = {!   !} 
```

```
*x+HN-cong :
    {p q : HNF (suc k)} {m n : Normal k} →
    p ≈H q →
    m ≈N n →
    -------------------------------------
    p *x+HN m ≈H q *x+HN n

*x+HN-cong p≈q m≈n = {!   !}
```

```
mutual
    ·H-cong :
        {c₁ c₂ : A} {p₁ p₂ : HNF (suc k)} →
        c₁ ≈R c₂ →
        p₁ ≈H p₂ →
        -----------------------------------
        c₁ ·H p₁ ≈H c₂ ·H p₂

    ·H-cong {c₁ = c₁} {c₂} c₁≈c₂ p₁≈p₂
        with c₁ ≟R 0R | c₂ ≟R 0R
    ... | yes c₁≈0 | no ¬c₂≈0 = zero-nonzero c₁≈0 c₁≈c₂ ¬c₂≈0
    ... | no ¬c₁≈0 | yes c₂≈0 = zero-nonzero′ c₂≈0 c₁≈c₂ ¬c₁≈0
    ... | yes _ | yes _ = ∅
    ·H-cong _ ∅ | no _ | no _ = ∅
    ·H-cong c₁≈c₂ (p₁≈p₂ *x+ c₃≈c₄ ·x+ n≈n₂) | no _ | no _ =
        *x+·x+HN-cong (·H-cong c₁≈c₂ p₁≈p₂) (*R-cong c₁≈c₂ c₃≈c₄) (·N-cong c₁≈c₂ n≈n₂)
    
    ·N-cong : 
        {c₁ c₂ : A} {p₁ p₂ : Normal k} →
        c₁ ≈R c₂ →
        p₁ ≈N p₂ →
        --------------------------------
        (c₁ ·N p₁) ≈N (c₂ ·N p₂)

    ·N-cong c≈d zero = zero
    ·N-cong c≈d (poly p≈q) = poly (·H-cong c≈d p≈q)
```

```
zero-ring : 1R ≈R 0R → ∀ c → c ≈R 0R
zero-ring 1≈0 c =
    begin
        c
            ≈⟨ *R-identityʳ _ ⟨
        c *R 1R
            ≈⟨ (R-refl ⟨ *R-cong ⟩ 1≈0) ⟩
        c *R 0R
            ≈⟨ R-zeroʳ _ ⟩
        0R
    ∎ where open EqR

trivial : 1R ≈R 0R → (p : HNF (suc k)) → ∀ c → c ·H p ≈H 0H
trivial 1≈0 p c = 
    begin
        c ·H p
            ≈⟨ ·H-cong (zero-ring 1≈0 c) ≈H-refl ⟩
        0R ·H p
            ≈⟨ ·H-zero _ ⟩
        0H
    ∎ where open EqH

-- 1. do we need to assume 1 ≉ 0 from the outset?
-- 2. 1R ·H p ≈H p may be different since 1R ·H p may induce simplifications.

-- mutual
--     ·H-one : (p : HNF (suc k)) → 1R ·H p ≈H p
--     ·H-one p with 1R ≟R 0R
--     ... | yes 1≈0 = ≈H-sym {!(trivial 1≈0 p 1R) !}
--     ·H-one ∅ | no _ = ∅
--     ·H-one (p *x+ c ·x+ n) | no _ =
--         begin
--             (1R ·H p) *x+ 1R *R c ·x+HN (1R ·N n)
--                 ≈⟨ *x+·x+HN-cong (·H-one p) (*R-identityˡ _) (·N-one n) ⟩
--             p *x+ c ·x+HN n
--                 ≈⟨ {!   !} ⟩
--             p *x+ c ·x+ n
--         ∎ where open EqH
    
--     ·N-one : (n : Normal k) → (1R ·N n) ≈N n
--     ·N-one zero = zero
--     ·N-one (poly p) = poly (·H-one p)

poly-inv : {p q : HNF (suc k)} → poly p ≡ poly q → p ≡ q
poly-inv refl = refl

*x+·x+-inv :
    {p q : HNF (suc k)} {c d : A} {m n : Normal k} →
    p *x+ c ·x+ m ≡ q *x+ d ·x+ n →
    p ≡ q × c ≡ d × m ≡ n
*x+·x+-inv refl = refl ,, refl ,, refl

poly-*x+·x+-inv :
    ∀ {p q : HNF (suc k)} {c d : A} {m n : Normal k} →
    _≡_ {A = Normal (suc k)} (poly (p *x+ c ·x+ m)) (poly (q *x+ d ·x+ n)) →
    p ≡ q × c ≡ d × m ≡ n

poly-*x+·x+-inv refl = refl ,, refl ,, refl

*x+·x+HN-nonzero₀ :
    {p : HNF (suc k)} {c : A} {n : Normal k} →
    ¬ (p ≈H 0H) →
    --------------------------------
    p *x+ c ·x+HN n ≡ p *x+ c ·x+ n

*x+·x+HN-nonzero₀ = {!   !}

*x+·x+HN-nonzero₁ :
    {p : HNF (suc k)} {c : A} {n : Normal k} →
    ¬ (c ≈R 0R) →
    --------------------------------
    p *x+ c ·x+HN n ≡ p *x+ c ·x+ n

*x+·x+HN-nonzero₁ {p = ∅} {c} ¬c≈0
    with c ≟R 0R
... | yes c≈0 = ⊥-elim (¬c≈0 c≈0)
... | no _ = refl
*x+·x+HN-nonzero₁ {p = p@(_ *x+ _ ·x+ _)} ¬c≈0 = refl

*x+·x+HN-nonzero₂ :
    {p : HNF (suc k)} {c : A} {n : Normal k} →
    ¬ (n ≈N 0N) →
    --------------------------------
    p *x+ c ·x+HN n ≡ p *x+ c ·x+ n

*x+·x+HN-nonzero₂ = {!   !}

*x+·x+HN-zero :
    {p : HNF (suc k)} {c : A} {n : Normal k} →
    p ≈H 0H →
    c ≈R 0R →
    n ≈N 0N →
    --------------------------------
    p *x+ c ·x+HN n ≡ 0H

*x+·x+HN-zero = {!   !}

·H-nonzero-∅ :
    {c : A} →
    ¬ (c ≈R 0R) →
    -------------
    c ·H ∅ ≡ ∅ {k}

·H-nonzero-∅ {c = c} ¬c≈0 with c ≟R 0R
... | yes c≈0 = ⊥-elim (¬c≈0 c≈0)
... | no _ = refl

·H-nonzero :
    {c d : A} {p : HNF (suc k)} {n : Normal k} →
    ¬ (c ≈R 0R) →
    ---------------------------------------------------------
    c ·H (p *x+ d ·x+ n) ≡ (c ·H p) *x+ (c *R d) ·x+HN (c ·N n)

·H-nonzero {c = c} {d} {p} {n} ¬c≈0
    with c ≟R 0R in eq
... | yes c≈0 = ⊥-elim (¬c≈0 c≈0)
... | no _ rewrite eq = refl

·H-nonzero′ :
    {c d : A} {p : HNF (suc k)} {n : Normal k} →
    ¬ (c ≈R 0R) →
    ¬ (d ≈R 0R) → -- do we need this assumption?
    ---------------------------------------------------------
    c ·H (p *x+ d ·x+HN n) ≡ (c ·H p) *x+ (c *R d) ·x+HN (c ·N n)

·H-nonzero′ {c = c} {d} {p} {n} ¬c≈0 ¬d≈0 =
    begin 
        c ·H (p *x+ d ·x+HN n)
            ≡⟨ cong (c ·H_) (*x+·x+HN-nonzero₁ ¬d≈0) ⟩
        c ·H (p *x+ d ·x+ n)
            ≡⟨ ·H-nonzero ¬c≈0 ⟩
        (c ·H p) *x+ (c *R d) ·x+HN (c ·N n)
    ∎ where open ≡-Eq

·H-nonzero′′ :
    {c d : A} {p : HNF (suc k)} {n : Normal k} →
    ¬ (c ≈R 0R) →
    ---------------------------------------------------------
    c ·H (p *x+ d ·x+HN n) ≡ (c ·H p) *x+ (c *R d) ·x+HN (c ·N n)

·H-nonzero′′ {c = c} {d} {p} {n} ¬c≈0 =
    go (p ≟H 0H) (d ≟R 0R) (n ≟N 0N) where

    go : Dec (p ≈H 0H) → Dec (d ≈R 0R) → Dec (n ≈N 0N) →
         c ·H (p *x+ d ·x+HN n) ≡ (c ·H p) *x+ (c *R d) ·x+HN (c ·N n)
    go (yes p≈0) (yes d≈0) (yes n≈0) =
        begin
            c ·H (p *x+ d ·x+HN n)
                ≡⟨ cong (c ·H_) (*x+·x+HN-zero p≈0 d≈0 n≈0) ⟩
            c ·H 0H
                ≡⟨ c·0≡0H ⟩
            0H
                ≡⟨ *x+·x+HN-zero (p≈0→c·p≈0H p≈0) (*-≈-zeroʳ d≈0) (n≈0→c·n≈0N n≈0) ⟨
            (c ·H p) *x+ c *R d ·x+HN (c ·N n)
        ∎ where open ≡-Eq

    go _ _ (no ¬n≈0) =
        begin
            c ·H (p *x+ d ·x+HN n)
                ≡⟨ cong (c ·H_) (*x+·x+HN-nonzero₂ ¬n≈0) ⟩
            c ·H (p *x+ d ·x+ n)
                ≡⟨ ·H-nonzero ¬c≈0 ⟩
            (c ·H p) *x+ c *R d ·x+HN (c ·N n)
        ∎ where open ≡-Eq
        
    go _ (no ¬d≈0) _ =
        begin
            c ·H (p *x+ d ·x+HN n)
                ≡⟨ cong (c ·H_) (*x+·x+HN-nonzero₁ ¬d≈0) ⟩
            c ·H (p *x+ d ·x+ n)
                ≡⟨ ·H-nonzero ¬c≈0 ⟩
            (c ·H p) *x+ c *R d ·x+HN (c ·N n)
        ∎ where open ≡-Eq
        
    go (no ¬p≈0) _ _ =
                begin
            c ·H (p *x+ d ·x+HN n)
                ≡⟨ cong (c ·H_) (*x+·x+HN-nonzero₀ ¬p≈0) ⟩
            c ·H (p *x+ d ·x+ n)
                ≡⟨ ·H-nonzero ¬c≈0 ⟩
            (c ·H p) *x+ c *R d ·x+HN (c ·N n)
        ∎ where open ≡-Eq

-- removed all assumptions on c, d, p, n
*x+·x+HN-scalar :
    {c d : A} {p : HNF (suc k)} {n : Normal k} →
    ------------------------------------------------------------
    c ·H (p *x+ d ·x+HN n) ≡ (c ·H p) *x+ (c *R d) ·x+HN (c ·N n)

*x+·x+HN-scalar {c = c} {d} {p} {n} = go (c ≟R 0R) where

    go : _ → _
    go (yes c≈0) =
        begin
            c ·H (p *x+ d ·x+HN n)
                ≡⟨ c≈0→c·p≡0H  c≈0 ⟩
            0H
                ≡⟨ *x+·x+HN-zero (≡→≈H (c≈0→c·p≡0H c≈0)) (*-≈-zeroˡ c≈0) (≡→≈N (c≈0→c·n≡0N c≈0)) ⟨
            (c ·H p) *x+ c *R d ·x+HN (c ·N n)
        ∎ where open ≡-Eq

    go (no ¬c≈0) = ·H-nonzero′′ ¬c≈0

-- this is just false since on the right there is no chance of simplification
-- ·H-nonzero :
--     {c d : A} {p : HNF (suc k)} {n : Normal k} →
--     ¬ (c ≈R 0R) →
--     ¬ (d ≈R 0R) →
--     ---------------------------------------------------------
--     c ·H (p *x+ d ·x+ n) ≡ (c ·H p) *x+ (c *R d) ·x+ (c ·N n)

·H-nonzero-∅′ :
    {c d : A} {n : Normal k} →
    ¬ (c ≈R 0R) →
    ¬ (d ≈R 0R) → 
    --------------------------------------------------
    c ·H (∅ *x+ d ·x+ n) ≡ ∅ *x+ (c *R d) ·x+ (c ·N n)

·H-nonzero-∅′ = {!   !}

·H-nonzero-zero-∅′ :
    {c : A} {n : Normal k} →
    ¬ (c ≈R 0R) →
    ---------------------------------------------
    c ·H (∅ *x+ 0R ·x+ n) ≡ ∅ *x+ 0R ·x+ (c ·N n)

·H-nonzero-zero-∅′ = {!   !}
```

```
mutual
    *-·-distribH :
        ∀ c d (p : HNF (suc k)) →
        ------------------------------
        (c *R d) ·H p ≈H c ·H (d ·H p)

    *-·-distribH c d ∅ =
        begin
            (c *R d) ·H ∅ ≡⟨ c·0≡0H ⟩
            ∅ ≡⟨ c·0≡0H ⟨
            c ·H ∅ ≡⟨ cong (c ·H_) c·0≡0H ⟨
            c ·H (d ·H ∅)
        ∎ where open EqH
    *-·-distribH c d p@(q *x+ e ·x+ n) = go (c ≟R 0R) (d ≟R 0R) where
        go : _ → _ → (c *R d) ·H p ≈H c ·H (d ·H p)

        go (yes c≈0) _ =
            begin
                (c *R d) ·H p ≡⟨ c≈0→c·p≡0H (*-≈-zeroˡ c≈0) ⟩
                0H ≡⟨ c≈0→c·p≡0H c≈0 ⟨
                c ·H (d ·H p)
            ∎ where open EqH

        go _ (yes d≈0) =
            begin
                (c *R d) ·H p ≡⟨ c≈0→c·p≡0H (*-≈-zeroʳ d≈0) ⟩
                0H ≡⟨ c·0≡0H ⟨
                c ·H 0H ≡⟨ cong (c ·H_) (c≈0→c·p≡0H d≈0) ⟨
                c ·H (d ·H p)
            ∎ where open EqH

        go (no c≉0) (no d≉0) = 
            begin
                (c *R d) ·H (q *x+ e ·x+ n)
                    ≡⟨ ·H-nonzero (no-zero-divisors-conv c≉0 d≉0) ⟩
                ((c *R d) ·H q) *x+ ((c *R d) *R e) ·x+HN ((c *R d) ·N n)
                    ≈⟨ *x+·x+HN-cong (*-·-distribH _ _ _) (*R-assoc _ _ _) (*-·-distribN _ _ _) ⟩
                (c ·H (d ·H q)) *x+ (c *R (d *R e)) ·x+HN (c ·N (d ·N n))
                    ≡⟨ *x+·x+HN-scalar ⟨
                c ·H ((d ·H q) *x+ (d *R e) ·x+HN (d ·N n))
                    ≡⟨ cong (c ·H_) (·H-nonzero d≉0) ⟨
                c ·H (d ·H (q *x+ e ·x+ n))
            ∎ where open EqH

    *-·-distribN :
        ∀ c d (n : Normal k) →
        ------------------------------
        (c *R d) ·N n ≈N c ·N (d ·N n)

    *-·-distribN c d zero = zero
    *-·-distribN c d (poly p) = poly (*-·-distribH c d p)

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
    ... | yes c≈0 | no ¬d≈0 = zero-nonzero c≈0 c≈d ¬d≈0
    ... | no ¬c≈0 | yes d≈0 = zero-nonzero′ d≈0 c≈d ¬c≈0

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
```

# Addition

## Zero

```
0+p≡pH :
    ∀ (p : HNF (suc k)) →
    ---------------------
    0H +H p ≡ p

0+p≡pH ∅ = refl
0+p≡pH (p *x+ e ·x+ n) = refl

p+0≡pH :
    ∀ (p : HNF (suc k)) →
    ---------------------
    p +H 0H ≡ p

p+0≡pH ∅ = refl
p+0≡pH (p *x+ e ·x+ n) = refl

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

p≈0→p+q≈q :
    {p q : HNF (suc k)} →
    p ≈H 0H →
    ---------------------
    p +H q ≈H q

p≈0→p+q≈q p≈0 = {!   !}

q≈0→p+q≈p :
    {p q : HNF (suc k)} →
    q ≈H 0H →
    ---------------------
    p +H q ≈H p

q≈0→p+q≈p q≈0 = {!   !}

m≈0→m+n≈n :
    {m n : Normal k} →
    m ≈N 0N →
    ---------------------
    m +N n ≈N n

m≈0→m+n≈n m≈0 = {!   !}

n≈0→m+n≈m :
    {m n : Normal k} →
    n ≈N 0N →
    ---------------------
    m +N n ≈N m

n≈0→m+n≈m n≈0 = {!   !}

p,q≈0→p+q≈0H : 
    {p q : HNF (suc k)} →
    p ≈H 0H →
    q ≈H 0H →
    ---------------------
    p +H q ≈H 0H

p,q≈0→p+q≈0H p≈0 q≈0 = {!   !}

m,n≈0→m+n≈0N : 
    {m n : Normal k} →
    m ≈N 0N →
    n ≈N 0N →
    ------------------
    m +N n ≈N 0N

m,n≈0→m+n≈0N m≈0 n≈0 = {!   !}
```



```
*x+·x+HN-add :
    (p q : HNF (suc k)) (c d : A) (m n : Normal k) →
    -----------------------------------------------------------------------------
    (p *x+ c ·x+HN m) +H (q *x+ d ·x+HN n) ≈H (p +H q) *x+ (c +R d) ·x+HN (m +N n)  

*x+·x+HN-add p q c d m n =
    go (p ≟H 0H) (q ≟H 0H) (c ≟R 0R) (d ≟R 0R) (m ≟N 0N) (n ≟N 0N) where

    because : _ → _ → _
    because x y = ≡→≈H (x ⟨ cong₂ _+H_ ⟩ y)

    go : _ → _ → _ → _ → _ → _ → _
    go (no p≉0) (no q≉0) _ _ _ _ = *x+·x+HN-nonzero₀ p≉0 ⟨ because ⟩ *x+·x+HN-nonzero₀ q≉0
    go (no p≉0) _ _ (no d≉0) _ _ = *x+·x+HN-nonzero₀ p≉0 ⟨ because ⟩ *x+·x+HN-nonzero₁ d≉0
    go (no p≉0) _ _ _ _ (no n≉0) = *x+·x+HN-nonzero₀ p≉0 ⟨ because ⟩ *x+·x+HN-nonzero₂ n≉0

    go _ (no q≉0) (no c≉0) _ _ _ = *x+·x+HN-nonzero₁ c≉0 ⟨ because ⟩ *x+·x+HN-nonzero₀ q≉0
    go _ _ (no c≉0) (no d≉0) _ _ = *x+·x+HN-nonzero₁ c≉0 ⟨ because ⟩ *x+·x+HN-nonzero₁ d≉0
    go _ _ (no c≉0) _ _ (no n≉0) = *x+·x+HN-nonzero₁ c≉0 ⟨ because ⟩ *x+·x+HN-nonzero₂ n≉0

    go _ (no q≉0) _ _ (no m≉0) _ = *x+·x+HN-nonzero₂ m≉0 ⟨ because ⟩ *x+·x+HN-nonzero₀ q≉0
    go _ _ _ (no d≉0) (no m≉0) _ = *x+·x+HN-nonzero₂ m≉0 ⟨ because ⟩ *x+·x+HN-nonzero₁ d≉0
    go _ _ _ _ (no m≉0) (no n≉0) = *x+·x+HN-nonzero₂ m≉0 ⟨ because ⟩ *x+·x+HN-nonzero₂ n≉0

    go (yes p≈0) _ (yes c≈0) _ (yes m≈0) _ =
        begin
            (p *x+ c ·x+HN m) +H (q *x+ d ·x+HN n)
                ≡⟨ *x+·x+HN-zero p≈0 c≈0 m≈0 ⟨ cong₂ _+H_ ⟩ refl ⟩
            0H +H q *x+ d ·x+HN n
                ≡⟨ 0+p≡pH _ ⟩
            q *x+ d ·x+HN n
                ≈⟨ *x+·x+HN-cong (p≈0→p+q≈q p≈0) (a≈0→a+b≈b c≈0) (m≈0→m+n≈n m≈0) ⟨
            (p +H q) *x+ (c +R d) ·x+HN (m +N n)
        ∎ where open EqH

    go _ (yes q≈0) _ (yes d≈0) _ (yes n≈0) =
        begin
            (p *x+ c ·x+HN m) +H (q *x+ d ·x+HN n)
                ≡⟨ (refl {x = p *x+ c ·x+HN m} ⟨ cong₂ _+H_ ⟩ *x+·x+HN-zero q≈0 d≈0 n≈0) ⟩
            (p *x+ c ·x+HN m) +H 0H
                ≡⟨ p+0≡pH (p *x+ c ·x+HN m) ⟩
            p *x+ c ·x+HN m
                ≈⟨ *x+·x+HN-cong (q≈0→p+q≈p {p = p} q≈0) (b≈0→a+b≈a d≈0) (n≈0→m+n≈m n≈0) ⟨
            (p +H q) *x+ (c +R d) ·x+HN (m +N n)
        ∎ where open EqH

*x+·x+HN-add₀ :
    (p q : HNF (suc k)) (c d : A) (m n : Normal k) →
    Normalised-HNF (q *x+ d ·x+ n) →
    --------------------------------------------------------------------------
    (p *x+ c ·x+HN m) +H (q *x+ d ·x+ n) ≈H (p +H q) *x+ (c +R d) ·x+HN (m +N n)

*x+·x+HN-add₀ p q c d m n norm =
    begin
        (p *x+ c ·x+HN m) +H (q *x+ d ·x+ n)
            ≡⟨ refl {x = p *x+ c ·x+HN m} ⟨ cong₂ _+H_ ⟩ normalised-*x+·x+HN norm ⟩
        (p *x+ c ·x+HN m) +H (q *x+ d ·x+HN n)
            ≈⟨ *x+·x+HN-add p q c d m n ⟩
        (p +H q) *x+ (c +R d) ·x+HN (m +N n)
    ∎ where open EqH

    -- go (p ≟H 0H) (c ≟R 0R) (m ≟N 0N) where

    -- because : _ → _
    -- because x = ≡→≈H (x ⟨ cong₂ _+H_ ⟩ refl)

    -- go : _ → _ → _ → _
    -- go (no p≉0) _ _ = because $ *x+·x+HN-nonzero₀ p≉0
    -- go _ (no c≉0) _ = because $ *x+·x+HN-nonzero₁ c≉0
    -- go _ _ (no m≉0) = because $ *x+·x+HN-nonzero₂ m≉0

    -- go (yes p≈0) (yes c≈0) (yes m≈0) =
    --     begin
    --         (p *x+ c ·x+HN m) +H (q *x+ d ·x+ n)
    --             ≡⟨ *x+·x+HN-zero p≈0 c≈0 m≈0 ⟨ cong₂ _+H_ ⟩ refl ⟩
    --         0H +H q *x+ d ·x+ n
    --             ≡⟨ 0+p≡pH _ ⟩
    --         q *x+ d ·x+ n
    --             ≈⟨ {!   !} ⟨
    --         q *x+ d ·x+HN n
    --             ≈⟨ *x+·x+HN-cong (p≈0→p+q≈q p≈0) (a≈0→a+b≈b c≈0) (m≈0→m+n≈n m≈0) ⟨
    --         (p +H q) *x+ (c +R d) ·x+HN (m +N n)
    --     ∎ where open EqH

*x+·x+HN-add₁ :
    (p q : HNF (suc k)) (c d : A) (m n : Normal k) →
    Normalised-HNF (p *x+ c ·x+ m) →
    ----------------------------------------------------------------------------
    (p *x+ c ·x+ m) +H (q *x+ d ·x+HN n) ≈H (p +H q) *x+ (c +R d) ·x+HN (m +N n)  

*x+·x+HN-add₁ p q c d m n norm =
    begin
        (p *x+ c ·x+ m) +H (q *x+ d ·x+HN n)
            ≡⟨ normalised-*x+·x+HN norm ⟨ cong₂ _+H_ ⟩ refl {x = q *x+ d ·x+HN n} ⟩
        (p *x+ c ·x+HN m) +H (q *x+ d ·x+HN n)
            ≈⟨ *x+·x+HN-add p q c d m n ⟩
        (p +H q) *x+ (c +R d) ·x+HN (m +N n)
    ∎ where open EqH

mutual

    +-·-distribH :
        ∀ (p : HNF (suc k)) c d →
        ---------------------------------
        (c +R d) ·H p ≈H c ·H p +H d ·H p

    +-·-distribH ∅ c d =
        begin
            (c +R d) ·H ∅ ≡⟨ c·0≡0H ⟩
            0H ≡⟨ 0+p≡pH _ ⟨
            0H +H 0H ≡⟨ (c·0≡0H ⟨ cong₂ _+H_ ⟩ c·0≡0H) ⟨
            c ·H ∅ +H d ·H ∅
        ∎ where open EqH

    +-·-distribH p@(q *x+ e ·x+ n) c d = go (c ≟R 0R) (d ≟R 0R) ((c +R d) ≟R 0R) where
        go : _ → _ → _ → _
        go (yes c≈0) _ _ =
            begin
                (c +R d) ·H p
                    ≈⟨ ·H-cong (a≈0→a+b≈b c≈0) ≈H-refl ⟩
                d ·H p
                    ≈⟨ p≈0→p+q≈q (≡→≈H (c≈0→c·p≡0H c≈0)) ⟨
                c ·H p +H d ·H p
            ∎ where open EqH

        go _ (yes d≈0) _ =
            begin
                (c +R d) ·H p
                    ≈⟨ ·H-cong (b≈0→a+b≈a d≈0) ≈H-refl ⟩
                c ·H p
                    ≈⟨ q≈0→p+q≈p (≡→≈H (c≈0→c·p≡0H d≈0)) ⟨
                c ·H p +H d ·H p
            ∎ where open EqH

        go (no c≉0) (no d≉0) c+d≟0 = go2 c+d≟0 where
            have : _ ≈H _
            have =
                begin
                    ((c +R d) ·H q) *x+ ((c +R d) *R e) ·x+HN ((c +R d) ·N n)
                        ≈⟨ *x+·x+HN-cong (+-·-distribH _ _ _) (R-distribʳ _ _ _) (+-·-distribN _ _ _) ⟩
                    (c ·H q +H d ·H q) *x+ (c *R e +R d *R e) ·x+HN (c ·N n +N d ·N n)
                        ≈⟨ *x+·x+HN-add (c ·H q) (d ·H q) (c *R e) (d *R e) (c ·N n) (d ·N n) ⟨
                    ((c ·H q) *x+ (c *R e) ·x+HN (c ·N n)) +H (d ·H q) *x+ (d *R e) ·x+HN (d ·N n)
                        ≡⟨ (·H-nonzero c≉0 ⟨ cong₂ _+H_ ⟩ ·H-nonzero d≉0) ⟨
                    c ·H (q *x+ e ·x+ n) +H d ·H (q *x+ e ·x+ n)
                ∎ where open EqH

            go2 : _ → _
            go2 (yes c+d≈0) =
                begin
                    (c +R d) ·H (q *x+ e ·x+ n)
                        ≡⟨ c≈0→c·p≡0H c+d≈0 ⟩
                    0H
                        ≡⟨ *x+·x+HN-zero (≡→≈H (c≈0→c·p≡0H c+d≈0)) (*-≈-zeroˡ c+d≈0) (≡→≈N (c≈0→c·n≡0N c+d≈0)) ⟨
                    ((c +R d) ·H q) *x+ ((c +R d) *R e) ·x+HN ((c +R d) ·N n)
                        ≈⟨ have ⟩
                    c ·H (q *x+ e ·x+ n) +H d ·H (q *x+ e ·x+ n)
                ∎ where open EqH

            go2 (no c+d≉0) =
                begin
                    (c +R d) ·H (q *x+ e ·x+ n)
                        ≡⟨ ·H-nonzero c+d≉0 ⟩
                    ((c +R d) ·H q) *x+ ((c +R d) *R e) ·x+HN ((c +R d) ·N n)
                        ≈⟨ have ⟩
                    c ·H (q *x+ e ·x+ n) +H d ·H (q *x+ e ·x+ n)
                ∎ where open EqH

    +-·-distribN :
        ∀ (n : Normal k) c d →
        -----------------------------
        (c +R d) ·N n ≈N c ·N n +N d ·N n

    +-·-distribN zero c d = zero
    +-·-distribN (poly p) c d = poly (+-·-distribH p c d)
```

```
mutual
    ·-+-distribH :
        (c : A) (p q : HNF (suc k)) →
        -------------------------------------
        c ·H (p +H q) ≈H (c ·H p) +H (c ·H q)

    ·-+-distribH c ∅ q =
        begin
            c ·H (∅ +H q) ≈⟨ R-refl ⟨ ·H-cong ⟩ +H-zeroˡ _ ⟩
            c ·H q ≈⟨ p≈0→p+q≈q c·0≈0H ⟨
            c ·H ∅ +H c ·H q
        ∎ where open EqH

    ·-+-distribH c p ∅ =
        begin
            c ·H (p +H ∅) ≈⟨ R-refl ⟨ ·H-cong ⟩ +H-zeroʳ _ ⟩
            c ·H p ≈⟨ q≈0→p+q≈p c·0≈0H ⟨
            c ·H p +H c ·H ∅
        ∎ where open EqH

    ·-+-distribH c p′@(p *x+ d ·x+ m) q′@(q *x+ e ·x+ n) = go (c ≟R 0R) where
        go : _ → _
        go (yes c≈0) =
            begin
                c ·H (p′ +H q′) ≡⟨ c≈0→c·p≡0H c≈0 ⟩
                0H ≈⟨ p,q≈0→p+q≈0H (≡→≈H (c≈0→c·p≡0H c≈0)) (≡→≈H (c≈0→c·p≡0H c≈0)) ⟨
                c ·H p′ +H c ·H q′
            ∎ where open EqH

        go (no c≉0) =
            begin
                c ·H (p′ +H q′)
                    ≈⟨⟩
                c ·H ((p +H q) *x+ (d +R e) ·x+HN (m +N n))
                    ≡⟨ *x+·x+HN-scalar ⟩
                (c ·H (p +H q)) *x+ (c *R (d +R e)) ·x+HN (c ·N (m +N n))
                    ≈⟨ *x+·x+HN-cong (·-+-distribH _ _ _) (R-distribˡ _ _ _) (·-+-distribN _ _ _) ⟩
                (c ·H p +H c ·H q) *x+ (c *R d +R c *R e) ·x+HN (c ·N m +N c ·N n)
                    ≈⟨ *x+·x+HN-add (c ·H p) _ _ _ _ _ ⟨
                ((c ·H p) *x+ (c *R d) ·x+HN (c ·N m)) +H
                    ((c ·H q) *x+ (c *R e) ·x+HN (c ·N n))
                    ≡⟨ (·H-nonzero c≉0 ⟨ cong₂ _+H_ ⟩ ·H-nonzero c≉0) ⟨
                c ·H p′ +H c ·H q′
            ∎ where open EqH

    ·-+-distribN :
        (c : A) (m n : Normal k) →
        -------------------------------------
        c ·N (m +N n) ≈N (c ·N m) +N (c ·N n)

    ·-+-distribN c zero zero = zero
    ·-+-distribN c (poly p) (poly q) = poly (·-+-distribH c p q)
```

## Associativity

```
mutual
    +H-assoc :
        {p q r : HNF (suc k)} →
        Normalised-HNF p →
        Normalised-HNF q →
        Normalised-HNF r →
        ------------------------------
        (p +H q) +H r ≈H p +H (q +H r)

    +H-assoc {p = ∅} {q} {r} _ _ _ =
        begin
            (0H +H q) +H r ≈⟨ +H-zeroˡ q ⟨ +H-cong ⟩ ≈H-refl ⟩
            q +H r ≈⟨ +H-zeroˡ _ ⟨
            0H +H (q +H r)
        ∎ where open EqH

    +H-assoc {p = p} {∅} {r} _ _ _ =
        begin
            (p +H 0H) +H r ≈⟨ +H-zeroʳ p ⟨ +H-cong ⟩ ≈H-refl ⟩
            p +H r ≈⟨ ≈H-refl {p = p} ⟨ +H-cong ⟩ +H-zeroˡ _ ⟨
            p +H (0H +H r)
        ∎ where open EqH

    +H-assoc {p = p} {q} {∅} _ _ _ =
        begin
            (p +H q) +H ∅ ≈⟨ +H-zeroʳ _ ⟩
            p +H q ≈⟨ ≈H-refl {p = p} ⟨ +H-cong ⟩ +H-zeroʳ _ ⟨
            p +H (q +H ∅)
        ∎ where open EqH

    +H-assoc
        {p = p′@(p *x+ c ·x+ m)} {q′@(q *x+ d ·x+ n)} {r′@(r *x+ e ·x+ o)}
        np′@(np *x+ c ·x+ nℓ by x) nq′@(nq *x+ d ·x+ nm by y) nr′@(nr *x+ e ·x+ nn by z) =
        begin
        (p′ +H q′) +H r′
            ≈⟨⟩
        ((p +H q) *x+ c +R d ·x+HN (m +N n)) +H (r *x+ e ·x+ o)
            ≈⟨ *x+·x+HN-add₀ (p +H q) _ _ _ _ _ nr′ ⟩
        ((p +H q) +H r) *x+ ((c +R d) +R e) ·x+HN ((m +N n) +N o)
            ≈⟨ *x+·x+HN-cong (+H-assoc np nq nr) (+R-assoc _ _ _) (+N-assoc nℓ nm nn) ⟩
        (p +H (q +H r)) *x+ (c +R (d +R e)) ·x+HN (m +N (n +N o))
            ≈⟨ *x+·x+HN-add₁ p _ _ _ _ _ np′ ⟨
        (p *x+ c ·x+ m) +H ((q +H r) *x+ d +R e ·x+HN (n +N o))
            ≈⟨⟩
        p′ +H (q′ +H r′)
        ∎ where open EqH

    +N-assoc :
        {m n o : Normal k} →
        Normalised m →
        Normalised n →
        Normalised o →
        -----------------------------
        (m +N n) +N o ≈N m +N (n +N o)

    +N-assoc zero zero zero =
        begin
            (zero +N zero) +N zero
                ≈⟨ +N-zeroʳ _ ⟨ +N-cong ⟩ ≈N-refl ⟩
            zero +N zero
                ≈⟨ +N-zeroˡ _ ⟩
            zero +N zero +N zero
        ∎ where open EqN
    +N-assoc (poly p) (poly q) (poly r) = poly (+H-assoc p q r)
```

## Commutativity

```
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


```

# Multiplication

```
mutual
    *H-cong :
        {p₁ p₂ q₁ q₂ : HNF (suc k)} →
        p₁ ≈H p₂ →
        q₁ ≈H q₂ →
        -----------------------------
        (p₁ *H q₁) ≈H (p₂ *H q₂)

    *H-cong = {!   !}

    *N-cong :
        {p₁ p₂ q₁ q₂ : Normal k} →
        p₁ ≈N p₂ →
        q₁ ≈N q₂ →
        --------------------------
        (p₁ *N q₁) ≈N (p₂ *N q₂)
    
    *N-cong  = {!   !}
```

```
mutual
    ·-*-distribH :
        ∀ c (p q : HNF (suc k)) →
        -----------------------------
        (c ·H p) *H q ≈H c ·H (p *H q)

    ·-*-distribH c p q = {!   !}

    ·-*-distribN :
        ∀ c (m n : Normal k) →
        ------------------------------
        (c ·N m) *N n ≈N c ·N (m *N n)

    ·-*-distribN c zero zero = zero
    ·-*-distribN c (poly p) (poly q) = poly (·-*-distribH c p q)
```

## Associativity



## Commutativity

```
mutual
    *NH-HN :
        (n : Normal k) (p : HNF (suc k)) →
        ----------------------------------
        n *NH p ≈H p *HN n

    *NH-HN _ ∅ = ∅
    *NH-HN m (p *x+ c ·x+ n)
        with m ≟N 0N
    ... | yes _ = ∅
    ... | no _
        with c ≟R 0R
    ... | yes _ = *NH-HN m p ⟨ *x+HN-cong ⟩ *N-comm m n
    ... | no _  = *NH-HN m p ⟨ +HN-cong ⟩ ≈N-refl ⟨ *x+HN-cong ⟩ *N-comm m n

    *HN-NH :
        (p : HNF (suc k)) (n : Normal k)  →
        ----------------------------------
        p *HN n ≈H n *NH p

    *HN-NH ∅ _ = ∅
    *HN-NH (p *x+ c ·x+ m) n
        with n ≟N 0N
    ... | yes _ = ∅
    ... | no _
        with c ≟R 0R
    ... | yes _ = *HN-NH p n ⟨ *x+HN-cong ⟩ *N-comm m n
    ... | no _  = *HN-NH p n ⟨ +HN-cong ⟩ ≈N-refl ⟨ *x+HN-cong ⟩ *N-comm m n

    *H-comm :
        (p q : HNF (suc k)) →
        ---------------------
        p *H q ≈H q *H p

    *H-comm ∅ ∅ = ∅
    *H-comm (_ *x+ _ ·x+ _) ∅ = ∅
    *H-comm ∅ (_ *x+ _ ·x+ _) = ∅
    *H-comm (p *x+ c ·x+ m) (q *x+ d ·x+ n) =
        begin
        (p *x+ c ·x+ m) *H (q *x+ d ·x+ n)
            ≈⟨⟩
        ((p *H q +H d ·H p +H c ·H q) *x+ c *R d ·x+HN (c ·N n +N d ·N m) +H p *HN n +H m *NH q) *x+HN (m *N n)
            ≈⟨ *x+·x+HN-cong (*H-comm p q ⟨ +H-cong ⟩ +H-comm (d ·H p) (c ·H q)) (*R-comm c d) (+N-comm (c ·N n) (d ·N m)) ⟨ +H-cong ⟩ h₀ ⟨ *x+HN-cong ⟩ *N-comm m n ⟩
        ((q *H p +H c ·H q +H d ·H p) *x+ d *R c ·x+HN (d ·N m +N c ·N n) +H q *HN m +H n *NH p) *x+HN (n *N m)
            ≈⟨⟩
        (q *x+ d ·x+ n) *H (p *x+ c ·x+ m)
        ∎ where
            open EqH

            h₀ : p *HN n +H m *NH q ≈H q *HN m +H n *NH p
            h₀ = begin
                p *HN n +H m *NH q
                    ≈⟨ +H-comm (p *HN n) (m *NH q) ⟩
                m *NH q +H p *HN n
                    ≈⟨ *NH-HN m q ⟨ +H-cong ⟩ *HN-NH p n ⟩
                q *HN m +H n *NH p
                ∎ where open EqH

    *N-comm :
        (m n : Normal k) →
        ------------------
        m *N n ≈N n *N m

    *N-comm zero zero = zero
    *N-comm (poly p) (poly q) = poly (*H-comm p q)

```


```
mutual
    -- almost true, however p may be unsimplified on the right
    -- ·H-one : (p : HNF (suc k)) → 1R ·H p ≈H p

    ·N-one-var-zero : 1R ·N normalise-var {suc k} zero ≈N normalise-var zero
    ·N-one-var-zero =
        begin
            1R ·N normalise-var zero
                ≈⟨⟩
            1R ·N poly (∅ *x+ 1R ·x+ 0N)
                ≡⟨ cong poly (·H-nonzero-∅′ 1≉0 1≉0) ⟩
            poly (∅ *x+ (1R *R 1R) ·x+ (1R ·N 0N))
                ≈⟨ poly (∅ *x+ *R-identityˡ _ ·x+ c·0≈0N) ⟩
            poly (∅ *x+ 1R ·x+ 0N)
                ≈⟨⟩
            normalise-var zero
        ∎ where open EqN

    ·N-one-var : ∀ (x : Fin k) → 1R ·N normalise-var x ≈N normalise-var x
    ·N-one-var zero = ·N-one-var-zero
    ·N-one-var (suc x) = 
        begin
            1R ·N normalise-var (suc x)
                ≈⟨⟩
            1R ·N poly (∅ *x+ 0R ·x+ normalise-var x)
                ≡⟨ cong poly (·H-nonzero-zero-∅′ 1≉0) ⟩
            poly (∅ *x+ 0R ·x+ (1R ·N normalise-var x))
                ≈⟨ poly (∅ *x+ R-refl ·x+ ·N-one-var x) ⟩
            poly (∅ *x+ 0R ·x+ normalise-var x)
                ≈⟨⟩
            normalise-var (suc x)
        ∎ where open EqN

    ·N-one-con :
        ∀ c (p : Term′ k) →
        1R ·N normalise (c · p) ≈N normalise (c · p)
    ·N-one-con c p =
        begin
            1R ·N normalise (c · p)
                ≈⟨⟩
            1R ·N (c ·N normalise p)
                ≈⟨ *-·-distribN _ _ _ ⟨
            (1R *R c) ·N normalise p
                ≈⟨ ·N-cong (*R-identityˡ _) ≈N-refl ⟩
            c ·N normalise p
                ≈⟨⟩
            normalise (c · p)
        ∎ where open EqN
    
    ·N-one-add :
        ∀ (p q : Term′ k) →
        1R ·N normalise (p + q) ≈N normalise (p + q)
    ·N-one-add p q =
        begin
            1R ·N normalise (p + q)
                ≈⟨⟩
            1R ·N (normalise p +N normalise q)
                ≈⟨ {! ·-+-distribN _ _ _ !} ⟩
            (1R ·N normalise p) +N (1R ·N normalise q)
                ≈⟨ +N-cong (·N-one p) (·N-one q) ⟩
            normalise p +N normalise q
                ≈⟨⟩
            normalise (p + q)
        ∎ where open EqN

    ·N-one-mul :
        ∀ (p q : Term′ k) →
        1R ·N normalise (p * q) ≈N normalise (p * q)
    ·N-one-mul p q =
        begin
            1R ·N normalise (p * q)
                ≈⟨⟩
            1R ·N (normalise p *N normalise q)
                ≈⟨ ·-*-distribN _ _ _ ⟨
            (1R ·N normalise p) *N normalise q
                ≈⟨ *N-cong (·N-one p) ≈N-refl ⟩
            normalise p *N normalise q
                ≈⟨⟩
            normalise (p * q)
        ∎ where open EqN

    ·N-one : (p : Term′ k) → 1R ·N normalise p ≈N normalise p
    ·N-one {k} 0T = c·0≈0N
    ·N-one (var x) = ·N-one-var x
    ·N-one (c · p) = ·N-one-con c p
    ·N-one (p + q) = ·N-one-add p q
    ·N-one (p * q) = ·N-one-mul p q
```


