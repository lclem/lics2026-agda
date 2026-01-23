---
title: Decidability of equivalence of polynomial expressions
---

```
-- {-# OPTIONS --allow-unsolved-metas #-}

open import Preliminaries.Base
import Preliminaries.Algebra

module Preliminaries.DecidableEquivalence
    (R : CommutativeRing)
    (_R≟_ : let open Preliminaries.Algebra R in WeaklyDecidable _≈R_)
    where

import Preliminaries.Algebra
open Preliminaries.Algebra R
open import Preliminaries.PolyExpr R hiding (x)

private variable
    X Y Z : Set
    m n : ℕ

module AuxLem {n : ℕ} where
    open import Preliminaries.AuxiliaryLemmas (PECommRing {n}) public

open AuxLem
```

# Weak Decidability of equivalence of polynomial expressions

```
trivialAlgorithm : WeaklyDecidable (_≈_ {X})
trivialAlgorithm _ _ = nothing
```

```
mutual
    data HNF : ℕ → Set where
        ∅     : HNF (suc n)
        _*x+_ : HNF (suc n) → Normal n → HNF (suc n)

    data Normal : ℕ → Set where
        con  : A → Normal zero
        poly : HNF (suc n) → Normal (suc n)
```

Semantics of normal forms

```
lift : PE n → PE (suc n)
lift (con c) = con c
lift (var x) = var (suc x)
lift (p + q) = lift p + lift q
lift (p * q) = lift p * lift q

≈-lift : ∀ {p q : PE n} → p ≈ q → lift p ≈ lift q
≈-lift ≈-refl = ≈-refl
≈-lift (≈-sym p≈q) = ≈-sym (≈-lift p≈q)
≈-lift (≈-trans p≈q p≈q₁) = ≈-trans (≈-lift p≈q) (≈-lift p≈q₁)
≈-lift (≈-con c≈d) = ≈-con c≈d
≈-lift (+-cong p≈q p≈q₁) = +-cong (≈-lift p≈q) (≈-lift p≈q₁)
≈-lift (+-con c d) = +-con c d
≈-lift (+-zeroʳ p) = +-zeroʳ (lift p)
≈-lift (+-assoc p q r) = +-assoc (lift p) (lift q) (lift r)
≈-lift (+-comm p q) = +-comm (lift p) (lift q)
≈-lift (+-invʳ p) = +-invʳ (lift p)
≈-lift (*-cong p≈q p≈q₁) = *-cong (≈-lift p≈q) (≈-lift p≈q₁)
≈-lift (*-con c d) = *-con c d
≈-lift (*-oneʳ p) = *-oneʳ (lift p)
≈-lift (*-assoc p q r) = *-assoc (lift p) (lift q) (lift r)
≈-lift (*-comm p q) = *-comm (lift p) (lift q)
≈-lift (*-distrʳ p q r) = *-distrʳ (lift p) (lift q) (lift r)
```

Semantics

```
private x : PE (suc n)
x = var zero

mutual
    ⟦_⟧H : HNF (suc n) → PE (suc n)
    ⟦ ∅       ⟧H = 0P
    ⟦ p *x+ c ⟧H = ⟦ p ⟧H * x + lift (⟦ c ⟧N)

    ⟦_⟧N : Normal n → PE n
    ⟦ con c  ⟧N = con c
    ⟦ poly p ⟧N = ⟦ p ⟧H
```

Equality of normal forms

```
mutual
    data _≈H_ : HNF n → HNF n → Set where
        ∅     : _≈H_ {suc n} ∅ ∅
        _*x+_ : {p₁ p₂ : HNF (suc n)} {c₁ c₂ : Normal n} →
                p₁ ≈H p₂ → c₁ ≈N c₂ → (p₁ *x+ c₁) ≈H (p₂ *x+ c₂)

    data _≈N_ : Normal n → Normal n → Set where
        con  : ∀ {c₁ c₂} → c₁ ≈R c₂ → con c₁ ≈N con c₂
        poly : {p₁ p₂ : HNF (suc n)} → p₁ ≈H p₂ → poly p₁ ≈N poly p₂
```

```
mutual

  -- The semantics respect the equality relations

  ⟦_⟧H-cong :
    {p₁ p₂ : HNF (suc n)} →
    p₁ ≈H p₂ →
    -----------------------
    ⟦ p₁ ⟧H ≈ ⟦ p₂ ⟧H
  ⟦ ∅               ⟧H-cong = ≈-refl
  ⟦ p₁≈p₂ *x+ c₁≈c₂ ⟧H-cong =
        (⟦ p₁≈p₂ ⟧H-cong ⟨ *-cong ⟩ ≈-refl)
            ⟨ +-cong ⟩
        (≈-lift ⟦ c₁≈c₂ ⟧N-cong)

  ⟦_⟧N-cong :
    {p₁ p₂ : Normal n} →
    p₁ ≈N p₂ →
    --------------------
    ⟦ p₁ ⟧N ≈ ⟦ p₂ ⟧N
  ⟦ con c₁≈c₂  ⟧N-cong = ≈-con c₁≈c₂
  ⟦ poly p₁≈p₂ ⟧N-cong = ⟦ p₁≈p₂ ⟧H-cong
```

Equality of normal forms is weakly decidable.

```
mutual
    infix 4 _≟H_ _≟N_

    _≟H_ : WeaklyDecidable (_≈H_ {n = n})
    ∅           ≟H ∅           = just ∅
    ∅           ≟H (_ *x+ _)   = nothing
    (_ *x+ _)   ≟H ∅           = nothing
    (p₁ *x+ c₁) ≟H (p₂ *x+ c₂) with p₁ ≟H p₂ | c₁ ≟N c₂
    ... | just p₁≈p₂ | just c₁≈c₂ = just (p₁≈p₂ *x+ c₁≈c₂)
    ... | _          | nothing    = nothing
    ... | nothing    | _          = nothing

    _≟N_ : WeaklyDecidable (_≈N_ {n = n})
    con c₁ ≟N con c₂ with c₁ R≟ c₂
    ... | just c₁≈c₂ = just (con c₁≈c₂)
    ... | nothing    = nothing
    poly p₁ ≟N poly p₂ with p₁ ≟H p₂
    ... | just p₁≈p₂ = just (poly p₁≈p₂)
    ... | nothing    = nothing
```

Decide syntactic equality of polynomial expressions

```
infix 4 _≡P_
data _≡P_ {X} : PolyExpr X → PolyExpr X → Set where

    ≡P-refl : ∀ {p} → p ≡P p
    ≡P-sym : ∀ {p q} → p ≡P q → q ≡P p
    ≡P-trans : ∀ {p q r} → p ≡P q → q ≡P r → p ≡P r

    ≡P-con : ∀ {c d : A} → c ≈R d → con c ≡P con d
    ≡P-var : ∀ {x : X} → var x ≡P var x

    +-cong : ∀ {p₀ p₁ q₀ q₁} → p₀ ≡P p₁ → q₀ ≡P q₁ → p₀ + q₀ ≡P p₁ + q₁
    *-cong : ∀ {p₀ p₁ q₀ q₁} → p₀ ≡P p₁ → q₀ ≡P q₁ → p₀ * q₀ ≡P p₁ * q₁

module DecSynEq (X : Set) (_≡?_ : WeaklyDecidable (_≡_ {A = X})) where 

    infix 4 _≡P?_
    _≡P?_ : WeaklyDecidable (_≡P_ {X})
    con c₁ ≡P? con c₂ with c₁ R≟ c₂
    ... | just c₁≈c₂  = just (≡P-con c₁≈c₂)
    ... | nothing = nothing
    con _ ≡P? _ = nothing
    var x₁ ≡P? var x₂ with x₁ ≡? x₂
    ... | just refl = just ≡P-var
    ... | nothing = nothing
    var x₁ ≡P? _ = nothing
    (p₀ + p₁) ≡P? (q₀ + q₁) with p₀ ≡P? q₀ | p₁ ≡P? q₁
    ... | just p₀≈q₀ | just p₁≈q₁ = just (+-cong p₀≈q₀ p₁≈q₁)
    ... | _          | _    = nothing
    (p₀ + p₁) ≡P? _ = nothing
    (p₀ * p₁) ≡P? (q₀ * q₁) with p₀ ≡P? q₀ | p₁ ≡P? q₁
    ... | just p₀≈q₀ | just p₁≈q₁ = just (*-cong p₀≈q₀ p₁≈q₁)
    ... | _          | _    = nothing
    (p₀ * p₁) ≡P? _ = nothing

private module _ where

    _≡Fin?_ : ∀ {n} → WeaklyDecidable (_≡_ {A = Fin n})
    zero ≡Fin? zero = just refl
    suc x ≡Fin? suc y with x ≡Fin? y
    ... | just x≈y = just (cong suc x≈y)
    ... | nothing  = nothing
    _ ≡Fin? _ = nothing

    open DecSynEq (Fin 4) (_≡Fin?_)

    -- testeq1 : x₄ ≡P x₄
    -- testeq1 with x₄ ≡P? x₄ in eq
    -- ... | just proof = proof
    -- ... | nothing with .eq
    -- ... | ()

    -- testeq2 : x₄ + y₄ + 1P ≡P x₄ + y₄ + 1P
    -- testeq2 with x₄ + y₄ + 1P ≡P? x₄ + y₄ + 1P in eq
    -- ... | just proof = proof
    -- ... | nothing = ≡P-refl
    -- -- with eq
    -- -- ... | ()
```

```
0H : HNF (suc n)
0H = ∅

0N : Normal n
0N {zero}  = con 0R
0N {suc n} = poly 0H
```

```
mutual
    1H : HNF (suc n)
    1H {n} = ∅ *x+ 1N {n}

    1N : Normal n
    1N {zero}  = con 1R
    1N {suc n} = poly 1H
```

A simplifying variant of `_*x+_`.

```
_*x+HN_ : HNF (suc n) → Normal n → HNF (suc n)
(p *x+ c′) *x+HN c = (p *x+ c′) *x+ c
∅          *x+HN c with c ≟N 0N
... | just _  = 0H
... | nothing = 0H *x+ c
```

```
mutual

    -- Addition.

    _+H_ : HNF (suc n) → HNF (suc n) → HNF (suc n)
    ∅ +H p = p
    (p₁ *x+ c₁) +H ∅ = p₁ *x+ c₁
    (p₁ *x+ c₁) +H (p₂ *x+ c₂) = (p₁ +H p₂) *x+HN (c₁ +N c₂)

    _+N_ : Normal n → Normal n → Normal n
    con c₁  +N con c₂  = con (c₁ +R c₂)
    poly p₁ +N poly p₂ = poly (p₁ +H p₂)

    -- Multiplication.

    _*x+H_ : HNF (suc n) → HNF (suc n) → HNF (suc n)
    p₁         *x+H (p₂ *x+ c) = (p₁ +H p₂) *x+HN c
    ∅          *x+H ∅          = ∅
    (p₁ *x+ c) *x+H ∅          = (p₁ *x+ c) *x+ 0N

mutual

    _*NH_ : Normal n → HNF (suc n) → HNF (suc n)
    c *NH ∅          = 0H
    c *NH (p *x+ c′) with c ≟N 0N
    ... | just c≈0 = 0H
    ... | nothing  = (c *NH p) *x+ (c *N c′)

    _*HN_ : HNF (suc n) → Normal n → HNF (suc n)
    ∅          *HN c = 0H
    (p *x+ c′) *HN c with c ≟N 0N
    ... | just c≈0 = 0H
    ... | nothing  = (p *HN c) *x+ (c′ *N c)

    _*H_ : HNF (suc n) → HNF (suc n) → HNF (suc n)
    ∅           *H _           = 0H
    (_ *x+ _)   *H ∅           = 0H
    (p₁ *x+ c₁) *H (p₂ *x+ c₂) =
        ((p₁ *H p₂) *x+H ((p₁ *HN c₂) +H (c₁ *NH p₂))) *x+HN (c₁ *N c₂)

    _*N_ : Normal n → Normal n → Normal n
    con c₁  *N con c₂  = con (c₁ *R c₂)
    poly p₁ *N poly p₂ = poly (p₁ *H p₂)
```

Homomorphism lemmas

```
0N-homo : ∀ {n} → ⟦ 0N {n} ⟧N ≈ 0P
0N-homo {zero} = ≈-refl
0N-homo {suc _} = ≈-refl

open AlgebraicProperties

1N-homo : ∀ {n} → ⟦ 1N {n} ⟧N ≈ 1P
1N-homo {zero} = ≈-refl
1N-homo {suc n} = begin
    ⟦ 1N {suc n} ⟧N
        ≈⟨⟩
    0P * x + lift ⟦ 1N {n} ⟧N
        ≈⟨ +-cong (*-zeroˡ _) ≈-refl ⟩
    0P + lift ⟦ 1N {n} ⟧N
        ≈⟨ +-zeroˡ _ ⟩
    lift ⟦ 1N {n} ⟧N
        ≈⟨ ≈-lift (1N-homo {n}) ⟩
    lift 1P
        ≈⟨⟩
    1P ∎ where open EqP
```

```
⟦0⟧≈0 : {c : Normal n} → c ≈N 0N → ⟦ c ⟧N ≈ 0P
⟦0⟧≈0 {c = c} c≈0 = begin
  ⟦ c  ⟧N   ≈⟨ ⟦ c≈0 ⟧N-cong ⟩
  ⟦ 0N ⟧N   ≈⟨ 0N-homo ⟩
  0P        ∎ where open EqP

0≈⟦0⟧ : {c : Normal n} → c ≈N 0N → 0P ≈ ⟦ c ⟧N
0≈⟦0⟧ c≈0 = ≈-sym $ ⟦0⟧≈0 c≈0

-- _*x+HN_ is equal to _*x+_.

*x+HN≈*x+ :
    (p : HNF (suc n)) (c : Normal n) →
    ----------------------------------
    ⟦ p *x+HN c ⟧H ≈ ⟦ p *x+ c ⟧H

*x+HN≈*x+ (p *x+ c′) c = ≈-refl
*x+HN≈*x+ ∅          c with c ≟N 0N
... | just c≈0 = begin
  0P ≈⟨ ≈-lift (0≈⟦0⟧ c≈0) ⟩
  lift ⟦ c ⟧N ≈⟨ ≈-sym $ lemma₆ _ _ ⟩
  0P * x + lift ⟦ c ⟧N ∎ where open EqP
... | nothing = ≈-refl

∅*x+HN-homo :
    (c : Normal n) →
    ----------------------
    ⟦ ∅ *x+HN c ⟧H ≈ lift ⟦ c ⟧N

∅*x+HN-homo c with c ≟N 0N
... | just c≈0 = ≈-lift (0≈⟦0⟧ c≈0)
... | nothing = lemma₆ _ _

mutual

  +H-homo : (p₁ p₂ : HNF (suc n)) →
            -------------------------------
            ⟦ p₁ +H p₂ ⟧H ≈ ⟦ p₁ ⟧H + ⟦ p₂ ⟧H

  +H-homo ∅ _ = ≈-sym (+-zeroˡ _)
  +H-homo (p₁ *x+ c₁) ∅ = ≈-sym (+-zeroʳ _)
  +H-homo {n} (p₁ *x+ c₁) (p₂ *x+ c₂) =
    begin
        ⟦ (p₁ +H p₂) *x+HN (c₁ +N c₂) ⟧H
            ≈⟨ *x+HN≈*x+ (p₁ +H p₂) (c₁ +N c₂) ⟩
        ⟦ p₁ +H p₂ ⟧H * x + lift ⟦ c₁ +N c₂ ⟧N
            ≈⟨ (+H-homo p₁ p₂ ⟨ *-cong ⟩ ≈-refl) ⟨ +-cong ⟩ (≈-lift (+N-homo c₁ c₂)) ⟩
        (⟦ p₁ ⟧H + ⟦ p₂ ⟧H) * x + lift (⟦ c₁ ⟧N + ⟦ c₂ ⟧N)
            ≈⟨⟩
        (⟦ p₁ ⟧H + ⟦ p₂ ⟧H) * x + (lift ⟦ c₁ ⟧N + lift ⟦ c₂ ⟧N)
            ≈⟨ lemma₁ _ _ _ _ _ ⟩
        (⟦ p₁ ⟧H * x + lift ⟦ c₁ ⟧N) + (⟦ p₂ ⟧H * x + lift ⟦ c₂ ⟧N)
    ∎ where open EqP

  +N-homo : ∀ {n} (p₁ p₂ : Normal n) →
            -------------------------------
            ⟦ p₁ +N p₂ ⟧N ≈ ⟦ p₁ ⟧N + ⟦ p₂ ⟧N

  +N-homo (con c₁)  (con c₂)  = +-con _ _
  +N-homo (poly p₁) (poly p₂) = +H-homo p₁ p₂
```

```
*x+H-homo :
    (p₁ p₂ : HNF (suc n)) →
    -------------------------------------
    ⟦ p₁ *x+H p₂ ⟧H ≈ ⟦ p₁ ⟧H * x + ⟦ p₂ ⟧H

*x+H-homo ∅         ∅ = ≈-sym $ lemma₆ _ _
*x+H-homo (p *x+ c) ∅ = begin
    ⟦ p *x+ c ⟧H * x + lift ⟦ 0N ⟧N
        ≈⟨ ≈-refl ⟨ +-cong ⟩ ≈-lift 0N-homo ⟩
    ⟦ p *x+ c ⟧H * x + 0P
    ∎ where open EqP
*x+H-homo p₁         (p₂ *x+ c₂) = begin
    ⟦ (p₁ +H p₂) *x+HN c₂ ⟧H
        ≈⟨ *x+HN≈*x+ (p₁ +H p₂) c₂ ⟩
    ⟦ p₁ +H p₂ ⟧H * x + lift ⟦ c₂ ⟧N
        ≈⟨ (+H-homo p₁ p₂ ⟨ *-cong ⟩ ≈-refl) ⟨ +-cong ⟩ ≈-refl ⟩
    (⟦ p₁ ⟧H + ⟦ p₂ ⟧H) * x + lift ⟦ c₂ ⟧N
        ≈⟨ lemma₀ _ _ _ _ ⟩
    ⟦ p₁ ⟧H * x + (⟦ p₂ ⟧H * x + lift ⟦ c₂ ⟧N)
    ∎ where open EqP
```

```
mutual

    *NH-homo :
        (c : Normal n) (p : HNF (suc n)) →
        ----------------------------------
        ⟦ c *NH p ⟧H ≈ lift ⟦ c ⟧N * ⟦ p ⟧H

    *NH-homo c ∅          = ≈-sym (*-zeroʳ _)
    *NH-homo c (p *x+ c′) with c ≟N 0N
    ... | just c≈0 = begin
        0P
            ≈⟨ ≈-sym (*-zeroˡ _) ⟩
        0P * (⟦ p ⟧H * x + lift ⟦ c′ ⟧N)
            ≈⟨ ≈-lift (0≈⟦0⟧ c≈0) ⟨ *-cong ⟩ ≈-refl ⟩
        lift ⟦ c ⟧N * (⟦ p ⟧H * x + lift ⟦ c′ ⟧N)
        ∎ where open EqP
    ... | nothing = begin
        ⟦ c *NH p ⟧H * x + lift ⟦ c *N c′ ⟧N
            ≈⟨ (*NH-homo c p ⟨ *-cong ⟩ ≈-refl) ⟨ +-cong ⟩ (≈-lift (*N-homo c c′)) ⟩
        (lift ⟦ c ⟧N * ⟦ p ⟧H) * x + lift (⟦ c ⟧N * ⟦ c′ ⟧N)
            ≈⟨ lemma₃ _ _ _ _ ⟩
        lift ⟦ c ⟧N * (⟦ p ⟧H * x + lift ⟦ c′ ⟧N)
        ∎ where open EqP

    *HN-homo :
        (p : HNF (suc n)) (c : Normal n) →
        ----------------------------------
        ⟦ p *HN c ⟧H ≈ ⟦ p ⟧H * lift ⟦ c ⟧N
        
    *HN-homo ∅          c = ≈-sym $ *-zeroˡ _
    *HN-homo (p *x+ c′) c with c ≟N 0N
    ... | just c≈0 = begin
        0P
            ≈⟨ ≈-sym (*-zeroʳ _) ⟩
        (⟦ p ⟧H * x + lift ⟦ c′ ⟧N) * 0P
            ≈⟨ ≈-refl ⟨ *-cong ⟩ ≈-lift (0≈⟦0⟧ c≈0) ⟩
        (⟦ p ⟧H * x + lift ⟦ c′ ⟧N) * lift ⟦ c ⟧N
        ∎  where open EqP
    ... | nothing = begin
        ⟦ p *HN c ⟧H * x + lift ⟦ c′ *N c ⟧N
            ≈⟨ (*HN-homo p c ⟨ *-cong ⟩ ≈-refl) ⟨ +-cong ⟩ ≈-lift (*N-homo c′ c) ⟩
        (⟦ p ⟧H * lift ⟦ c ⟧N) * x + lift (⟦ c′ ⟧N * ⟦ c ⟧N)
            ≈⟨ lemma₂ _ _ _ _ ⟩
        (⟦ p ⟧H * x + lift ⟦ c′ ⟧N) * lift ⟦ c ⟧N
        ∎ where open EqP

    *H-homo :
        ∀ {n} (p₁ p₂ : HNF (suc n)) →
        -------------------------------
        ⟦ p₁ *H p₂ ⟧H ≈ ⟦ p₁ ⟧H * ⟦ p₂ ⟧H

    *H-homo ∅           p₂          = ≈-sym $ *-zeroˡ _
    *H-homo (p₁ *x+ c₁) ∅           = ≈-sym $ *-zeroʳ _
    *H-homo (p₁ *x+ c₁) (p₂ *x+ c₂) =
        begin
        ⟦ ((p₁ *H p₂) *x+H ((p₁ *HN c₂) +H (c₁ *NH p₂))) *x+HN (c₁ *N c₂) ⟧H
            ≈⟨ *x+HN≈*x+ ((p₁ *H p₂) *x+H ((p₁ *HN c₂) +H (c₁ *NH p₂))) (c₁ *N c₂) ⟩
        ⟦ (p₁ *H p₂) *x+H ((p₁ *HN c₂) +H (c₁ *NH p₂)) ⟧H * x + lift ⟦ c₁ *N c₂ ⟧N
            ≈⟨ (*x+H-homo (p₁ *H p₂) ((p₁ *HN c₂) +H (c₁ *NH p₂)) ⟨ *-cong ⟩ ≈-refl) ⟨ +-cong ⟩ ≈-lift (*N-homo c₁ c₂)⟩
        (⟦ p₁ *H p₂ ⟧H * x + ⟦ (p₁ *HN c₂) +H (c₁ *NH p₂) ⟧H) * x + lift ⟦ c₁ ⟧N * lift ⟦ c₂ ⟧N
            ≈⟨ (((*H-homo p₁ p₂ ⟨ *-cong ⟩ ≈-refl) ⟨ +-cong ⟩ (+H-homo (p₁ *HN c₂) (c₁ *NH p₂) )) ⟨ *-cong ⟩ ≈-refl) ⟨ +-cong ⟩ ≈-refl ⟩
        ((⟦ p₁ ⟧H * ⟦ p₂ ⟧H) * x + (⟦ p₁ *HN c₂ ⟧H + ⟦ c₁ *NH p₂ ⟧H )) * x + lift ⟦ c₁ ⟧N * lift ⟦ c₂ ⟧N
            ≈⟨ ((≈-refl ⟨ +-cong ⟩ (*HN-homo p₁ c₂ ⟨ +-cong ⟩ *NH-homo c₁ p₂ )) ⟨ *-cong ⟩ ≈-refl) ⟨ +-cong ⟩ ≈-refl ⟩
        ((⟦ p₁ ⟧H * ⟦ p₂ ⟧H) * x + (⟦ p₁ ⟧H * lift ⟦ c₂ ⟧N + lift ⟦ c₁ ⟧N * ⟦ p₂ ⟧H)) * x + (lift ⟦ c₁ ⟧N * lift ⟦ c₂ ⟧N)
            ≈⟨ lemma₄ _ _ _ _ _ ⟩
        (⟦ p₁ ⟧H * x + lift ⟦ c₁ ⟧N) * (⟦ p₂ ⟧H * x + lift ⟦ c₂ ⟧N)
        ∎ where open EqP

    *N-homo :
        ∀ {n} (p₁ p₂ : Normal n) →
        -------------------------------
        ⟦ p₁ *N p₂ ⟧N ≈ ⟦ p₁ ⟧N * ⟦ p₂ ⟧N
    *N-homo (con c₁)  (con c₂)  = *-con _ _
    *N-homo (poly p₁) (poly p₂) = *H-homo p₁ p₂
```

Conversion to normal forms

```
normalise-con : A → Normal n
normalise-con {zero}  c = con c
normalise-con {suc n} c = poly (∅ *x+HN normalise-con {n} c)

normalise-var : Fin n → Normal n
normalise-var zero    = poly ((∅ *x+ 1N) *x+ 0N)
normalise-var (suc x) = poly (∅ *x+HN normalise-var x)

normalise : PE n → Normal n
normalise (con c) = normalise-con c
normalise (var x) = normalise-var x
normalise (t₁ + t₂) = normalise t₁ +N normalise t₂
normalise (t₁ * t₂) = normalise t₁ *N normalise t₂

⟦_⟧↓ : PE n → PE n
⟦ p ⟧↓ = ⟦ normalise p ⟧N
```

```
normalise-con-zero : ∀ {c} → normalise-con {n} c ≈N 0N → c ≈R 0R
normalise-con-zero {zero} (con eq) = eq
normalise-con-zero {suc n} {c} (poly .{n} eq)
    with normalise-con {n} c ≟N 0N in eq'
... | just c≈0 = normalise-con-zero c≈0
normalise-con-zero {suc n} {c} (poly .{n} ()) | nothing

normalise-var-zero : ∀ (x : Fin n) → normalise-var x ≈N 0N → ⊥
normalise-var-zero zero (poly ())
normalise-var-zero (suc x) (poly eq) with normalise-var x ≟N 0N
... | just x≈0 = normalise-var-zero x x≈0
normalise-var-zero (suc x) (poly ()) | nothing

-- normalise-zero : ∀ p → normalise {n} p ≈N 0N → p ≈ 0P
-- normalise-zero p eq = {!   !}
```

```
sound-con : ∀ c → ⟦ normalise-con {n} c ⟧N ≈ con c
sound-con {zero} c = ≈-refl
sound-con {suc n} c with normalise-con {n} c ≟N 0N in eq
... | nothing  =
    begin
        0P * x + lift ⟦ normalise-con c ⟧N
            ≈⟨ +-cong (*-zeroˡ _) (≈-lift (sound-con c)) ⟩
        0P + lift (con c)
            ≈⟨ +-zeroˡ _ ⟩
        con c
    ∎ where open EqP
... | just c≈0 = ≈-sym (≈-con (normalise-con-zero c≈0))

sound-var : ∀ x → ⟦ normalise-var {n} x ⟧N ≈ var x
sound-var zero =
    begin
        (0P * x + lift ⟦ 1N ⟧N) * x + lift ⟦ 0N ⟧N
            ≈⟨ +-cong ≈-refl (≈-lift 0N-homo) ⟩
        (0P * x + lift ⟦ 1N ⟧N) * x + 0P
            ≈⟨ +-zeroʳ _ ⟩
        (0P * x + lift ⟦ 1N ⟧N) * x
            ≈⟨ *-cong (+-cong (*-zeroˡ _) (≈-lift 1N-homo)) ≈-refl ⟩
        (0P + 1P) * x
            ≈⟨ *-cong (+-zeroˡ _)  ≈-refl ⟩
        1P * x
            ≈⟨ *-oneˡ _ ⟩
        var zero
    ∎ where open EqP
sound-var (suc y) with normalise-var y ≟N 0N in eq
... | nothing =
    begin
        0P * x + lift ⟦ normalise-var y ⟧N
            ≈⟨ +-cong (*-zeroˡ _) (≈-lift (sound-var y)) ⟩
        0P + lift (var y)
            ≈⟨ +-zeroˡ _ ⟩
        var (suc y)
    ∎ where open EqP
sound-var (suc x) | just x≈0 = ⊥-elim (normalise-var-zero _ x≈0)

soundN : (p : PE n) → ⟦ normalise p ⟧N ≈ p
soundN (con c) = sound-con c
soundN (var x) = sound-var x
soundN (p + q) = 
    begin
    ⟦ normalise p +N normalise q ⟧N ≈⟨ +N-homo (normalise p) (normalise q) ⟩
    ⟦ normalise p ⟧N + ⟦ normalise q ⟧N ≈⟨ +-cong (soundN p) (soundN q) ⟩
    p + q
    ∎ where open EqP
soundN (p * q) =
    begin
    ⟦ normalise p *N normalise q ⟧N ≈⟨ *N-homo (normalise p) (normalise q) ⟩
    ⟦ normalise p ⟧N * ⟦ normalise q ⟧N ≈⟨ *-cong (soundN p) (soundN q) ⟩
    p * q
    ∎ where open EqP

mutual
    reflectH : {p q : HNF (suc n)} → p ≈H q → ⟦ p ⟧H ≈ ⟦ q ⟧H
    reflectH {n} {p} {q} ∅ = ≈-refl
    reflectH {n} {p *x+ c} {q *x+ d} (p≈Hq *x+ c≈Nd) =
        begin
        ⟦ p ⟧H * x + lift ⟦ c ⟧N
            ≈⟨ +-cong (*-cong (reflectH p≈Hq) ≈-refl) (≈-lift (reflectN c≈Nd)) ⟩
        ⟦ q ⟧H * x + lift ⟦ d ⟧N
        ∎ where open EqP

    reflectN : {p q : Normal n} → p ≈N q → ⟦ p ⟧N ≈ ⟦ q ⟧N
    reflectN (con x) = ≈-con x
    reflectN (poly x) = reflectH x

sound : {p q : PE n} → normalise p ≈N normalise q → p ≈ q
sound {n} {p} {q} eq =
    begin
        p ≈⟨ ≈-sym (soundN p) ⟩
        ⟦ normalise p ⟧N ≈⟨ reflectN eq ⟩
        ⟦ normalise q ⟧N ≈⟨ soundN q ⟩
        q
    ∎ where open EqP

infix 4 _≟_
_≟_ : ∀ {n} → WeaklyDecidable (_≈_ {Fin n})
p ≟ q with normalise p ≟N normalise q
... | just eq = just (sound eq)
... | nothing = nothing
```