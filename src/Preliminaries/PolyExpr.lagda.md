---
title: Polynomial expressions
---

In this section we define polynomial expressions over a commutative ring `R`,
and discuss some of their properties.

```
{-# OPTIONS --backtracking-instance-search --instance-search-depth 4 #-}
-- {-# OPTIONS --allow-unsolved-metas #-}

open import Preliminaries.Base
module Preliminaries.PolyExpr (R : CommutativeRing) where

open import Preliminaries.Algebra R

private variable
    X Y Z : Set
    m n : ℕ
```

# Syntax

Let `X` by a type for variables.
A polynomial expression over `X` is built from constants from `A`, variables from `X`,
and the binary operations of addition `_+_` and multiplication `_*_`.

In Agda, this is expressed by the inductive data type `PolyExpr X`,
defined as follows:

```
infixr 9 _+_
infixr 10 _*_
data PolyExpr (X : Set) : Set where
    con : A → PolyExpr X
    var : (x : X) → PolyExpr X
    _+_ _*_ : (p q : PolyExpr X) → PolyExpr X

0P 1P : PolyExpr X
0P = con 0R
1P = con 1R
```

We can define a scalar multiplication.

```
infixr 10 _·_
_·_ : (c : A) (p : PolyExpr X) → PolyExpr X
c · p = con c * p
```

We can define additive inverses.

```
-1R = -R 1R

infix 3 -_
-_ : PolyExpr X → PolyExpr X
- p = con -1R * p

infixl 9 _-_
_-_ : PolyExpr X → PolyExpr X → PolyExpr X
p - q = p + (- q)
```

# Equivalence of polynomial expressions

We introduce a natural equivalence relation on polynomial expressions
capturing commutativity, associativity, and distributivity of addition and multiplication.
This equivalence turns the set of polynomial expressions into a commutative algebra over `R`.

```
infix 4 _≈_
private variable p q r p₀ p₁ q₀ q₁ r₀ r₁ : PolyExpr X

data _≈_ {X} : PolyExpr X → PolyExpr X → Set where

    ≈-refl : p ≈ p
    ≈-sym : p ≈ q → q ≈ p
    ≈-trans : p ≈ q → q ≈ r → p ≈ r

    -- lift equivalence from the base ring to polynomials
    ≈-con : ∀ {c d : A} → c ≈R d → con c ≈ con d

    +-cong : p₀ ≈ p₁ → q₀ ≈ q₁ → p₀ + q₀ ≈ p₁ + q₁
    +-con : ∀ (c d : A) → con (c +R d) ≈ con c + con d
    +-zeroʳ : ∀ p → p + 0P ≈ p
    +-assoc : ∀ p q r → (p + q) + r ≈ p + (q + r)
    +-comm : ∀ p q → p + q ≈ q + p
    +-invʳ : ∀ p → p - p ≈ 0P

    *-cong : p₀ ≈ p₁ → q₀ ≈ q₁ → p₀ * q₀ ≈ p₁ * q₁
    *-con : ∀ (c d : A) → con (c *R d) ≈ con c * con d
    *-oneʳ : ∀ p → p * 1P ≈ p
    *-assoc : ∀ p q r → (p * q) * r ≈ p * (q * r)
    *-comm : ∀ p q → p * q ≈ q * p
    *-distrʳ : ∀ p q r → (q + r) * p ≈ (q * p) + (r * p)

≈-isEquivalence : IsEquivalence (_≈_ {X})
≈-isEquivalence = record { refl = ≈-refl ; sym = ≈-sym ; trans = ≈-trans }
```

```
·-*-compatibility : ∀ (c : A) (p q : PolyExpr X) → (c · p) * q ≈ c · (p * q)
·-*-compatibility c p q = *-assoc (con c) p q
```

A polynomial over a commutative ring is precisely an equivalence class of modulo `_≈_`.

```
module EqP {X : Set} where
    open import Preliminaries.Equivalence (≈-isEquivalence {X})
    open Eq public
```

```
con-*-distrʳ : ∀ (p : PolyExpr X) c d → (c +R d) · p ≈ (c · p) + (d · p)
con-*-distrʳ p c d =
    begin
        con (c +R d) * p
            ≈⟨ +-con _ _ ⟨ *-cong ⟩ ≈-refl ⟩
        (con c + con d) * p
            ≈⟨ *-distrʳ _ _ _ ⟩
        (con c * p) + (con d * p)
            ≈⟨⟩
        (c · p) + (d · p)
    ∎ where open EqP

con-*-assoc : ∀ (p : PolyExpr X) c d → (c *R d) · p ≈ c · (d · p)
con-*-assoc p c d =
    begin
        (c *R d) · p
            ≈⟨ *-con _ _ ⟨ *-cong ⟩ ≈-refl ⟩
        (con c * con d) * p
            ≈⟨ *-assoc _ _ _ ⟩
        con c * (con d * p)
            ≈⟨⟩
        c · (d · p)
    ∎ where open EqP
```

## Algebraic properties

```
module AlgebraicProperties where
    +-zeroˡ : ∀ (p : PolyExpr X) → 0P + p ≈ p
    +-zeroˡ p =
        begin
            0P + p
                ≈⟨ +-comm _ _ ⟩
            p + 0P
                ≈⟨ +-zeroʳ p ⟩
            p
        ∎ where open EqP

    +-identityˡ = +-zeroˡ

    +-identityʳ : ∀ (p : PolyExpr X) → p + 0P ≈ p
    +-identityʳ = +-zeroʳ

    +-invˡ : ∀ (p : PolyExpr X) → (- p) + p ≈ 0P
    +-invˡ p =
        begin
            (- p) + p
                ≈⟨ +-comm _ _ ⟩
            p + (- p)
                ≈⟨ +-invʳ p ⟩
            0P
        ∎ where open EqP
```

```
    -‿cong : ∀ {X} {p q : PolyExpr X} → p ≈ q → (- p) ≈ (- q)
    -‿cong = *-cong ≈-refl
```

### Additive structure

```
    +-isMonoid : ∀ {X} → IsMonoid (_≈_ {X}) _+_ (0P)
    +-isMonoid = record {
        isSemigroup = record {
        isMagma = record {
            isEquivalence = ≈-isEquivalence;
            ∙-cong = +-cong
        };
        assoc = +-assoc
        };
        identity = record { fst = +-zeroˡ; snd = +-zeroʳ }
        }

    +-isGroup : IsGroup (_≈_ {X}) _+_ (0P) (-_)
    +-isGroup = record {
        isMonoid = +-isMonoid;
        inverse = record {fst = +-invˡ; snd = +-invʳ};
        ⁻¹-cong = -‿cong
        }

    +-isAbelianGroup : IsAbelianGroup (_≈_ {X}) _+_ (0P) (-_)
    +-isAbelianGroup = record {
        isGroup = +-isGroup;
        comm = +-comm
        }
```

### Multiplicative structure

```
    *-oneˡ : ∀ (p : PolyExpr X) → 1P * p ≈ p
    *-oneˡ p = 
        begin
            1P * p
                ≈⟨ *-comm _ _ ⟩
            p * 1P
                ≈⟨ *-oneʳ p ⟩
            p
        ∎ where open EqP

    *-distrˡ : (p q r : PolyExpr X) →
        p * (q + r) ≈ (p * q) + (p * r)
    *-distrˡ p q r = 
        begin
            p * (q + r) ≈⟨ *-comm p (q + r) ⟩
            (q + r) * p ≈⟨ *-distrʳ p q r ⟩
            q * p + r * p ≈⟨ +-cong (*-comm q p) (*-comm r p) ⟩
            p * q + p * r
        ∎ where open EqP
```

```
    *-identity : Identity (_≈_ {X}) (1P) _*_
    *-identity = record { fst = *-oneˡ; snd = *-oneʳ }

    *-isMonoid : ∀ {X} → IsMonoid (_≈_ {X}) _*_ (1P)
    *-isMonoid = record {
        isSemigroup = record {
        isMagma = record {
            isEquivalence = ≈-isEquivalence;
            ∙-cong = *-cong
        };
        assoc = *-assoc
        };
        identity = *-identity
        }

    *-isCommutativeMonoid : ∀ {X} → IsCommutativeMonoid (_≈_ {X}) _*_ (1P)
    *-isCommutativeMonoid = record { isMonoid = *-isMonoid; comm = *-comm }
```

### Ring structure

```
    isRing : ∀ {X} → IsRing (_≈_ {X}) _+_ _*_ -_ (0P) (1P)
    isRing = record
        { +-isAbelianGroup = +-isAbelianGroup
        ; *-cong = *-cong
        ; *-assoc = *-assoc
        ; *-identity = *-identity
        ; distrib = record {fst = *-distrˡ; snd = *-distrʳ}
        }

    isCommutativeRing : ∀ {X} → IsCommutativeRing (_≈_ {X}) _+_ _*_ -_ (0P) (1P)
    isCommutativeRing = record { isRing = isRing; *-comm = *-comm }

    -- isRing.zeroˡ
    PolyExprCommRing : Set → CommutativeRing
    PolyExprCommRing X = record
        { Carrier = PolyExpr X
        ; _≈_ = (_≈_ {X})
        ; _+_ = _+_
        ; _*_ = _*_
        ; -_ = -_
        ; 0# = (0P)
        ; 1# = (1P)
        ; isCommutativeRing = isCommutativeRing
        }
```

These two properties follow from the ring structure.

```
    *-zeroˡ : ∀ (p : PolyExpr X) → 0P * p ≈ 0P
    *-zeroˡ {X} = CR.zeroˡ (PolyExprCommRing X)

    *-zeroʳ : ∀ (p : PolyExpr X) → p * 0P ≈ 0P
    *-zeroʳ {X} = CR.zeroʳ (PolyExprCommRing X)
```

```
open AlgebraicProperties
```



```
-- module Semantics where

Env : Set → Set
Env X = X → A

infix 200 ⟦_⟧_
⟦_⟧_ : PolyExpr X → Env X → A
⟦ con c ⟧ ϱ = c
⟦ var x ⟧ ϱ = ϱ x
⟦ p + q ⟧ ϱ = ⟦ p ⟧ ϱ +R ⟦ q ⟧ ϱ
⟦ p * q ⟧ ϱ = ⟦ p ⟧ ϱ *R ⟦ q ⟧ ϱ

≈-eval₀ :
    ∀ {p q : PolyExpr X} {ϱ} →
    p ≈ q →
    ---------------------------
    ⟦ p ⟧ ϱ ≈R ⟦ q ⟧ ϱ

≈-eval₀ ≈-refl = R-refl
≈-eval₀ (≈-sym p≈q) = R-sym (≈-eval₀ p≈q)
≈-eval₀ (≈-trans p≈q q≈r) = R-trans (≈-eval₀ p≈q) (≈-eval₀ q≈r)
≈-eval₀ (≈-con c≈d) = c≈d
≈-eval₀ (+-cong p≈p′ q≈q′) = +R-cong (≈-eval₀ p≈p′) (≈-eval₀ q≈q′)
≈-eval₀ (+-con c d) = R-refl
≈-eval₀ (+-zeroʳ p) = +R-identityʳ _
≈-eval₀ (+-assoc p q r) = +R-assoc _ _ _
≈-eval₀ (+-comm p q) = +R-comm _ _
≈-eval₀ (+-invʳ p) = add-inv _
≈-eval₀ (*-cong p≈p′ q≈q′) = *R-cong (≈-eval₀ p≈p′) (≈-eval₀ q≈q′)
≈-eval₀ (*-con c d) = R-refl
≈-eval₀ (*-oneʳ p) = *R-identityʳ _
≈-eval₀ (*-assoc p q r) = *R-assoc _ _ _
≈-eval₀ (*-comm p q) = *R-comm _ _
≈-eval₀ (*-distrʳ p q r) = R-distribʳ _ _ _

≈-eval :
    ∀ (p : PolyExpr X) {ϱ₀ ϱ₁} →
    (∀ x → ϱ₀ x ≈R ϱ₁ x) →
    -----------------------------
    ⟦ p ⟧ ϱ₀ ≈R ⟦ p ⟧ ϱ₁

≈-eval (con c) _ = R-refl
≈-eval (var x) ϱ₀≈ϱ₁ = ϱ₀≈ϱ₁ x
≈-eval (p + q) ϱ₀≈ϱ₁ = ≈-eval p ϱ₀≈ϱ₁ ⟨ +R-cong ⟩ ≈-eval q ϱ₀≈ϱ₁
≈-eval (p * q) ϱ₀≈ϱ₁ = ≈-eval p ϱ₀≈ϱ₁ ⟨ *R-cong ⟩ ≈-eval q ϱ₀≈ϱ₁
```

```
Subst : Set → Set → Set
Subst X Y = X → PolyExpr Y

subst : Subst X Y → PolyExpr X → PolyExpr Y
subst ϱ (con c) = con c
subst ϱ (var x) = ϱ x
subst ϱ (p + q) = subst ϱ p + subst ϱ q
subst ϱ (p * q) = subst ϱ p * subst ϱ q

subst-≡ : ∀ p (ϱ₀ : Subst X Y) (ϱ₁ : Subst X Y) →
  (∀ x → ϱ₀ x ≡ ϱ₁ x) →
  -----------------------------------------------
  subst ϱ₀ p ≡ subst ϱ₁ p

subst-≡ (con x) ϱ₀ ϱ₁ ϱ≡ϱ′ = refl
subst-≡ (var x) ϱ₀ ϱ₁ ϱ≡ϱ′ = ϱ≡ϱ′ x
subst-≡ (p + q) ϱ₀ ϱ₁ ϱ≡ϱ′
    rewrite subst-≡ p ϱ₀ ϱ₁ ϱ≡ϱ′ | subst-≡ q ϱ₀ ϱ₁ ϱ≡ϱ′ = refl
subst-≡ (p * q) ϱ₀ ϱ₁ ϱ≡ϱ′
    rewrite subst-≡ p ϱ₀ ϱ₁ ϱ≡ϱ′ | subst-≡ q ϱ₀ ϱ₁ ϱ≡ϱ′ = refl


subst-subst :
  ∀ p (ϱ₀ : Subst X Y) (ϱ₁ : Subst Y Z) →
  -----------------------------------------------
  subst ϱ₁ (subst ϱ₀ p) ≡ subst (subst ϱ₁ ∘ ϱ₀) p

subst-subst (con c) ϱ₀ ϱ₁ = refl
subst-subst (var x) _ _ = refl
subst-subst (p + q) ϱ₀ ϱ₁ = cong₂ _+_ (subst-subst p ϱ₀ ϱ₁) (subst-subst q ϱ₀ ϱ₁)
subst-subst (p * q) ϱ₀ ϱ₁ = cong₂ _*_ (subst-subst p ϱ₀ ϱ₁) (subst-subst q ϱ₀ ϱ₁)

subst-inv :
    ∀ {p q : PolyExpr X} (ϱ : Subst X Y) →
    p ≈ q →
    ----------------------------------
    subst ϱ p ≈ subst ϱ q

subst-inv _ ≈-refl = ≈-refl
subst-inv _ (≈-sym p≈q) = ≈-sym (subst-inv _ p≈q)
subst-inv _ (≈-trans p≈r r≈q) = ≈-trans (subst-inv _ p≈r) (subst-inv _ r≈q)

subst-inv ϱ (≈-con x) = ≈-con x
subst-inv ϱ (+-con c d) = +-con c d
subst-inv ϱ (*-con c d) = *-con c d

subst-inv _ (+-cong p₀≈p₁ q₀≈q₁) = +-cong (subst-inv _ p₀≈p₁) (subst-inv _ q₀≈q₁)
subst-inv _ (+-zeroʳ p) = +-zeroʳ (subst _ p)
subst-inv _ (+-assoc p q r) = +-assoc (subst _ p) (subst _ q) (subst _ r)
subst-inv _ (+-comm p q) = +-comm (subst _ p) (subst _ q)
subst-inv _ (+-invʳ p) = +-invʳ (subst _ p)

subst-inv _ (*-cong p≈q p≈q₁) = *-cong (subst-inv _ p≈q) (subst-inv _ p≈q₁)
subst-inv _ (*-oneʳ p) = *-oneʳ (subst _ p)
subst-inv _ (*-assoc p q r) = *-assoc (subst _ p) (subst _ q) (subst _ r)
subst-inv _ (*-comm p q) = *-comm (subst _ p) (subst _ q)
subst-inv ϱ (*-distrʳ p q r) = *-distrʳ (subst ϱ p) (subst ϱ q) (subst ϱ r)

subst-inv′ :
    ∀ p {ϱ₀ ϱ₁ : Subst X Y} →
    (∀ (x : X) → ϱ₀ x ≈ ϱ₁ x) →
    -----------------------
    subst ϱ₀ p ≈ subst ϱ₁ p

subst-inv′ (con c) _ = ≈-refl
subst-inv′ (var x) ϱ₀≈ϱ₁ = ϱ₀≈ϱ₁ x
subst-inv′ (p + q) ϱ₀≈ϱ₁ = subst-inv′ p ϱ₀≈ϱ₁ ⟨ +-cong ⟩ subst-inv′ q ϱ₀≈ϱ₁
subst-inv′ (p * q) ϱ₀≈ϱ₁ = subst-inv′ p ϱ₀≈ϱ₁ ⟨ *-cong ⟩ subst-inv′ q ϱ₀≈ϱ₁
```

# Expressions over finitely many variables

We introduce a special trearment for polynomial expressions over finitely many variables.
Variables are represented by elements from a finite set.

```
Var = Fin
```

A polynomial expression over `n` variables, written `PE n`,
is a polynomial expression where the variables are drawn from `Var n`,
the type of a set with `n` elements.

```
PE : (n : ℕ) → Set
PE n = PolyExpr (Var n)

open import Data.Nat.Properties

<-forward : m < n → m < suc n
<-forward m<n = m<n⇒m<1+n m<n

instance
  _ : 0 < suc n
  _ = s≤s z≤n

  <-ste : ⦃ m < n ⦄ → suc m < suc n
  <-ste {{m<n}} = s<s m<n

  <-back : ⦃ suc m < n ⦄ → m < n
  <-back ⦃ s≤s sm≤n ⦄ = <-forward sm≤n

mkVar : ∀ (m : ℕ) → ⦃ m < n ⦄ → PE n
mkVar _ ⦃ m<n ⦄ = var (fromℕ< m<n)

x : PE (1 +ℕ n)
x  = mkVar 0

y : PE (2 +ℕ n)
y  = mkVar 1
```

```
PECommRing : {n : ℕ} → CommutativeRing
PECommRing {n} = PolyExprCommRing (Var n)
```

# Integral polynomial expressions

Integral polynomial expressions are those which do not use any constants from `R`.

```
data IntegralPolyExpr {X : Set} : PolyExpr X → Set where

    con0 : IntegralPolyExpr 0P
    con1 : IntegralPolyExpr 1P
    var : ∀ x → IntegralPolyExpr (var x)
    -- neg : ∀ {p} → IntegralPolyExpr p → IntegralPolyExpr (- p)
    _+_ : ∀ {p q} → IntegralPolyExpr p → IntegralPolyExpr q → IntegralPolyExpr (p + q)
    _*_ : ∀ {p q} → IntegralPolyExpr p → IntegralPolyExpr q → IntegralPolyExpr (p * q)

isIntegralPolyExpr? : WeaklyDecidable₁ (IntegralPolyExpr {Fin n})
isIntegralPolyExpr? (con _) = nothing -- can't really check whether 0R or 1R without a decidable equality on R
isIntegralPolyExpr? (var x) = just $ var x
isIntegralPolyExpr? (p + q)
    with isIntegralPolyExpr? p | isIntegralPolyExpr? q
... | just p' | just q' = just $ p' + q'
... | _ | _ = nothing
isIntegralPolyExpr? (p * q)
    with isIntegralPolyExpr? p | isIntegralPolyExpr? q
... | just p' | just q' = just $ p' * q'
... | _ | _ = nothing
```