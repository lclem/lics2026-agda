---
title: "Polynomials"
---

In this section we introduce an natural equivalence on terms turning them into polynomial expressions (without constant term)
and we study their properties.

```
{-# OPTIONS --guardedness --sized-types #-}

open import Preliminaries.Base
module Special.Polynomials (R : CommutativeRing) where

open import Preliminaries.Algebra R
open import General.Terms R
```

# Equivalence of terms

We introduce a natural equivalence relation on terms
capturing commutativity, associativity, and distributivity of addition and multiplication.
This equivalence turns the set of terms into a commutative algebra over `R`.

```
infix 4 _≈_ _≈₄_ _≈₅_ _≈₆_ _≈₇_ _≈₉_
private variable
    X Y : Set
    c d : A
    p q r p₀ p₁ q₀ q₁ r₀ r₁ : Term X
    n : ℕ
```

Formally, two terms `p` and `q` are equivalent, written `p ≈ q`,
if they satisfy any of the following rules.

```
data _≈_ {X} : Term X → Term X → Set where

    ≈-refl : p ≈ p
    ≈-sym : p ≈ q → q ≈ p
    ≈-trans : p ≈ q → q ≈ r → p ≈ r

    ·-cong : c ≈R d → p ≈ q → c · p ≈ d · q
    ·-one : ∀ p → 1R · p ≈ p
    ·-+-distrib : ∀ c p q → c · (p + q) ≈ c · p + c · q
    +-·-distrib : ∀ p c d → (c +R d) · p ≈ c · p + d · p
    ·-*-distrib : ∀ c p q → (c · p) * q ≈ c · (p * q)
    *-·-distrib : ∀ c d p → (c *R d) · p ≈ c · (d · p)

    +-cong : p₀ ≈ p₁ → q₀ ≈ q₁ → p₀ + q₀ ≈ p₁ + q₁
    +-zeroʳ : ∀ p → p + 0T ≈ p
    +-assoc : ∀ p q r → (p + q) + r ≈ p + (q + r)
    +-comm : ∀ p q → p + q ≈ q + p
    +-invʳ : ∀ p → p - p ≈ 0T

    *-cong : p₀ ≈ p₁ → q₀ ≈ q₁ → p₀ * q₀ ≈ p₁ * q₁
    *-assoc : ∀ p q r → (p * q) * r ≈ p * (q * r)
    *-comm : ∀ p q → p * q ≈ q * p
    *-distribʳ : ∀ p q r → (q + r) * p ≈ (q * p) + (r * p)
```

A polynomial over a commutative ring without constant term is precisely an equivalence class of terms of modulo `_≈_`.
Clearly, !ref(_≈_) is an equivalence relation.

```
≈-isEquivalence : IsEquivalence (_≈_ {X})
≈-isEquivalence = record { refl = ≈-refl ; sym = ≈-sym ; trans = ≈-trans }

module EqP {X : Set} where
    open import Preliminaries.Equivalence (≈-isEquivalence {X})
    open Eq public
```

To help the type checker, we introduce specialized versions of `_≈_` for terms over finitely many variables.

```
_≈₄_ : Term′ 4 → Term′ 4 → Set
p ≈₄ q = p ≈ q

_≈₅_ : Term′ 5 → Term′ 5 → Set
p ≈₅ q = p ≈ q

_≈₆_ : Term′ 6 → Term′ 6 → Set
p ≈₆ q = p ≈ q

_≈₇_ : Term (Var 7) → Term (Var 7) → Set
p ≈₇ q = p ≈ q

_≈₉_ : Term (Var 9) → Term (Var 9) → Set
p ≈₉ q = p ≈ q
```

## Algebraic properties

```
module AlgebraicProperties where
```

### Additive structure

```
    +-zeroˡ : ∀ (p : Term X) → 0T + p ≈ p
    +-zeroˡ p =
        begin
            0T + p
                ≈⟨ +-comm _ _ ⟩
            p + 0T
                ≈⟨ +-zeroʳ p ⟩
            p
        ∎ where open EqP

    +-identityˡ = +-zeroˡ

    +-identityʳ : ∀ (p : Term X) → p + 0T ≈ p
    +-identityʳ = +-zeroʳ

    +-invˡ : ∀ (p : Term X) → (- p) + p ≈ 0T
    +-invˡ p =
        begin
            (- p) + p
                ≈⟨ +-comm _ _ ⟩
            p + (- p)
                ≈⟨ +-invʳ p ⟩
            0T
        ∎ where open EqP

    -‿cong : {p q : Term X} → p ≈ q → (- p) ≈ (- q)
    -‿cong = ·-cong R-refl
```

```
    +-isMonoid : ∀ {X} → IsMonoid (_≈_ {X}) _+_ 0T
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
```

```
    +-isGroup : IsGroup (_≈_ {X}) _+_ 0T (-_)
    +-isGroup = record {
        isMonoid = +-isMonoid;
        inverse = record {fst = +-invˡ; snd = +-invʳ};
        ⁻¹-cong = -‿cong
        }

    +-isAbelianGroup : IsAbelianGroup (_≈_ {X}) _+_ 0T (-_)
    +-isAbelianGroup = record {
        isGroup = +-isGroup;
        comm = +-comm
        }
```

```
    isLeftModule : IsLeftModule (_≈_ {X}) _+_ -_ 0T _·_
    isLeftModule = record
        { +-isAbelianGroup = +-isAbelianGroup
        ; ·-cong = ·-cong
        ; distribˡ = ·-+-distrib
        ; distribʳ = +-·-distrib
        ; combatible = *-·-distrib
        ; identity = ·-one
        }
```

## Multiplicative structure

```
    *-distribˡ : (p q r : Term X) →
        p * (q + r) ≈ (p * q) + (p * r)
    *-distribˡ p q r = 
        begin
            p * (q + r) ≈⟨ *-comm p (q + r) ⟩
            (q + r) * p ≈⟨ *-distribʳ p q r ⟩
            q * p + r * p ≈⟨ +-cong (*-comm q p) (*-comm r p) ⟩
            p * q + p * r
        ∎ where open EqP
```

Terms form a commutative semigroup under multiplication.
It is not a monoid since we do not require a multiplicative identity.

```
    *-isSemigroup : IsSemigroup (_≈_ {X}) _*_
    *-isSemigroup = record {
        isMagma = record {
            isEquivalence = ≈-isEquivalence;
            ∙-cong = *-cong
        };
        assoc = *-assoc
        }

    *-isCommutativeSemigroup : ∀ {X} → IsCommutativeSemigroup (_≈_ {X}) _*_
    *-isCommutativeSemigroup = record { isSemigroup = *-isSemigroup; comm = *-comm }
```

## Ring structure

```
    isRingWithoutOne : IsRingWithoutOne (_≈_ {X}) _+_ _*_ -_ 0T
    isRingWithoutOne = record
        { +-isAbelianGroup = +-isAbelianGroup
        ; *-cong = *-cong
        ; *-assoc = *-assoc
        ; distrib = record {fst = *-distribˡ; snd = *-distribʳ}
        }

    isCommutativeRingWithoutOne : IsCommutativeRingWithoutOne (_≈_ {X}) _+_ _*_ -_ 0T
    isCommutativeRingWithoutOne = record { isRingWithoutOne = isRingWithoutOne; *-comm = *-comm }
```

## Algebra structure

Summarising, terms with the equivalence `_≈_` form an associative commutative algebra over `R`.

```
    isAlgebra : IsAlgebra (_≈_ {X}) _+_ _*_ -_ 0T _·_
    isAlgebra = record {
        isCommutativeRingWithoutOne = isCommutativeRingWithoutOne
        ; isLeftModule = isLeftModule
        ; compatible = ·-*-distrib }
```

These two properties follow from the ring structure.

```
    *-zeroˡ : ∀ (p : Term X) → 0T * p ≈ 0T
    *-zeroˡ = zeroˡ where open IsRingWithoutOne isRingWithoutOne

    *-zeroʳ : ∀ (p : Term X) → p * 0T ≈ 0T
    *-zeroʳ = zeroʳ where open IsRingWithoutOne isRingWithoutOne

    +-expand :
        ∀ (p : Term X) →
        ------------------------
        0R · p + 0R · p ≈ 0R · p

    +-expand p =
        begin
            0R · p + 0R · p
                ≈⟨ +-·-distrib _ _ _ ⟨
            (0R +R 0R) · p
                ≈⟨ ·-cong (+R-identityˡ _) ≈-refl ⟩
            0R · p
        ∎ where open EqP

    +-reduce :
        ∀ (p : Term X) →
        p + p ≈ p → 
        ----------------
        p ≈ 0T

    +-reduce p red =
        begin
            p
                ≈⟨ +-zeroʳ _ ⟨
            p + 0T
                ≈⟨ +-cong ≈-refl (+-invʳ _) ⟨
            p + (p - p)
                ≈⟨ +-assoc _ _ _ ⟨
            (p + p) - p
                ≈⟨ +-cong red ≈-refl ⟩
            p - p
                ≈⟨ +-invʳ _ ⟩
            0T
        ∎ where open EqP

    ·-zero : ∀ (p : Term X) → 0R · p ≈ 0T
    ·-zero p = +-reduce _ (+-expand _)

open AlgebraicProperties
```

## Properties of substitution

Substitution preserves equivalence of terms.
This comes in two flavours.
First of all, equivalent expressions are equivalent after substitution.

```
subst-inv :
    ∀ {p q : Term X} (ϱ : Subst X Y) →
    p ≈ q →
    ----------------------------------
    subst ϱ p ≈ subst ϱ q

subst-inv _ ≈-refl = ≈-refl
subst-inv _ (≈-sym p≈q) = ≈-sym (subst-inv _ p≈q)
subst-inv _ (≈-trans p≈r r≈q) = ≈-trans (subst-inv _ p≈r) (subst-inv _ r≈q)

subst-inv ϱ (·-cong c≈d p≈q) = c≈d ⟨ ·-cong ⟩ subst-inv ϱ p≈q
subst-inv ϱ (·-one p) = ·-one (subst ϱ p)
subst-inv ϱ (·-+-distrib c p q) = ·-+-distrib _ _ _
subst-inv ϱ (+-·-distrib p c d) = +-·-distrib _ _ _
subst-inv ϱ (·-*-distrib c p q) = ·-*-distrib _ _ _
subst-inv ϱ (*-·-distrib c d p) = *-·-distrib _ _ _

subst-inv _ (+-cong p₀≈p₁ q₀≈q₁) = subst-inv _ p₀≈p₁ ⟨ +-cong ⟩ subst-inv _ q₀≈q₁
subst-inv _ (+-zeroʳ p) = +-zeroʳ (subst _ p)
subst-inv _ (+-assoc p q r) = +-assoc (subst _ p) (subst _ q) (subst _ r)
subst-inv _ (+-comm p q) = +-comm (subst _ p) (subst _ q)
subst-inv _ (+-invʳ p) = +-invʳ (subst _ p)

subst-inv _ (*-cong p≈q p≈q₁) = subst-inv _ p≈q ⟨ *-cong ⟩ subst-inv _ p≈q₁
subst-inv _ (*-assoc p q r) = *-assoc (subst _ p) (subst _ q) (subst _ r)
subst-inv _ (*-comm p q) = *-comm (subst _ p) (subst _ q)
subst-inv _ (*-distribʳ p q r) = *-distribʳ (subst _ p) (subst _ q) (subst _ r)
```

Second, applying equivalent substitutions yields equivalent expressions.

```
private variable
    ϱ₀ ϱ₁ : Subst X Y

subst-inv′ :
    ∀ p → (∀ x → ϱ₀ x ≈ ϱ₁ x) →
    ---------------------------
    subst ϱ₀ p ≈ subst ϱ₁ p

subst-inv′ 0T _ = ≈-refl
subst-inv′ (var x) ϱ₀≈ϱ₁ = ϱ₀≈ϱ₁ x
subst-inv′ (c · q) ϱ₀≈ϱ₁ = R-refl ⟨ ·-cong ⟩ subst-inv′ q ϱ₀≈ϱ₁
subst-inv′ (p + q) ϱ₀≈ϱ₁ = subst-inv′ p ϱ₀≈ϱ₁ ⟨ +-cong ⟩ subst-inv′ q ϱ₀≈ϱ₁
subst-inv′ (p * q) ϱ₀≈ϱ₁ = subst-inv′ p ϱ₀≈ϱ₁ ⟨ *-cong ⟩ subst-inv′ q ϱ₀≈ϱ₁
```

## Vectors of equivalences

```
private variable
    ϱ η : Substᵥ n X

infix 4 _≈ᵥ_
infixr 5 _∷-≈_
data _≈ᵥ_ {X : Set} : ∀ {m : ℕ} → (ϱ η : Substᵥ m X) → Set where
    []-≈ : [] ≈ᵥ []
    _∷-≈_ : ∀ {p q} (p≈q : p ≈ q) (ϱ≈η : ϱ ≈ᵥ η) → (p ∷ ϱ) ≈ᵥ (q ∷ η)

≈ᵥ-lookup : ∀ {ϱ η : Substᵥ n X} → ϱ ≈ᵥ η → ∀ x → lookup ϱ x ≈ lookup η x
≈ᵥ-lookup (p≈q ∷-≈ _) zero = p≈q
≈ᵥ-lookup (_ ∷-≈ ϱ≈η) (suc x) = ≈ᵥ-lookup ϱ≈η x
```

```
subst-invᵥ :
    ∀ {p q : Term′ n} (ϱ : Substᵥ n X) →
    p ≈ q →
    ------------------------------------
    substᵥ ϱ p ≈ substᵥ ϱ q

subst-invᵥ ϱ p≈q = subst-inv (lookup ϱ) p≈q
```

```
subst-inv′ᵥ :
    ∀ (p : Term′ n) →
    ϱ ≈ᵥ η →
    -----------------------
    substᵥ ϱ p ≈ substᵥ η p

subst-inv′ᵥ {ϱ = ϱ} {η} p ϱ≈η = subst-inv′ p (≈ᵥ-lookup ϱ≈η)
```
