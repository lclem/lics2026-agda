---
title: "Special product rules 🚧"
---

```
{-# OPTIONS --guardedness --sized-types #-}
-- {-# OPTIONS --allow-unsolved-metas #-}

open import Preliminaries.Base
module Special.Polynomials (R : CommutativeRing) where

open import Preliminaries.Algebra R
open import Preliminaries.PolyExpr R as P
    using (PolyExpr; IntegralPolyExpr; 1P; 0P; con; ≈-con; +-con; *-con; con0; con1; var)
    renaming (_≈_ to _≈P_; _+_ to _+P_; _-_ to _-P_; _·_ to _·P_ ; _*_ to _*P_; ≈-refl to P-refl; module EqP to EqP′)

open P.AlgebraicProperties using () renaming (+-identityˡ to +P-identityˡ)

open import General.Terms R

```
# Equivalence of polynomial expressions

We introduce a natural equivalence relation on polynomial expressions
capturing commutativity, associativity, and distributivity of addition and multiplication.
This equivalence turns the set of polynomial expressions into a commutative algebra over `R`.

```
infix 4 _≈_ _≈₄_ _≈₅_ _≈₆_ _≈₇_ _≈₉_
private variable
    X Y : Set
    c d : A
    p q r p₀ p₁ q₀ q₁ r₀ r₁ : Term X
    n : ℕ

data _≈_ {X} : Term X → Term X → Set where

    ≈-refl : p ≈ p
    ≈-sym : p ≈ q → q ≈ p
    ≈-trans : p ≈ q → q ≈ r → p ≈ r

    ·-cong : (c≈d : c ≈R d) (p≈q : p ≈ q) → c · p ≈ d · q
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

≈-isEquivalence : IsEquivalence (_≈_ {X})
≈-isEquivalence = record { refl = ≈-refl ; sym = ≈-sym ; trans = ≈-trans }

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

≈-toPolyExpr :
    ∀ {X} {p q : Term X} →
    p ≈ q →
    ----------------------------
    toPolyExpr p ≈P toPolyExpr q

≈-toPolyExpr = go where
    go : p ≈ q → toPolyExpr p ≈P toPolyExpr q

    go ≈-refl = P-refl
    go (≈-sym p≈q) = P.≈-sym (go p≈q)
    go (≈-trans p≈q q≈r) = P.≈-trans (go p≈q) (go q≈r)
    go (·-cong c≈d p≈q) = P.*-cong (≈-con c≈d) (go p≈q)
    go (·-one p) = *-oneˡ (toPolyExpr p) where open P.AlgebraicProperties
    go (·-+-distrib c p q) = *-distrˡ _ _ _ where open P.AlgebraicProperties
    go (+-·-distrib p c d) = P.con-*-distrʳ _ _ _
    go (·-*-distrib c p q) = P.*-assoc _ _ _
    go (*-·-distrib c d p) = P.con-*-assoc _ _ _
    go (+-cong p≈p′ q≈q′) = P.+-cong (go p≈p′) (go q≈q′)
    go (+-zeroʳ p) = P.+-zeroʳ _
    go (+-assoc p q r) = P.+-assoc _ _ _
    go (+-comm p q) = P.+-comm _ _
    go (+-invʳ p) = P.+-invʳ _
    go (*-cong p≈p′ q≈q′) = P.*-cong (go p≈p′) (go q≈q′)
    go (*-assoc p q r) = P.*-assoc _ _ _
    go (*-comm p q) = P.*-comm _ _
    go (*-distribʳ p q r) = P.*-distrʳ _ _ _
```

A polynomial over a commutative ring is precisely an equivalence class of modulo `_≈_`.

```
module EqP {X : Set} where
    open import Preliminaries.Equivalence (≈-isEquivalence {X})
    open Eq public
```

## Algebraic properties

```
module AlgebraicProperties where

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

### Additive structure

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

    -- TODO: for some misterious reason this one does not work
    -- isLeftModule : IsLeftModule (_≈_ {X}) _+_ -_ 0T _·_
    -- isLeftModule = record
    --     { +-isAbelianGroup = +-isAbelianGroup
    --     ; distribˡ = ·-+-distrib
    --     ; distribʳ = +-·-distrib
    --     ; combatible = *-·-distrib
    --     ; identity = ·-one
    --     }
```

### Multiplicative structure

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


```
    -- this is rather a commutative semigroup

    -- *-identity : Identity (_≈_ {X}) 1T _*_
    -- *-identity = record { fst = *-oneˡ; snd = *-oneʳ }

    -- *-isMonoid : IsMonoid (_≈_ {X}) _*_ 1T
    -- *-isMonoid = record {
    --     isSemigroup = record {
    --     isMagma = record {
    --         isEquivalence = ≈-isEquivalence;
    --         ∙-cong = *-cong
    --     };
    --     assoc = *-assoc
    --     };
    --     identity = *-identity
    --     }

    -- *-isCommutativeMonoid : ∀ {X} → IsCommutativeMonoid (_≈_ {X}) _*_ 1T
    -- *-isCommutativeMonoid = record { isMonoid = *-isMonoid; comm = *-comm }
```

### Ring structure

```
    -- rather a nonunintal ring...
    isRingWithoutOne : IsRingWithoutOne (_≈_ {X}) _+_ _*_ -_ 0T
    isRingWithoutOne = record
        { +-isAbelianGroup = +-isAbelianGroup
        ; *-cong = *-cong
        ; *-assoc = *-assoc
        ; distrib = record {fst = *-distribˡ; snd = *-distribʳ}
        }

    -- isCommutativeRing : IsCommutativeRing (_≈_ {X}) _+_ _*_ -_ 0T 1T
    -- isCommutativeRing = record { isRing = isRing; *-comm = *-comm }

    -- isAlgebra : IsAlgebra (_≈_ {X}) _+_ _*_ -_ 0T 1T _·_
    -- isAlgebra = record {
    --     isRing = isCommutativeRing
    --     ; isLeftModule = isLeftModule
    --     ; compatible = ·-*-distrib }
    
    -- isRing.zeroˡ
    -- PolyExprCommRing : Set → CommutativeRing
    -- PolyExprCommRing X = record
    --     { Carrier = Term X
    --     ; _≈_ = (_≈_ {X})
    --     ; _+_ = _+_
    --     ; _*_ = _*_
    --     ; -_ = -_
    --     ; 0# = 0T
    --     ; 1# = 1T
    --     ; isCommutativeRing = isCommutativeRing
    --     }
```

These two properties follow from the ring structure.

```
    -- *-zeroˡ : ∀ (p : Term X) → 0T * p ≈ 0T
    -- *-zeroˡ {X} = CR.zeroˡ (PolyExprCommRing X)

    -- *-zeroʳ : ∀ (p : Term X) → p * 0T ≈ 0T
    -- *-zeroʳ {X} = CR.zeroʳ (PolyExprCommRing X)

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

Substitution preserves equivalence of polynomial expressions.
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

-- subst-inv ϱ (≈-var x) = lem-toPolyExpr _

subst-inv ϱ (·-cong c≈d p≈q) = ·-cong c≈d (subst-inv ϱ p≈q)
subst-inv ϱ (·-one p) = ·-one (subst ϱ p)
subst-inv ϱ (·-+-distrib c p q) = ·-+-distrib _ _ _
subst-inv ϱ (+-·-distrib p c d) = +-·-distrib _ _ _
subst-inv ϱ (·-*-distrib c p q) = ·-*-distrib _ _ _
subst-inv ϱ (*-·-distrib c d p) = *-·-distrib _ _ _

subst-inv _ (+-cong p₀≈p₁ q₀≈q₁) = +-cong (subst-inv _ p₀≈p₁) (subst-inv _ q₀≈q₁)
subst-inv _ (+-zeroʳ p) = +-zeroʳ (subst _ p)
subst-inv _ (+-assoc p q r) = +-assoc (subst _ p) (subst _ q) (subst _ r)
subst-inv _ (+-comm p q) = +-comm (subst _ p) (subst _ q)
subst-inv _ (+-invʳ p) = +-invʳ (subst _ p)

subst-inv _ (*-cong p≈q p≈q₁) = *-cong (subst-inv _ p≈q) (subst-inv _ p≈q₁)
subst-inv _ (*-assoc p q r) = *-assoc (subst _ p) (subst _ q) (subst _ r)
subst-inv _ (*-comm p q) = *-comm (subst _ p) (subst _ q)
subst-inv _ (*-distribʳ p q r) = *-distribʳ (subst _ p) (subst _ q) (subst _ r)
```

Second, applying equivalent substitutions yield equivalent expressions.

```
private variable
    ϱ ϱ₀ ϱ₁ : Subst X Y

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

```
-- extension of equivalence to vectors of polynomial expressions
infix 4 _≈ᵥ_
infixr 5 _∷-≈_
data _≈ᵥ_ {X : Set} : ∀ {m : ℕ} → (ϱ η : Substᵥ m X) → Set where
    []-≈ : [] ≈ᵥ []
    _∷-≈_ : ∀ {m p q} {ϱ η : Substᵥ m X} (p≈q : p ≈ q) (ϱ≈η : ϱ ≈ᵥ η) → (p ∷ ϱ) ≈ᵥ (q ∷ η)

≈ᵥ-lookup : ∀ {ϱ η : Substᵥ n X} → ϱ ≈ᵥ η → ∀ x → lookup ϱ x ≈ lookup η x
≈ᵥ-lookup (p≈q ∷-≈ _) zero = p≈q
≈ᵥ-lookup (_ ∷-≈ ϱ≈η) (suc x) = ≈ᵥ-lookup ϱ≈η x

subst-invᵥ :
    ∀ {p q : Term′ n} (ϱ : Substᵥ n X) →
    p ≈ q →
    ---------------------------------
    substᵥ ϱ p ≈ substᵥ ϱ q

subst-invᵥ ϱ p≈q = subst-inv (lookup ϱ) p≈q

subst-inv′ᵥ :
    ∀ (p : Term′ n) {ϱ η : Substᵥ n X} →
    ϱ ≈ᵥ η →
    ---------------------------------
    substᵥ ϱ p ≈ substᵥ η p

subst-inv′ᵥ p {ϱ} {η} ϱ≈η = subst-inv′ p (≈ᵥ-lookup ϱ≈η)
```

```
-- TODO: this needs to be adjusted to polynomial expressions without constant term (origin intercepting)

-- fromPolyExpr : PolyExpr X → Term X
-- fromPolyExpr (P.con c) = conT c
-- fromPolyExpr (P.var x) = var x
-- fromPolyExpr (p +P q) = fromPolyExpr p + fromPolyExpr q
-- fromPolyExpr (p *P q) = fromPolyExpr p * fromPolyExpr q

-- translate :
--     ∀ (p q : PolyExpr X) →
--     p ≈P q →
--     -------------------------------
--     fromPolyExpr p ≈ fromPolyExpr q

-- translate p q P.≈-refl = ≈-refl
-- translate p q (P.≈-sym p≈q) = ≈-sym (translate q p p≈q)
-- translate p q (P.≈-trans p≈r r≈q) = ≈-trans (translate _ _ p≈r) (translate _ _ r≈q)
-- translate (con c) (con d) (≈-con c≈d) = ·-cong c≈d ≈-refl
-- translate _ _ (P.+-cong p≈p′ q≈q′) = +-cong (translate _ _ p≈p′) (translate  _ _ q≈q′)
-- translate p q (+-con c d) =
--     begin
--         conT (c +R d)
--             ≈⟨⟩ 
--         (c +R d) · 1T
--             ≈⟨ +-·-distrib _ _ _ ⟩ 
--         c · 1T + d · 1T
--             ≈⟨⟩ 
--         conT c + conT d
--     ∎ where open EqP

-- translate p q (P.+-zeroʳ .q) =
--     begin
--         fromPolyExpr q + conT 0R
--             ≈⟨ +-cong ≈-refl (·-zero _) ⟩
--         fromPolyExpr q + 0T
--             ≈⟨ +-zeroʳ _ ⟩
--         fromPolyExpr q
--     ∎ where open EqP

-- translate _ _ (P.+-assoc _ _ _) = +-assoc _ _ _
-- translate _ _ (P.+-comm _ _) = +-comm _ _

-- translate _ _ (P.+-invʳ p) =
--     begin
--         fromPolyExpr p + ((-R 1R) · 1T) * fromPolyExpr p
--             ≈⟨ ≈-refl ⟨ +-cong ⟩ ·-one-* _ _ ⟩
--         fromPolyExpr p + (-R 1R) · fromPolyExpr p
--             ≈⟨⟩
--         fromPolyExpr p - fromPolyExpr p
--             ≈⟨ +-invʳ _ ⟩
--         0T
--             ≈⟨ ·-zero _ ⟨
--         conT 0R
--     ∎ where open EqP

-- translate _ _ (P.*-cong p₀≈p₁ q₀≈q₁) =
--     (translate _ _ p₀≈p₁) ⟨ *-cong ⟩ (translate _ _ q₀≈q₁)

-- translate p q (*-con c d) =
--     begin
--         conT (c *R d)
--             ≈⟨⟩
--         (c *R d) · 1T
--             ≈⟨ ·-cong R-refl (*-oneʳ _) ⟨
--         (c *R d) · (1T * 1T)
--             ≈⟨ *-·-distrib _ _ _ ⟩
--         c · (d · (1T * 1T))
--             ≈⟨ ·-cong R-refl (·-*-distrib _ _ _) ⟨
--         c · ((d · 1T) * 1T)
--             ≈⟨ ·-cong R-refl (*-comm _ _) ⟩
--         c · (1T * (d · 1T))
--             ≈⟨ ·-*-distrib _ _ _ ⟨
--         (c · 1T) * (d · 1T)
--             ≈⟨⟩
--         conT c * conT d
--     ∎ where open EqP

-- translate _ _ (P.*-oneʳ q) =
--     begin
--         fromPolyExpr q * conT 1R
--             ≈⟨⟩
--         fromPolyExpr q * (1R · 1T)
--             ≈⟨ ≈-refl ⟨ *-cong ⟩ (·-one _) ⟩
--         fromPolyExpr q * 1T
--             ≈⟨ *-oneʳ _ ⟩
--         fromPolyExpr q
--     ∎ where open EqP

-- translate _ _ (P.*-assoc p q r) = *-assoc _ _ _
-- translate _ _ (P.*-comm p q) = *-comm _ _

-- translate _ _ (P.*-distrʳ p q r) = *-distribʳ _ _ _

-- -- forbid scalar multiplication
-- private data IntegralTerm {X : Set} : Term X → Set where
--     0T : IntegralTerm 0T
--     var : ∀ x → IntegralTerm (var x)
--     _+_ : ∀ {p q} → IntegralTerm p → IntegralTerm q → IntegralTerm (p + q)
--     _*_ : ∀ {p q} → IntegralTerm p → IntegralTerm q → IntegralTerm (p * q)

-- sound :
--     {p : Term X} →
--     IntegralTerm p →
--     -------------------------------
--     p ≈ fromPolyExpr (toPolyExpr p)

-- sound 0T =
--     begin
--         0T ≈⟨ ·-zero _ ⟨
--         0R · 1T
--     ∎ where open EqP   

-- sound (var x) = ≈-refl
    
-- sound (p + q) = +-cong (sound p) (sound q)
-- sound (p * q) = *-cong (sound p) (sound q)

-- transfer :
--     ∀ (p q : Term X) →
--     IntegralTerm p →
--     IntegralTerm q →
--     toPolyExpr p ≈P toPolyExpr q →
--     ------------------------------
--     p ≈ q

-- transfer p q ip iq eq =
--     begin
--         p
--             ≈⟨ sound ip ⟩
--         fromPolyExpr (toPolyExpr p)
--             ≈⟨ translate _ _ eq ⟩
--         fromPolyExpr (toPolyExpr q)
--             ≈⟨ sound iq ⟨
--         q
--     ∎ where open EqP

-- isIntegralTerm? : WeaklyDecidable₁ (IntegralTerm {X})
-- isIntegralTerm? 0T = just 0T
-- isIntegralTerm? (var x) = just $ var x
-- isIntegralTerm? (_ · _) = nothing
-- isIntegralTerm? (p + q)
--     with isIntegralTerm? p | isIntegralTerm? q
-- ... | just p' | just q' = just $ p' + q'
-- ... | _ | _ = nothing
-- isIntegralTerm? (p * q)
--     with isIntegralTerm? p | isIntegralTerm? q
-- ... | just p' | just q' = just $ p' * q'
-- ... | _ | _ = nothing

-- open import Preliminaries.PolyExpr.Integers R
--     using (_≟′_)
--     -- renaming (_≟_ to _≟′_)

-- integralTransfer :
--     ∀ {p : Term X} →
--     IntegralTerm p →
--     -------------------------------
--     IntegralPolyExpr (toPolyExpr p)

-- integralTransfer 0T = con0
-- integralTransfer 1T = con1
-- integralTransfer (var x) = var x
-- integralTransfer (ip + iq) = integralTransfer ip P.+ integralTransfer iq
-- integralTransfer (ip * iq) = integralTransfer ip P.* integralTransfer iq

-- infix 4 _≟_ _≟₄_ _≟₅_ _≟₆_ _≟₇_ _≟₉_
-- _≟_ : ∀ {n} → WeaklyDecidable (_≈_ {Fin n})
-- p ≟ q
--     with isIntegralTerm? p | isIntegralTerm? q
-- ... | nothing | _ = nothing
-- ... | _ | nothing = nothing
-- ... | just ip | just iq
--     with integralTransfer ip | integralTransfer iq
-- ... | ip′ | iq′
--     with ip′ ≟′ iq′    
-- ... | just eq = just (transfer _ _ ip iq eq)
-- ... | nothing = nothing

-- _≟₄_ : WeaklyDecidable (_≈₄_)
-- p ≟₄ q = p ≟ q

-- _≟₅_ : WeaklyDecidable (_≈₅_)
-- p ≟₅ q = p ≟ q

-- _≟₆_ : WeaklyDecidable (_≈₆_)
-- p ≟₆ q = p ≟ q

-- _≟₇_ : WeaklyDecidable (_≈₇_)
-- p ≟₇ q = p ≟ q

-- _≟₉_ : WeaklyDecidable (_≈₉_)
-- p ≟₉ q = p ≟ q

-- equivTest : Term (Fin n) → Term (Fin n) → Bool
-- equivTest p q 
--     with p ≟ q
-- ... | just _ = true
-- ... | nothing = false
```