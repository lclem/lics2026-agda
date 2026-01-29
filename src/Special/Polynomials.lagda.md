---
title: "Polynomials"
---

In this section we introduce an natural equivalence on terms turning them into polynomial expressions (without constant term)
and we study their properties.

```
{-# OPTIONS --guardedness --sized-types #-}
{-# OPTIONS --allow-unsolved-metas #-}

open import Preliminaries.Base
module Special.Polynomials (R : CommutativeRing) where

open import Preliminaries.Algebra R
open import Preliminaries.PolyExpr R as P
    using (PolyExpr; IntegralPolyExpr; 1P; 0P; con; ≈-con; +-con; *-con; con0; con1; var)
    renaming (_≈_ to _≈P_; _+_ to _+P_; _-_ to _-P_; _·_ to _·P_ ; _*_ to _*P_; ≈-refl to P-refl; module EqP to EqP′)

open P.AlgebraicProperties using () renaming (+-identityˡ to +P-identityˡ)

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
    +-invʳ : ∀ p → p - p ≈ 0T -- this rule "loses information" in one direction

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

    ·-zero′ : ∀ c → _≈_ {X} 0T (c · 0T)
    ·-zero′ c = {!   !}

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

# Relation to polynomial expressions

In this section we relate terms modulo `_≈_` to polynomial expressions.
We begin by showing that converting terms to polynomial expressions
respects term equivalence `_≈_`.

```
≈-term→poly :
    ∀ {X} {p q : Term X} →
    p ≈ q →
    ----------------------------
    term→poly p ≈P term→poly q

≈-term→poly = go where

    go : p ≈ q → term→poly p ≈P term→poly q
    go ≈-refl = P-refl
    go (≈-sym p≈q) = P.≈-sym (go p≈q)
    go (≈-trans p≈q q≈r) = P.≈-trans (go p≈q) (go q≈r)
    go (·-cong c≈d p≈q) = P.*-cong (≈-con c≈d) (go p≈q)
    go (·-one p) = *-oneˡ (term→poly p) where open P.AlgebraicProperties
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

# Decidability of equivalence of terms

```
-- private data IntegralTerm {X : Set} : Term X → Set where
--     -- 0T : IntegralTerm 0T
--     var : ∀ x → IntegralTerm (var x)
--     _+_ : ∀ {p q} → IntegralTerm p → IntegralTerm q → IntegralTerm (p + q)
--     _*_ : ∀ {p q} → IntegralTerm p → IntegralTerm q → IntegralTerm (p * q)

-- private data IntPolyExpr {X : Set} : PolyExpr X → Set where
--     -- 0IP : IntPolyExpr 0P
--     var : ∀ x → IntPolyExpr (var x)
--     _+_ : ∀ {p q} → IntPolyExpr p → IntPolyExpr q → IntPolyExpr (p +P q)
--     _*_ : ∀ {p q} → IntPolyExpr p → IntPolyExpr q → IntPolyExpr (p *P q)

-- iterm→poly :
--     ∀ {u : Term X} →
--     IntegralTerm u →
--     -------------------------
--     IntPolyExpr (term→poly u)

-- -- iterm→poly 0T = 0IP
-- iterm→poly (var x) = var x
-- iterm→poly (iu + iv) = iterm→poly iu + iterm→poly iv
-- iterm→poly (iu * iv) = iterm→poly iu * iterm→poly iv

-- poly→term : PolyExpr X → Term (Maybe X)
-- poly→term (con c) = c · var nothing
-- poly→term (var x) = var (just x)
-- poly→term (p P.+ q) = poly→term p + poly→term q
-- poly→term (p P.* q) = poly→term p * poly→term q

-- translate-help-1 :
--     ∀ {p q : PolyExpr X} →
--     IntPolyExpr p →
--     p ≈P q →
--     -----------------------
--     IntPolyExpr q

-- translate-help-2 :
--     ∀ {p q : PolyExpr X} →
--     IntPolyExpr q →
--     p ≈P q →
--     -----------------------
--     IntPolyExpr p

-- translate-help-1 ip P.≈-refl = ip
-- translate-help-1 ip (P.≈-sym p≈q) = translate-help-2 ip p≈q
-- translate-help-1 ip (P.≈-trans p≈q p≈q₁) = translate-help-1 (translate-help-1 ip p≈q) p≈q₁
-- translate-help-1 (ip + ip′) (P.+-cong p≈p′ q≈q′) = translate-help-1 ip p≈p′ + translate-help-1 ip′ q≈q′
-- translate-help-1 (ip + _) (P.+-zeroʳ _) = ip
-- translate-help-1 ((ip + iq) + ir) (P.+-assoc p q r) = ip + (iq + ir)
-- translate-help-1 (ip + iq) (P.+-comm p q) = iq + ip
-- translate-help-1 (_ + (() * _)) (P.+-invʳ p)
-- translate-help-1 ip (P.*-cong p≈q p≈q₁) = {!   !}
-- translate-help-1 ip (P.*-oneʳ _) = {!   !}
-- translate-help-1 ip (P.*-assoc p q r) = {!   !}
-- translate-help-1 ip (P.*-comm p q) = {!   !}
-- translate-help-1 ip (P.*-distrʳ p q r) = {!   !}

-- translate-help-2 ip p≈q = {!   !}

-- translate :
--     ∀ {p q : PolyExpr X}
--     (ip : IntPolyExpr p)
--     (iq : IntPolyExpr q) →
--     p ≈P q →
--     ---------------------------
--     poly→term p ≈ poly→term q

-- translate ip iq P.≈-refl = ≈-refl
-- translate ip iq (P.≈-sym p≈q) = ≈-sym (translate iq ip p≈q)
-- translate ip iq (P.≈-trans p≈r r≈q) = ≈-trans (translate ip (translate-help-1 ip p≈r) p≈r) (translate (translate-help-1 ip p≈r) iq r≈q)
-- translate (ip + ip′) (iq + iq′) (P.+-cong p≈p′ q≈q′) = +-cong (translate ip iq  p≈p′) (translate ip′ iq′ q≈q′)
-- translate ip iq (P.+-zeroʳ _) = {!   !} -- ok
-- translate ip iq (P.+-assoc p q r) = +-assoc _ _ _
-- translate ip iq (P.+-comm p q) = +-comm _ _
-- translate (ip * ip′) (iq * iq′) (P.*-cong p≈p′ q≈q′) = *-cong  (translate ip iq p≈p′) (translate ip′ iq′ q≈q′)
-- translate (ip * ()) iq (P.*-oneʳ _) -- = {!   !}
-- translate ip iq (P.*-assoc p q r) = *-assoc _ _ _
-- translate ip iq (P.*-comm p q) = *-comm _ _
-- translate ip iq (P.*-distrʳ p q r) = *-distribʳ _ _ _

-- justt : Term X → Term (Maybe X)
-- justt 0T = 0T
-- justt (var x) = var (just x)
-- justt (c · p) = c · justt p
-- justt (p + q) = justt p + justt q
-- justt (p * q) = justt p * justt q

-- justt-Integral :
--     ∀ {u : Term X} →
--     IntegralTerm u →
--     ----------------------
--     IntegralTerm (justt u)

-- justt-Integral (var x) = var (just x)
-- justt-Integral (iu + iv) = justt-Integral iu + justt-Integral iv
-- justt-Integral (iu * iv) = justt-Integral iu * justt-Integral iv

-- justtt-lem1 :
--     ∀ {u : Term X} {v : Term (Maybe X)} →
--     IntegralTerm u →
--     justt u ≈ v →
--     ------------------
--     ∃[ t ] v ≡ justt t

-- justtt-lem2 :
--     ∀ {u : Term X} {v : Term (Maybe X)} →
--     IntegralTerm u →
--     v ≈ justt u →
--     ------------------
--     ∃[ t ] v ≡ justt t

-- justtt-lem1 (var x) ≈-refl = var x ,, refl
-- justtt-lem1 (var x) (≈-sym ass) = justtt-lem2 (var x) ass
-- justtt-lem1 (var x) (≈-trans ass ass₁) = {!   !}
-- justtt-lem1 (iu + iv) ass = {!   !}
-- justtt-lem1 (iu * iv) ass = {!   !}

-- justtt-lem2 = {!   !}

-- justtt-sound :
--     ∀ {u v : Term X} →
--     IntegralTerm u →
--     IntegralTerm v →
--     justt u ≈ justt v →
--     -------------------
--     u ≈ v

-- justtt-sound iu iv u≈v = {!   !}

-- sound :
--     ∀ {u : Term X} →
--     IntegralTerm u →
--     ---------------------------
--     justt u ≈ poly→term (term→poly u)

-- -- sound 0T = ≈-sym (·-zero _)
-- sound (var x) = ≈-refl
-- sound (iu + iv) = +-cong (sound iu) (sound iv)
-- sound (iu * iv) = *-cong (sound iu) (sound iv)

-- transfer′ :
--     ∀ {u v : Term X}
--     (iu : IntegralTerm u)
--     (iv : IntegralTerm v) →
--     term→poly u ≈P term→poly v →
--     ----------------------------
--     justt u ≈ justt v

-- transfer′ {u = u} {v} iu iv p≈q =
--     begin
--         justt u
--             ≈⟨ sound iu ⟩
--         poly→term (term→poly u)
--             ≈⟨ translate (iterm→poly iu) (iterm→poly iv) p≈q ⟩
--         poly→term (term→poly v)
--             ≈⟨ sound iv ⟨
--         justt v
--     ∎ where open EqP

-- transfer :
--     ∀ {u v : Term X}
--     (iu : IntegralTerm u)
--     (iv : IntegralTerm v) →
--     term→poly u ≈P term→poly v →
--     ----------------------------
--     u ≈ v

-- transfer {u = u} {v} iu iv p≈q = {!   !}
--     -- begin
--     --     u
--     --         ≈⟨ sound iu ⟩
--     --     poly→term (term→poly u)
--     --         ≈⟨ translate ? ? p≈q ⟩
--     --     poly→term (term→poly v)
--     --         ≈⟨ sound iv ⟨
--     --     v
--     -- ∎ where open EqP

-- isIntegralTerm? : WeaklyDecidable₁ (IntegralTerm {X})
-- isIntegralTerm? 0T = nothing -- just 0T
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

-- open import Preliminaries.Integers R
--     using (_≟′_)
--     -- renaming (_≟_ to _≟′_)

-- integralTransfer :
--     ∀ {p : Term X} →
--     IntegralTerm p →
--     -------------------------------
--     IntegralPolyExpr (term→poly p)

-- -- integralTransfer 0T = con0
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
-- ... | just eq = just (transfer ip iq eq)
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

-- -- equivTest : Term (Fin n) → Term (Fin n) → Bool
-- -- equivTest p q 
-- --     with p ≟ q
-- -- ... | just _ = true
-- -- ... | nothing = false
```

# Directed equivalence of terms

```
-- infix 4 _↝_
-- data _↝_ {X} : Term X → Term X → Set where

--     ↝-refl : p ↝ p
--     ↝-trans : p ↝ q → q ↝ r → p ↝ r

--     ·-cong : c ≈R d → p ↝ q → c · p ↝ d · q
--     -- ·-cong′ : c ≈R d → c · p ↝ d · q → p ↝ q

--     ·-one : ∀ p → 1R · p ↝ p
--     ·-+-distrib : ∀ c p q → c · (p + q) ↝ c · p + c · q
--     +-·-distrib : ∀ p c d → c · p + d · p ↝ (c +R d) · p
--     ·-*-distrib : ∀ c p q → (c · p) * q ↝ c · (p * q)
--     *-·-distrib : ∀ c d p → c · (d · p) ↝ (c *R d) · p

--     +-cong : p₀ ↝ p₁ → q₀ ↝ q₁ → p₀ + q₀ ↝ p₁ + q₁
--     +-zeroʳ : ∀ p → p + 0T ↝ p
--     +-assoc : ∀ p q r → (p + q) + r ↝ p + (q + r)
--     +-assoc′ : ∀ p q r → p + (q + r) ↝ (p + q) + r
--     +-comm : ∀ p q → p + q ↝ q + p
--     +-invʳ : ∀ p → p - p ↝ 0T
--     -- alternative rule
--     -- +-canc : ∀ p q r → p + q ↝ p + r → q ↝ r

--     *-cong : p₀ ↝ p₁ → q₀ ↝ q₁ → p₀ * q₀ ↝ p₁ * q₁
--     *-assoc : ∀ p q r → (p * q) * r ↝ p * (q * r)
--     *-comm : ∀ p q → p * q ↝ q * p
--     *-distribʳ : ∀ p q r → (q + r) * p ↝ (q * p) + (r * p)

-- data Term-Prop (Var-Prop : X → Set) : Term X → Set where
--     0T : Term-Prop Var-Prop 0T
--     var : ∀ {x} → Var-Prop x → Term-Prop Var-Prop (var x)
--     _·_ : ∀ {u} c → Term-Prop Var-Prop u → Term-Prop Var-Prop (c · u)
--     _+_ : ∀ {u v} → Term-Prop Var-Prop u → Term-Prop Var-Prop v → Term-Prop Var-Prop (u + v)
--     _*_ : ∀ {u v} → Term-Prop Var-Prop u → Term-Prop Var-Prop v → Term-Prop Var-Prop (u * v)

-- module _ (Var-Prop : X → Set) where

--     proj : Term (∃[ x ] Var-Prop x) → Term X
--     proj 0T = 0T
--     proj (var (x ,, _)) = var x
--     proj (c · α) = c · proj α
--     proj (α + β) = proj α + proj β
--     proj (α * β) = proj α * proj β
    
--     lift : (u : Term (∃ Var-Prop)) → Term-Prop Var-Prop (proj u)
--     lift 0T = 0T
--     lift (var (_ ,, px)) = var px
--     lift (c · u) = c · lift u
--     lift (u + v) = lift u + lift v
--     lift (u * v) = lift u * lift v

--     forget : ∀ {u : Term X} → Term-Prop Var-Prop u → Term (∃ Var-Prop)
--     forget 0T = 0T
--     forget (var {x = x} px) = var (x ,, px)
--     forget (c · pu) = c · forget pu
--     forget (pu + pv) = forget pu + forget pv
--     forget (pu * pv) = forget pu * forget pv

--     Term-Prop-↝ :
--         ∀ {α β} →
--         Term-Prop Var-Prop α →
--         α ↝ β →
--         ----------------------
--         Term-Prop Var-Prop β

--     Term-Prop-↝ pα ↝-refl = pα
--     Term-Prop-↝ pα (↝-trans α↝β α↝β₁) = Term-Prop-↝ (Term-Prop-↝ pα α↝β) α↝β₁
--     Term-Prop-↝ (_ · pα) (·-cong _ α↝β) = _ · Term-Prop-↝ pα α↝β
--     Term-Prop-↝ (_ · pα) (·-one _) = pα
--     Term-Prop-↝ (_ · (pα + pα₁)) (·-+-distrib _ _ _) = (_ · pα) + (_ · pα₁)
--     Term-Prop-↝ ((_ · pα) + _) (+-·-distrib _ _ _) = _ · pα
--     Term-Prop-↝ ((_ · pα) * pα₁) (·-*-distrib _ _ _) = _ · (pα * pα₁)
--     Term-Prop-↝ (_ · (_ · pα)) (*-·-distrib _ _ _) = _ · pα
--     Term-Prop-↝ (pα + pα₁) (+-cong α↝β α↝β₁)
--         = Term-Prop-↝ pα α↝β + Term-Prop-↝ pα₁ α↝β₁
--     Term-Prop-↝ (pα + _) (+-zeroʳ _) = pα
--     Term-Prop-↝ ((pα + pα₂) + pα₁) (+-assoc _ _ _) = pα + (pα₂ + pα₁)
--     Term-Prop-↝ (pα + (pα₂ + pα₁)) (+-assoc′ _ _ _) = (pα + pα₂) + pα₁
--     Term-Prop-↝ (pα + pα₁) (+-comm _ _) = pα₁ + pα
--     Term-Prop-↝ _ (+-invʳ _) = 0T
--     Term-Prop-↝ (pα * pα₁) (*-cong α↝β α↝β₁)
--         = Term-Prop-↝ pα α↝β * Term-Prop-↝ pα₁ α↝β₁
--     Term-Prop-↝ ((pα * pα₂) * pα₁) (*-assoc _ _ _) = pα * (pα₂ * pα₁)
--     Term-Prop-↝ (pα * pα₁) (*-comm _ _) = pα₁ * pα
--     Term-Prop-↝ ((pα + pα₂) * pα₁) (*-distribʳ _ _ _) = (pα * pα₁) + (pα₂ * pα₁)

--     confluence :
--         ∀ {α β₁ β₂ : Term X} →
--         α ↝ β₁ →
--         α ↝ β₂ →
--         ----------------------
--         ∃[ γ ] β₁ ↝ γ × β₂ ↝ γ

--     confluence ↝-refl α↝β₂ = _ ,, α↝β₂ ,, ↝-refl
--     confluence α↝β₁ ↝-refl = _ ,, ↝-refl ,, α↝β₁

--     confluence (↝-trans α↝γ γ↝β₁) α↝β₂
--         with confluence α↝γ α↝β₂
--     ... | _ ,, γ↝δ ,, β₂↝δ
--         with confluence γ↝β₁ γ↝δ
--     ... | _ ,, β₁↝ε ,, δ↝ε = _ ,, β₁↝ε ,, ↝-trans β₂↝δ δ↝ε

--     -- confluence α↝β₁ (↝-trans α↝γ γ↝β₂)
--     --     with confluence α↝β₁ α↝γ
--     -- ... | _ ,, β₁↝δ ,, γ↝δ
--     --     with confluence γ↝δ γ↝β₂
--     -- ... | _ ,, δ↝ε ,, β₂↝ε  = _ ,, ↝-trans β₁↝δ δ↝ε ,, β₂↝ε

--     confluence (·-cong x₁ α↝β₁) α↝β₂ = {!   !}

--     confluence (·-one _) α↝β₂ = {!   !}

--     confluence (·-+-distrib c p q) α↝β₂ = {!   !}

--     confluence (+-·-distrib p c d) α↝β₂ = {!   !}

--     confluence (·-*-distrib c p q) α↝β₂ = {!   !}

--     confluence (*-·-distrib c d p) α↝β₂ = {!   !}

--     confluence (+-cong α↝β₁ α↝β₃) α↝β₂ = {!   !}

--     confluence (+-zeroʳ _) α↝β₂ = {!   !}

--     confluence (+-assoc _ _ _) α↝β₂ = _ ,, ↝-trans (+-assoc′ _ _ _) α↝β₂ ,, ↝-refl
--     confluence (+-assoc′ _ _ _) α↝β₂ = _ ,, ↝-trans (+-assoc _ _ _) α↝β₂ ,, ↝-refl

--     confluence (+-comm p q) α↝β₂ = _ ,, ↝-trans (+-comm q p) α↝β₂ ,, ↝-refl

--     confluence (+-invʳ p) α↝β₂ = _ ,, {!   !} ,, {!   !}

--     confluence (*-cong α↝β₁ α↝β₃) α↝β₂ = {!   !}

--     confluence (*-assoc p q r) α↝β₂ = {!   !}

--     confluence (*-comm p q) α↝β₂ = _ ,, ↝-trans (*-comm q p) α↝β₂ ,, ↝-refl

--     confluence (*-distribʳ p q r) α↝β₂ = {!   !}

--     ≈→↝ :
--         ∀ {α β : Term X} →
--         α ≈ β →
--         --------------------
--         ∃[ γ ] α ↝ γ × β ↝ γ

--     ≈→↝ ≈-refl = _ ,, ↝-refl ,, ↝-refl

--     ≈→↝ (≈-sym α≈β)
--         with ≈→↝ α≈β
--     ... | _ ,, β↝γ ,, α↝γ = _ ,, α↝γ ,, β↝γ

--     ≈→↝ (≈-trans α≈γ γ≈β)
--         with ≈→↝ α≈γ | ≈→↝ γ≈β
--     ... | _ ,, α↝γ₁ ,, γ↝γ₁ | _ ,, γ↝γ₂ ,, β↝γ₂
--         with confluence γ↝γ₁ γ↝γ₂
--     ... | _ ,, γ₁↝δ ,, γ₂↝δ
--         = _ ,, ↝-trans α↝γ₁ γ₁↝δ ,, ↝-trans β↝γ₂ γ₂↝δ

--     ≈→↝ (·-cong c≈d α≈β)
--         with ≈→↝ α≈β
--     ... | _ ,, α↝γ ,, β↝γ  = _ ,, ·-cong c≈d α↝γ ,, ·-cong R-refl β↝γ
    
--     ≈→↝ (·-one _) = _ ,, ·-one _ ,, ↝-refl

--     ≈→↝ (·-+-distrib c p q) = c · p + c · q ,, ·-+-distrib c p q ,, ↝-refl

--     ≈→↝ (+-·-distrib p c d) = (c +R d) · p ,, ↝-refl ,, +-·-distrib p c d

--     ≈→↝ (·-*-distrib c p q) = c · p * q ,, ·-*-distrib c p q ,, ↝-refl

--     ≈→↝ (*-·-distrib c d p) = (c *R d) · p ,, ↝-refl ,, *-·-distrib c d p

--     ≈→↝ (+-cong α≈α′ β≈β′)
--         with ≈→↝ α≈α′ | ≈→↝ β≈β′
--     ... | _ ,, α↝γ ,, α′↝γ | _ ,, β↝δ ,, β′↝δ = _ ,, +-cong α↝γ  β↝δ ,, +-cong α′↝γ β′↝δ

--     ≈→↝ (+-zeroʳ _) = _ ,, +-zeroʳ _ ,, ↝-refl

--     ≈→↝ (+-assoc p q r) = p + q + r ,, +-assoc p q r ,, ↝-refl

--     ≈→↝ (+-comm p q) = q + p ,, +-comm p q ,, ↝-refl

--     ≈→↝ (+-invʳ p) = 0T ,, +-invʳ p ,, ↝-refl

--     ≈→↝ (*-cong α≈α′ β≈β′)
--         with ≈→↝ α≈α′ | ≈→↝ β≈β′
--     ... | _ ,, α↝γ ,, α′↝γ | _ ,, β↝δ ,, β′↝δ = _ ,, *-cong α↝γ  β↝δ ,, *-cong α′↝γ β′↝δ

--     ≈→↝ (*-assoc p q r) = p * q * r ,, *-assoc p q r ,, ↝-refl

--     ≈→↝ (*-comm p q) = q * p ,, *-comm p q ,, ↝-refl

--     ≈→↝ (*-distribʳ p q r) = _ ,, *-distribʳ p q r ,, ↝-refl

--     Injective : ∀ {X : Set} → (X → Set) → Set
--     Injective P = ∀ {x} → (p q : P x) → p ≡ q
    
--     module _ (inj : Injective Var-Prop) where

--         inj′ : Injective (Term-Prop Var-Prop)
--         inj′ = {!   !}

--         ↝-forget :
--             ∀ {α β} →
--             (pα : Term-Prop Var-Prop α) →
--             (pβ : Term-Prop Var-Prop β) →
--             α ↝ β →
--             -----------------------------
--             forget pα ≈ forget pβ

--         ↝-forget pα pβ ↝-refl rewrite inj′ pα pβ = ≈-refl
--         ↝-forget pα pβ (↝-trans α↝β α↝β₁) = {!   !}
--         ↝-forget pα pβ (·-cong x₁ α↝β) = {!   !}
--         ↝-forget pα pβ (·-one _) = {!   !}
--         ↝-forget pα pβ (·-+-distrib c p q) = {!   !}
--         ↝-forget pα pβ (+-·-distrib p c d) = {!   !}
--         ↝-forget pα pβ (·-*-distrib c p q) = {!   !}
--         ↝-forget pα pβ (*-·-distrib c d p) = {!   !}
--         ↝-forget pα pβ (+-cong α↝β α↝β₁) = {!   !}
--         ↝-forget pα pβ (+-zeroʳ _) = {!   !}
--         ↝-forget pα pβ (+-assoc p q r) = {!   !}
--         ↝-forget pα pβ (+-assoc′ p q r) = {!   !}
--         ↝-forget pα pβ (+-comm p q) = {!   !}
--         ↝-forget pα pβ (+-invʳ p) = {!   !}
--         ↝-forget pα pβ (*-cong α↝β α↝β₁) = {!   !}
--         ↝-forget pα pβ (*-assoc p q r) = {!   !}
--         ↝-forget pα pβ (*-comm p q) = {!   !}
--         ↝-forget pα pβ (*-distribʳ p q r) = {!   !}

--         corollary : 
--             ∀ {α β} →
--             (pα : Term-Prop Var-Prop α) →
--             (pβ : Term-Prop Var-Prop β) →
--             α ≈ β →
--             -----------------------------
--             forget pα ≈ forget pβ
        
--         corollary pα pβ α≈β
--             with ≈→↝ α≈β
--         ... | γ ,, α↝γ ,, β↝γ
--             with ↝-forget pα (Term-Prop-↝ pα α↝γ) α↝γ | ↝-forget pβ (Term-Prop-↝ pα α↝γ) β↝γ
--         ... | eq | eq′ = ≈-trans eq (≈-sym eq′)

--     -- if two terms are equivalent after projecting away the variable properties,
--     -- then they were equivalent to begin with;
--     transfer :
--         ∀ (α β : Term (∃ Var-Prop)) →
--         proj α ≈ proj β →
--         -----------------------------
--         α ≈ β

--     transfer α β pα≈pβ = {! pα≈pβ !}
```
