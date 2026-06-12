---
title: Algebraic preliminaries
comment: keep me
---

In this section we import the algebraic structures that we need in the rest of the formalisation.

```
{-# OPTIONS --sized-types #-}

open import Preliminaries.Base
module Preliminaries.Algebra (R : CommutativeRing) where

open import Algebra renaming (CommutativeRing to CR) public

private variable
    ℓ m : Level

open CR R renaming
    (Carrier to A;
    0# to 0R;
    1# to 1R;
    _+_ to _+R_;
    _*_ to _*R_;
    _≈_ to _≈R_;
    -_ to -R_;
    _-_ to _-R_;
    refl to R-refl;
    sym to R-sym;
    trans to R-trans;
    -‿cong to -R‿cong;
    -- -‿inverse to -R-inverse;
    -‿inverseˡ to -R-inverseˡ;
    -‿inverseʳ to -R-inverseʳ;
    +-identityˡ to +R-identityˡ;
    +-identityʳ to +R-identityʳ;
    +-identity to +R-identity;
    +-cong to +R-cong;
    +-comm to +R-comm;
    +-assoc to +R-assoc;
    *-cong to *R-cong;
    *-assoc to *R-assoc;
    *-comm to *R-comm;
    *-identity to *R-identity;
    *-identityˡ to *R-identityˡ;
    *-identityʳ to *R-identityʳ;
    distrib to R-distrib;
    distribˡ to R-distribˡ;
    distribʳ to R-distribʳ;
    zero to R-zero;
    zeroˡ to R-zeroˡ;
    zeroʳ to R-zeroʳ;
    +-isMonoid to +R-isMonoid;
    +-isGroup to +R-isGroup;
    +-isAbelianGroup to +R-isAbelianGroup;
    *-isSemigroup to *R-isSemigroup;
    *-isMonoid to *R-isMonoid;
    *-isCommutativeSemigroup to *R-isCommutativeSemigroup;
    *-isCommutativeMonoid to *R-isCommutativeMonoid;
    isRing to R-isRing;
    isRingWithoutOne to R-isRingWithoutOne;
    isCommutativeRing to R-isCommutativeRing)
    hiding (-‿inverse) public
```

We also define two algebraic structures that we will need in the rest of the formalisation,
namely left modules and associative, commutative algebras.

```
module _ {M : Set} (_≈_ : M → M → Set) where

    -- left module over the commutative ring R
    record IsLeftModule
        (_+_ : Op₂ M) (-_ : Op₁ M) (0# : M)
        (_·_ : A → M → M) : Set where

        field
            +-isAbelianGroup : IsAbelianGroup _≈_ _+_ 0# -_
            ·-cong : ∀ {c d} {x y} → c ≈R d → x ≈ y → (c · x) ≈ (d · y)
            distribˡ : ∀ x y z → (x · (y + z)) ≈ ((x · y) + (x · z))
            distribʳ : ∀ x y z → ((y +R z) · x) ≈ ((y · x) + (z · x))
            combatible : ∀ x y z → ((x *R y) · z) ≈ (x · (y · z))
            identity : ∀ x → (1R · x) ≈ x
    
    record IsCommutativeRingWithoutOne
        (+ * : Op₂ M) (- : Op₁ M) (0# : M) : Set where

        field
            isRingWithoutOne : IsRingWithoutOne _≈_ + * - 0#
            *-comm : Commutative _≈_ *

        open IsRingWithoutOne isRingWithoutOne public

    -- open IsCommutativeRingWithoutOne

    -- associative, commutative algebra
    record IsAlgebra
        (_+_ _*_ : Op₂ M) (-_ : Op₁ M) (0# : M)
        (_·_ : A → M → M) : Set where

        field
            isCommutativeRingWithoutOne : IsCommutativeRingWithoutOne _+_ _*_ -_ 0#
            isLeftModule : IsLeftModule _+_ -_ 0# _·_
            compatible : ∀ x y z → ((x · y) * z) ≈ (x · (y * z))
```

```
open IsEquivalence
open import Preliminaries.Equivalence isEquivalence

module EqR where
    open Eq public
```
