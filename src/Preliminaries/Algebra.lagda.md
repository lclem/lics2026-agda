---
title: Algebraic preliminaries 🚧
---

```
{-# OPTIONS --allow-unsolved-metas #-}

open import Preliminaries.Base
module Preliminaries.Algebra (R : CommutativeRing) where

open import Algebra renaming (CommutativeRing to CR) public
open import Preliminaries.Structures using (IsCommutativeRingWithoutOne) public

module _ where

    open CR R renaming (refl to R-refl; sym to R-sym; trans to R-trans)
    open import Preliminaries.Equivalence isEquivalence

    -- additive inverses are unique
    +-inv-unique : ∀ a b → a + b ≈ 0# → b ≈ - a
    +-inv-unique a b a+b≈0 = begin
        b
            ≈⟨ +-identityʳ _ ⟨
        b + 0#
            ≈⟨ (R-refl ⟨ +-cong ⟩ -‿inverseʳ _) ⟨
        b + (a - a)
            ≈⟨ +-assoc _ _ _ ⟨
        (b + a) - a
            ≈⟨ ((R-trans (+-comm _ _) a+b≈0) ⟨ +-cong ⟩ R-refl) ⟩
        0# - a
            ≈⟨ +-identityˡ _ ⟩
        - a
        ∎ where open Eq

    0≈-0 : 0# ≈ - 0#
    0≈-0 = +-inv-unique _ _ $ +-identityˡ _

    -‿-‿lem : ∀ a → - (- a) ≈ a
    -‿-‿lem a = R-sym $ +-inv-unique _ _ $ -‿inverseˡ a

    add-inv : ∀ a → a + (- 1#) * a ≈ 0#
    add-inv a =
        begin
            a + (- 1#) * a
                ≈⟨ (*-identityˡ _ ⟨ +-cong ⟩ R-refl) ⟨
            1# * a + (- 1#) * a
                ≈⟨ distribʳ _ _ _ ⟨
            (1# + - 1#) * a
                ≈⟨ (-‿inverseʳ _ ⟨ *-cong ⟩ R-refl) ⟩
            0# * a
                ≈⟨ zeroˡ _ ⟩
            0#
        ∎ where open Eq

    gather : ∀ a b → a + b * a ≈ (1# + b) * a
    gather a b =
        begin
            a + b * a
                ≈⟨ *-identityˡ _ ⟨ +-cong ⟩ R-refl ⟨
            (1# * a) + (b * a)
                ≈⟨ distribʳ _ _ _ ⟨
            (1# + b) * a
        ∎ where open Eq

    a+-0≈a : ∀ a → a + (- 0#) ≈ a
    a+-0≈a a =
        begin
            a + (- 0#)
                ≈⟨ R-refl ⟨ +-cong ⟩ 0≈-0 ⟨
            a + 0#
                ≈⟨ +-identityʳ _ ⟩
            a
        ∎ where open Eq

    middle-swap : ∀ a b c d → (a + b) + (c + d) ≈ (a + c) + (b + d)
    middle-swap a b c d =
        begin
            (a + b) + (c + d)
                ≈⟨ +-assoc _ _ _ ⟩
            a + (b + (c + d))
                ≈⟩ R-refl ⟨ +-cong ⟩ +-assoc _ _ _ ⟩
            a + ((b + c) + d)
                ≈⟨ R-refl ⟨ +-cong ⟩ (+-comm _ _ ⟨ +-cong ⟩ R-refl) ⟩
            a + ((c + b) + d)
                ≈⟨ R-refl ⟨ +-cong ⟩ +-assoc _ _ _ ⟩
            a + (c + (b + d))
                ≈⟩ +-assoc _ _ _ ⟩
            (a + c) + (b + d)
        ∎ where open Eq
        
    -+-hom : ∀ a b → - (a + b) ≈ - a - b
    -+-hom a b = R-sym (+-inv-unique _ _ lem) where

        lem : (a + b) + (- a - b) ≈ 0#
        lem =
            begin
                (a + b) + (- a - b)
                    ≈⟨ middle-swap _ _ _ _ ⟩
                (a - a) + (b - b)
                    ≈⟨ -‿inverseʳ _ ⟨ +-cong ⟩ -‿inverseʳ _ ⟩
                0# + 0#
                    ≈⟨ +-identityˡ _ ⟩
                0#
            ∎ where open Eq
   
    -[a-b]≈b-a : ∀ a b → - (a - b) ≈ b - a
    -[a-b]≈b-a a b =
        begin
            - (a - b)
                ≈⟨ -+-hom _ _ ⟩
            - a + - (- b)
                ≈⟨ R-refl ⟨ +-cong ⟩ -‿-‿lem _ ⟩
            - a + b
                ≈⟨ +-comm _ _ ⟩
            b - a
        ∎ where open Eq

    -[a*b]≈a*-b : ∀ a b → - (a * b) ≈ a * - b
    -[a*b]≈a*-b a b = R-sym $ +-inv-unique _ _ lem where

        lem : a * b + a * - b ≈ 0#
        lem =
            begin
                a * b + a * - b ≈⟩ distribˡ a  b (- b) ⟩
                a * (b + - b) ≈⟨⟩
                a * (b - b) ≈⟨ R-refl ⟨ *-cong ⟩ -‿inverseʳ _ ⟩
                a * 0# ≈⟨ zeroʳ _ ⟩
                0#
            ∎ where open Eq

    -[a*b]≈-a*b : ∀ a b → - (a * b) ≈ - a * b
    -[a*b]≈-a*b a b =
        begin
            - (a * b) ≈⟨ (-‿cong $ *-comm _ _) ⟩
            - (b * a) ≈⟨ -[a*b]≈a*-b _ _ ⟩
            b * - a ≈⟨ *-comm _ _ ⟩
             - a * b
        ∎ where open Eq

    a*b≈-a*-b : ∀ a b → a * b ≈ - a * - b
    a*b≈-a*-b a b = R-sym lem where

        lem : - a * - b ≈ a * b
        lem = 
            begin
                - a * - b ≈⟨ -[a*b]≈-a*b _ _ ⟨
                - (a * - b) ≈⟨ -‿cong (-[a*b]≈a*-b _ _) ⟨
                - (- (a * b)) ≈⟨ -‿-‿lem _ ⟩
                a * b
            ∎ where open Eq

    one-plus-lem : ∀ a b → (1# + a) - (1# + b) ≈ a - b
    one-plus-lem a b =
        begin
            (1# + a) - (1# + b)
                ≈⟨ R-refl ⟨ +-cong ⟩ -+-hom _ _ ⟩
            (1# + a) + (- 1# - b)
                ≈⟨ middle-swap _ _ _ _ ⟩
            (1# - 1#) + (a - b)
                ≈⟨ -‿inverseʳ _ ⟨ +-cong ⟩ R-refl ⟩
            0# + (a - b)
                ≈⟨ +-identityˡ _ ⟩
            a - b
        ∎ where open Eq

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
    *-isMonoid to *R-isMonoid;
    *-isCommutativeMonoid to *R-isCommutativeMonoid;
    isRing to R-isRing;
    isRingWithoutOne to R-isRingWithoutOne;
    isCommutativeRing to R-isCommutativeRing)
    hiding (-‿inverse) public
```

```
Op₁₁ : ∀ {ℓ} → Set ℓ → Set ℓ → Set ℓ
Op₁₁ A B = A → B → B

module _ {M : Set} (_≈_ : M → M → Set) where

    _DistribOverˡ_ : Op₁₁ A M → Op₂ M → Set _
    _*_ DistribOverˡ _+_ =
        ∀ x y z → (x * (y + z)) ≈ ((x * y) + (x * z))

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

    -- associative, commutative, unital algebra
    record IsAlgebra
        (_+_ _*_ : Op₂ M) (-_ : Op₁ M) (0# 1# : M)
        (_·_ : A → M → M) : Set where

        field
            isRing : IsCommutativeRing _≈_ _+_ _*_ -_ 0# 1#            
            isLeftModule : IsLeftModule _+_ -_ 0# _·_
            compatible : ∀ x y z → ((x · y) * z) ≈ (x · (y * z))

    module _ (isEquiv : IsEquivalence _≈_) where

        open import Preliminaries.Equivalence isEquiv
        open IsEquivalence isEquiv renaming (refl to M-refl)
        open Eq

        module _ where

            open IsRing
            open IsAbelianGroup
            
            ≈-ring :
                ∀ {_+_ _*_ _*′_ : Op₂ M} { -_ : Op₁ M}
                {0# 1# : M} →
                IsRing _≈_ _+_ _*_ -_ 0# 1#  →
                (∀ x y → (x * y) ≈ (x *′ y)) →
                --------------------------------------
                IsRing _≈_ _+_ _*′_ -_ 0# 1#

            ≈-ring {_+_} {_*_} {_*′_} { -_ } {0#} {1#} ring *≈*′ = record
                { +-isAbelianGroup = +-isAbelianGroup ring
                ; *-cong = *-cong′
                ; *-assoc = *-assoc′
                ; *-identity = *-identityˡ′ ,, *-identityʳ′
                ; distrib = distribˡ′ ,, distribʳ′
                } where

                *-cong′ : ∀ {x y x' y'} → x ≈ y → x' ≈ y' → (x *′ x') ≈ (y *′ y')
                *-cong′ {x} {y} {x'} {y'} x≈y x'≈y' =
                    begin
                        x *′ x'
                            ≈⟨ *≈*′ _ _ ⟨
                        x * x'
                            ≈⟨ ring .*-cong x≈y x'≈y' ⟩
                        y * y'
                            ≈⟨ *≈*′ _ _ ⟩
                        y *′ y'
                    ∎

                *-assoc′ : ∀ x y z → ((x *′ y) *′ z) ≈ (x *′ (y *′ z))
                *-assoc′ x y z =
                    begin
                        (x *′ y) *′ z
                            ≈⟨ *≈*′ _ _ ⟨
                        (x *′ y) * z
                            ≈⟨ *-cong ring (*≈*′ x y) M-refl ⟨
                        (x * y) * z
                            ≈⟨ ring .*-assoc x y z ⟩
                        x * (y * z)
                            ≈⟨ *≈*′ _ _ ⟩
                        x *′ (y * z)
                            ≈⟨ (M-refl ⟨ *-cong′ ⟩ *≈*′ _ _) ⟩
                        x *′ (y *′ z)
                    ∎

                *-identityˡ′ : ∀ x → (1# *′ x) ≈ x
                *-identityˡ′ x =
                    begin
                        1# *′ x
                            ≈⟨ *≈*′ _ _ ⟨
                        1# * x
                            ≈⟨ fst (ring .*-identity) _ ⟩
                        x
                    ∎

                *-identityʳ′ : ∀ x → (x *′ 1#) ≈ x
                *-identityʳ′ x =
                    begin
                        x *′ 1#
                            ≈⟨ *≈*′ _ _ ⟨
                        x * 1#
                            ≈⟨ snd (ring .*-identity) _ ⟩
                        x
                    ∎

                distribˡ′ : ∀ x y z → (x *′ (y + z)) ≈ ((x *′ y) + (x *′ z))
                distribˡ′ x y z =
                    begin
                        x *′ (y + z)
                            ≈⟨ *≈*′ _ _ ⟨
                        x * (y + z)
                            ≈⟨ distribˡ ring _ _ _ ⟩
                        (x * y) + (x * z)
                            ≈⟨ (*≈*′ _ _ ⟨ +-cong ring ⟩ *≈*′ _ _ ) ⟩
                        (x *′ y) + (x *′ z)
                    ∎

                distribʳ′ : ∀ x y z → ((y + z) *′ x) ≈ ((y *′ x) + (z *′ x))
                distribʳ′ x y z =
                    begin
                        (y + z) *′ x
                            ≈⟨ *≈*′ _ _ ⟨
                        (y + z) * x
                            ≈⟨ distribʳ ring _ _ _ ⟩
                        (y * x) + (z * x)
                            ≈⟨ (*≈*′ _ _ ⟨ +-cong ring ⟩ *≈*′ _ _ ) ⟩
                        (y *′ x) + (z *′ x)
                    ∎

        open IsLeftModule
        open IsAlgebra
        open IsCommutativeRing

        ≈-commring :
            ∀ {_+_ _*_ _*′_ : Op₂ M} { -_ : Op₁ M}
            {0# 1# : M} →
            IsCommutativeRing _≈_ _+_ _*_ -_ 0# 1#  →
            (∀ x y → (x * y) ≈ (x *′ y)) →
            --------------------------------------
            IsCommutativeRing _≈_ _+_ _*′_ -_ 0# 1#

        ≈-commring {_+_} {_*_} {_*′_} ring *≈*′ = record {
            isRing = ≈-ring (ring .isRing) *≈*′ ;
            *-comm = *-comm′ } where

            *-comm′ : ∀ x y → (x *′ y) ≈ (y *′ x)
            *-comm′ x y =
                begin
                    x *′ y
                        ≈⟨ *≈*′ _ _ ⟨
                    x * y
                        ≈⟨ ring .*-comm x y ⟩
                    y * x
                        ≈⟨ *≈*′ _ _ ⟩
                    y *′ x
                ∎

        ≈-algebra :
            ∀ {_+_ _*_ _*′_ : Op₂ M} { -_ : Op₁ M}
            {0# 1# : M} {_·_ : A → M → M} →
            IsAlgebra _+_ _*_ -_ 0# 1# _·_ →
            (∀ x y → (x * y) ≈ (x *′ y)) →
            --------------------------------------
            IsAlgebra _+_ _*′_ -_ 0# 1# _·_

        ≈-algebra {_+_} {_*_} {_*′_} {_·_ = _·_} alg *≈*′ = record {
            isRing = ≈-commring (alg .isRing) *≈*′ ;
            isLeftModule = alg .isLeftModule;
            compatible = compatible′ } where

            compatible′ : ∀ (x : A) (y z : M) → ((x · y) *′ z) ≈ (x · (y *′ z))
            compatible′ x y z =
                begin
                    (x · y) *′ z
                        ≈⟨ *≈*′ _ _ ⟨
                    (x · y) * z
                        ≈⟨ alg .compatible x y z ⟩
                    x · (y * z)
                        ≈⟨ alg .isLeftModule .·-cong R-refl (*≈*′ _ _) ⟩
                    x · (y *′ z)
                ∎ where open Eq
```

```
open IsEquivalence
open import Preliminaries.Equivalence isEquivalence

module EqR where
    open Eq public
```