---
title: 🚧
---

```
open import Preliminaries.Base
import Preliminaries.Algebra

module Preliminaries.PolyExpr.Integer (R : CommutativeRing)
    where

open import Algebra

open CommutativeRing R renaming
    (Carrier to CarrierR;
    0# to 0R;
    1# to 1R;
    _+_ to _+R_;
    -_ to -R_;
    _*_ to _*R_;
    _≈_ to _≈R_;
    refl to R-refl;
    sym to R-sym;
    +-cong to +R-cong;
    +-assoc to +R-assoc;
    +-identityˡ to +R-identityˡ;
    *-identityˡ to *R-identityˡ;
    zeroˡ to R-zeroˡ;
    distribˡ to R-distribˡ;
    distribʳ to R-distribʳ;
    isEquivalence to isEquivalenceR
    )

open import Preliminaries.Equivalence isEquivalenceR

open import Data.Nat.Base as ℕ
    using (ℕ; suc; zero)
    renaming (_+_ to _+ℕ_; _*_ to _*ℕ_)
    
import Data.Nat.Properties as ℕ

open import Data.Integer.Base as ℤ using (ℤ; +_)
open import Data.Integer.Properties as ℤ

open import Preliminaries.PolyExpr.Homomorphism -- ℤ.+-*-commutativeRing R
```

The integers map homomorphically to every commutative ring.

```
φℕ : ℕ → CarrierR
φℕ zero = 0R
φℕ (suc n) = 1R +R φℕ n

φℤ : ℤ → CarrierR
φℤ (+ n) = φℕ n
φℤ (ℤ.-[1+ n ]) = -R (1R +R φℕ n)

open CommutativeRing ℤ.+-*-commutativeRing

≈-hom-φℤ : ∀ {a b} → a ≡ b → φℤ a ≈R φℤ b
≈-hom-φℤ refl = R-refl

1+0≈1 : 1R +R 0R ≈R 1R
1+0≈1 = {!   !}

+-hom-φℕ : ∀ a b → φℕ (a +ℕ b) ≈R φℕ a +R φℕ b
+-hom-φℕ zero b = R-sym (+R-identityˡ _)
+-hom-φℕ (suc a) b = 
    begin
        1R +R φℕ (a +ℕ b)
            ≈⟨ +R-cong R-refl (+-hom-φℕ a b) ⟩
        1R +R (φℕ a +R φℕ b)
            ≈⟨ +R-assoc _ _ _ ⟨
        1R +R φℕ a +R φℕ b
    ∎ where open Eq

*-hom-φℕ : ∀ a b → φℕ (a *ℕ b) ≈R φℕ a *R φℕ b
*-hom-φℕ zero b = R-sym (R-zeroˡ _)
*-hom-φℕ (suc a) b =
    begin
        φℕ (b +ℕ a *ℕ b)
            ≈⟨ +-hom-φℕ b _ ⟩
        φℕ b +R φℕ (a *ℕ b)
            ≈⟨ R-refl ⟨ +R-cong ⟩ *-hom-φℕ a b ⟩
        φℕ b +R (φℕ a *R φℕ b)
            ≈⟨  *R-identityˡ _ ⟨ +R-cong ⟩ R-refl ⟨
        (1R *R φℕ b) +R (φℕ a *R φℕ b)
            ≈⟨ R-distribʳ _ _ _ ⟨
        (1R +R φℕ a) *R φℕ b
    ∎ where open Eq

+-hom-φℤ : ∀ a b → φℤ (a + b) ≈R φℤ a +R φℤ b
+-hom-φℤ (+ n) (+ m) = +-hom-φℕ n m
+-hom-φℤ (+_ n) (ℤ.-[1+_] m) = {!   !}
+-hom-φℤ (ℤ.-[1+_] n) b = {!   !}

*-hom-φℤ : ∀ a b → φℤ (a * b) ≈R φℤ a *R φℤ b
*-hom-φℤ = {!   !}

φℤ-isRingHom : IsRingHom ℤ.+-*-commutativeRing R φℤ
φℤ-isRingHom = record
  { ≈-hom = ≈-hom-φℤ
  ; 0-hom = R-refl
  ; 1-hom = 1+0≈1
  ; +-hom = +-hom-φℤ
  ; *-hom = *-hom-φℤ }
```