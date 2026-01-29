---
title: Decidability of equivalence of polynomial expressions over the integers
---

```
-- {-# OPTIONS --allow-unsolved-metas #-}

open import Preliminaries.Base
import Preliminaries.Algebra

module Preliminaries.IntegerPolynomials (R : CommutativeRing) where

open import Data.Bool.Properties using (T-≡; T-not-≡)
open import Data.Bool.Base using (not)
open import Function.Bundles using (Equivalence)
open import Relation.Nullary.Decidable.Core using (T?)

open import Data.Integer
    renaming (_*_ to _*ℤ_; _+_ to _+ℤ_; _-_ to _-ℤ_; _≟_ to _≟ℤ_)
    public

open import Data.Integer.Properties as ℤ
    hiding (<⇒≤; _≟_)
    renaming (+-comm to +ℤ-comm)
    public

Z : CommutativeRing
Z = ℤ.+-*-commutativeRing

weq : WeaklyDecidable {A = ℤ} _≡_
weq x y with x ≟ℤ y
... | yes a = just a
... | no a = nothing

open import Preliminaries.PolyExpr Z
    using ()
    renaming (PolyExpr to PolyExprZ; _≈_ to _≈Z_; var to varZ; con to conZ; _+_ to _+Z_; _*_ to _*Z_; _-_ to _-Z_)

open import Preliminaries.DecidableEquivalence Z weq
    renaming (_≟_ to _≟Z_)

open import Preliminaries.Algebra R
open import Preliminaries.Equivalence isEquivalence

open import Data.Nat.Base as ℕ
    using (ℕ; suc; zero; _∸_)
    renaming (_+_ to _+ℕ_; _*_ to _*ℕ_; _≥_ to _≥ℕ_; _<_ to _<ℕ_)
open import Data.Nat
    using ()
    renaming (_≤?_ to _≤ℕ?_; _<?_ to _<ℕ?_; _>?_ to _>ℕ?_)

open import Preliminaries.Naturals R
    renaming (+-hom-φ to +-hom-φℕ; *-hom-φ to *-hom-φℕ; φ to φℕ)

open import Preliminaries.AuxiliaryLemmas R

-- φℕ = φ
φ : ℤ → A
φ (+ n) = φℕ n
φ (-[1+ n ]) = -R φℕ (ℕ.suc n)

not<ᵇ⇒≥ : ∀ m n → T (not (m ℕ.<ᵇ n)) → m ≥ℕ n
not<ᵇ⇒≥ _ zero m<n = z≤n
not<ᵇ⇒≥ (suc m) (suc n) m<n = s≤s (not<ᵇ⇒≥ m n m<n)

-- open CommutativeRing ℤ.+-*-commutativeRing

≈-hom-φ : ∀ {a b} → a ≡ b → φ a ≈R φ b
≈-hom-φ refl = R-refl

open import Data.Nat.Properties using (<ᵇ⇒<; <⇒≤)

open Equivalence

-‿-hom-φ : ∀ m → φ (- + m) ≈R -R φ (+ m)
-‿-hom-φ zero = 0≈-0
-‿-hom-φ (ℕ.suc m) = R-refl

⊖-hom-φ-φℕ : ∀ (m n : ℕ) → φ (m ⊖ n) ≈R φℕ m -R φℕ n
⊖-hom-φ-φℕ m n with m ℕ.<ᵇ n in eq
... | true  = 
    begin
        φ (- (+ (n ∸ m))) ≈⟨ -‿-hom-φ $ n ∸ m ⟩
        -R φ (+ (n ∸ m)) ≈⟨⟩
        -R φℕ (n ∸ m) ≈⟨ -R‿cong (∸-hom-φ (<⇒≤ (<ᵇ⇒< m n (from T-≡ eq)))) ⟩
        -R (φℕ n -R φℕ m) ≈⟨ -[a-b]≈b-a _ _ ⟩
        φℕ m +R -R φℕ n
    ∎ where open Eq
... | false = ∸-hom-φ m≥n where

    have : T (not (m ℕ.<ᵇ n))
    have = from T-not-≡ eq

    m≥n : m ≥ℕ n
    m≥n = not<ᵇ⇒≥ _ _ have

+-hom-φ : ∀ a b → φ (a +ℤ b) ≈R φ a +R φ b
+-hom-φ (+ n) (+ m) = +-hom-φℕ n m
+-hom-φ (+ n) (-[1+ m ]) = ⊖-hom-φ-φℕ n (ℕ.suc m)
+-hom-φ a @ (-[1+ m ]) b @ (+ n)
    rewrite +ℤ-comm a b = 
    begin
        φ (b +ℤ a)
            ≈⟨ +-hom-φ b a ⟩
        φ b +R φ a
            ≈⟨ +R-comm _ _ ⟩
        φ a +R φ b
    ∎ where open Eq
+-hom-φ a @ (-[1+ m ]) b @ (-[1+ n ]) =
    begin
        -R (1R +R φℕ (ℕ.suc m +ℕ n))
            ≈⟨ -R‿cong (R-refl ⟨ +R-cong ⟩ +-hom-φℕ (ℕ.suc m) n) ⟩
        -R (1R +R (φℕ (ℕ.suc m) +R φℕ n))
            ≈⟨ -R‿cong (lemma₇ _ _ _) ⟩
        -R (φℕ (ℕ.suc m) +R (1R +R φℕ n))
            ≈⟨ -R‿cong (R-refl ⟨ +R-cong ⟩ φ-suc n) ⟨
        -R (φℕ (ℕ.suc m) +R φℕ (ℕ.suc n))
            ≈⟨ -+-hom _ _ ⟩
        -R φℕ (ℕ.suc m) -R φℕ (ℕ.suc n)
    ∎ where open Eq

module _ where
    open import Data.Sign.Base

    convert : Sign → A
    convert + = 1R
    convert - = -R 1R

    infix 5 _◃R_
    _◃R_ : Sign → A → A
    + ◃R a = a
    - ◃R a = -R a

    ◃R-cong : ∀ s {a b} → a ≈R b → s ◃R a ≈R s ◃R b
    ◃R-cong - a≈b = -R‿cong a≈b
    ◃R-cong + a≈b = a≈b

    sign-φ : ∀ s n → φ (s ◃ n) ≈R s ◃R φℕ n
    sign-φ + ℕ.zero = R-refl
    sign-φ + (ℕ.suc _) = R-refl
    sign-φ - ℕ.zero = 0≈-0
    sign-φ - (ℕ.suc _) = R-refl

open import Data.Sign.Base as Sign using (Sign)

*-hom-φ : ∀ a b → φ (a *ℤ b) ≈R φ a *R φ b
*-hom-φ a b = 
    begin
        φ (a *ℤ b)
            ≈⟨⟩
        φ (sign a Sign.* sign b ◃ ∣ a ∣ *ℕ ∣ b ∣)
            ≈⟨ sign-φ (sign a Sign.* sign b) (∣ a ∣ *ℕ ∣ b ∣) ⟩
        (sign a Sign.* sign b) ◃R φℕ (∣ a ∣ *ℕ ∣ b ∣)
            ≈⟨ ◃R-cong (sign a Sign.* sign b) (*-hom-φℕ (∣ a ∣) (∣ b ∣)) ⟩
        (sign a Sign.* sign b) ◃R (φℕ (∣ a ∣) *R φℕ (∣ b ∣))
            ≈⟨ lem a b ⟩
        φ a *R φ b
    ∎ where
    open Eq

    lem : ∀ a b → (sign a Sign.* sign b) ◃R (φℕ (∣ a ∣) *R φℕ (∣ b ∣)) ≈R φ a *R φ b
    lem (+_ n) (+_ m) = R-refl
    lem (+_ n) (-[1+_] m) = -[a*b]≈a*-b _ _
    lem (-[1+_] n) (+_ m) = -[a*b]≈-a*b _ _
    lem (-[1+_] n) (-[1+_] m) = a*b≈-a*-b _ _

open import Preliminaries.Homomorphism Z R

φ-isRingHom : IsRingHom φ
φ-isRingHom = record
    { ≈-hom = ≈-hom-φ
    ; 0-hom = R-refl
    ; 1-hom = R-refl
    ; +-hom = +-hom-φ
    ; *-hom = *-hom-φ }

open import Preliminaries.PolyExpr R

transfer :
    ∀ {X : Set} {p q : PolyExprZ X} →
    p ≈Z q →
    --------------------------------
    ext φ p ≈ ext φ q

transfer = hom-lemma φ-isRingHom

-- open IntegralPolyExpr

inImage :
    {X : Set} {p : PolyExpr X} →
    IntegralPolyExpr p →
    -----------------------------
    ∃ λ q → ext φ q ≡ p

inImage con0 = conZ 0ℤ ,, refl
inImage con1 = conZ 1ℤ ,, refl
inImage (var x) = varZ x ,, refl
-- inImage (neg ip)
--     with inImage ip
-- ... | q ,, refl = conZ -1ℤ *Z q ,, refl
inImage (ip₀ + ip₁)
    with inImage ip₀ | inImage ip₁
... | q₀ ,, refl | q₁ ,, refl = q₀ +Z q₁ ,, refl
inImage (ip₀ * ip₁)
    with inImage ip₀ | inImage ip₁
... | q₀ ,, refl | q₁ ,, refl = q₀ *Z q₁ ,, refl

_≟′_ :
    ∀ {n} {p q : PolyExpr (Fin n)} →
    IntegralPolyExpr p →
    IntegralPolyExpr q →
    --------------------------------
    Maybe (p ≈ q)

ip ≟′ iq
    with inImage ip | inImage iq
... | pℤ ,, refl | qℤ ,, refl
    with pℤ ≟Z qℤ
... | nothing = nothing
... | just p≈qℤ = just $ transfer p≈qℤ

infix 4 _≟_
_≟_ : ∀ {n} → WeaklyDecidable (_≈_ {Fin n})
p ≟ q
    with isIntegralPolyExpr? p | isIntegralPolyExpr? q
... | nothing | _ = nothing
... | _ | nothing = nothing
... | just ip | just iq = ip ≟′ iq
```
