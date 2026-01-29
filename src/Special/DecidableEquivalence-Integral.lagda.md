---
title: Completeness of equivalence algorithm
---

```
{-# OPTIONS --guardedness --sized-types #-}
{-# OPTIONS --allow-unsolved-metas #-}

open import Preliminaries.Base
import Preliminaries.Algebra

module Special.DecidableEquivalence-Integral
    (R : CommutativeRing)
    -- (_≟R_ : let open Preliminaries.Algebra R in WeaklyDecidable _≈R_)
    where

-- module _ where

--     open Preliminaries.Algebra ringℤ
--     open import General.Terms ringℤ
--     open import Special.Polynomials ringℤ

--     Termℤ = Term
--     _≈ℤ_ = _≈_


open Preliminaries.Algebra R
open import General.Terms hiding (x) renaming (_-_ to _[-]_)

Termℤ = Term ringℤ
TermR = Term R

open import Special.Polynomials

_≈ℤ_ = (_≈_) ringℤ
_≈TR_ = (_≈_) R

open import Special.HNF R

open import Special.AuxiliaryLemmas R
-- open import Special.DecidableEquivalence R _≟R_

private variable
    X Y Z : Set
    m n k : ℕ

```

```
data Integral {X : Set} : TermR X → Set where
    0T : Integral 0T
    var : ∀ x → Integral (var x)
    -- _1·_ : ∀ {c p} → c ≈R 1R → Integral p → Integral (c · p)
    -- _-1·_ : ∀ {c p} → c ≈R (-R 1R) → Integral p → Integral (c · p)
    _+_ : ∀ {p q} → Integral p → Integral q → Integral (p + q)
    _*_ : ∀ {p q} → Integral p → Integral q → Integral (p * q)

isIntegral? : WeaklyDecidable₁ (Integral {X})

isIntegral? 0T = just 0T

isIntegral? (var x) = just $ var x

isIntegral? (c · p) = nothing
--     with isIntegral? p
-- ... | nothing = nothing
-- ... | just p'
--     with c ≟R 1R
-- ... | just c≈1 = just $ c≈1 1· p'
-- ... | nothing
--     with c ≟R (-R 1R)
-- ... | just c≈-1 = just $ c≈-1 -1· p'
-- ... | nothing = nothing

isIntegral? (p + q)
    with isIntegral? p | isIntegral? q
... | just p' | just q' = just $ p' + q'
... | _ | _ = nothing

isIntegral? (p * q)
    with isIntegral? p | isIntegral? q
... | just p' | just q' = just $ p' * q'
... | _ | _ = nothing

int→ℤ : ∀ {p : TermR X} → Integral p → Termℤ X
int→ℤ 0T = 0T
int→ℤ (var x) = var x
int→ℤ (ip + iq) = int→ℤ ip + int→ℤ iq
int→ℤ (ip * iq) = int→ℤ ip * int→ℤ iq

-- a term over the integers interprets to a term over any ring
ℤ→term : Termℤ X → TermR X
ℤ→term 0T = 0T
ℤ→term (var x) = var x
ℤ→term (c · p) = {!   !} · ℤ→term p
ℤ→term (p + q) = ℤ→term p + ℤ→term q
ℤ→term (p * q) = ℤ→term p * ℤ→term q

-- ℤ→int : ∀ (p : Termℤ X) → Integral (ℤ→term p)
-- ℤ→int = {!   !}

ℤ→term-≈ :
    ∀ {p q : Termℤ X} →
    p ≈ℤ q →
    ---------------------
    ℤ→term p ≈TR ℤ→term q

ℤ→term-≈ ≈-refl = ≈-refl
ℤ→term-≈ (≈-sym p≈q) = ≈-sym (ℤ→term-≈ p≈q)
ℤ→term-≈ (≈-trans p≈q q≈r) = ≈-trans (ℤ→term-≈ p≈q) (ℤ→term-≈ q≈r)
ℤ→term-≈ (·-cong c≈d p≈q) = {!   !} ⟨ ·-cong ⟩ ℤ→term-≈ p≈q
ℤ→term-≈ (·-one p) = {! ·-one _ !}
ℤ→term-≈ (·-+-distrib c p q) = ·-+-distrib _ _ _
ℤ→term-≈ (+-·-distrib p c d) = +-·-distrib _ _ _
ℤ→term-≈ (·-*-distrib c p q) = ·-*-distrib _ _ _
ℤ→term-≈ (*-·-distrib c d p) = *-·-distrib _ _ _
ℤ→term-≈ (+-cong p≈q r≈s) = ℤ→term-≈ p≈q ⟨ +-cong ⟩ ℤ→term-≈ r≈s
ℤ→term-≈ (+-zeroʳ _) = {!   !}
ℤ→term-≈ (+-assoc _ _ _) = +-assoc _ _ _
ℤ→term-≈ (+-comm _ _) = +-comm _ _
ℤ→term-≈ (+-invʳ p) = {!   !}
ℤ→term-≈ (*-cong p≈q r≈s) = ℤ→term-≈ p≈q ⟨ *-cong ⟩ ℤ→term-≈ r≈s
ℤ→term-≈ (*-assoc _ _ _) = *-assoc _ _ _
ℤ→term-≈ (*-comm _ _) = *-comm _ _
ℤ→term-≈ (*-distribʳ _ _ _) = *-distribʳ _ _ _

int→ℤ-≈ :
    ∀ {p : TermR X}
    (ip : Integral p) →
    ---------------------
    p ≈TR ℤ→term (int→ℤ ip)

int→ℤ-≈ 0T = ≈-refl
int→ℤ-≈ (var x) = ≈-refl
int→ℤ-≈ (ip + iq) = int→ℤ-≈ ip ⟨ +-cong ⟩ int→ℤ-≈ iq
int→ℤ-≈ (ip * iq) = int→ℤ-≈ ip ⟨ *-cong ⟩ int→ℤ-≈ iq

transfer :
    ∀ {p q : Term′ R n}
    (ip : Integral p) (iq : Integral q) →
    int→ℤ ip ≈ℤ int→ℤ iq →
    -------------------------------------
    p ≈TR q

transfer {p = p} {q} ip iq ip≈iq =
    begin
        p
            ≈⟨ int→ℤ-≈ _ ⟩
        ℤ→term (int→ℤ ip)
            ≈⟨ ℤ→term-≈ ip≈iq ⟩
        ℤ→term (int→ℤ iq)
            ≈⟨ int→ℤ-≈ _ ⟨
        q
    ∎ where open EqP R
```
