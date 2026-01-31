---
title: Decidability of equivalence of polynomial expressions
---

```
{-# OPTIONS --guardedness --sized-types #-}
{-# OPTIONS --allow-unsolved-metas #-}

open import Preliminaries.Base
import Preliminaries.Algebra

module Special.DecidableEquivalence
    (R : CommutativeRing)
    (_≟R_ : let open Preliminaries.Algebra R in Decidable _≈R_)
    where

open Preliminaries.Algebra R
open import General.Terms R hiding (x)
open import Special.Polynomials R
open import Special.HNF R

open import Special.AuxiliaryLemmas R

private variable
    X Y Z : Set
    m n k : ℕ

-- Equality of normal forms is weakly decidable.

mutual
    infix 4 _≟H_ _≟N_

    _≟H_ : Decidable (_≈H_ {n = n})
    ∅ ≟H ∅ = yes ∅
    ∅ ≟H (_ *x+ _ ·x+ _) = no λ ()
    (_ *x+ _ ·x+ _) ≟H ∅ = no λ ()
    (p *x+ c ·x+ m) ≟H (q *x+ d ·x+ n)
        with p ≟H q | c ≟R d | m ≟N n
    ... | yes p≈q | yes c≈d | yes m≈n = yes (p≈q *x+ c≈d ·x+ m≈n)
    ... | _        | _        | no m≉n = no λ { (_ *x+ _ ·x+ m≈n) → m≉n m≈n }
    ... | _        | no c≉d   | _      = no λ { (_ *x+ c≈d ·x+ _) → c≉d c≈d }
    ... | no p≉q   | _        | _      = no λ { (p≈q *x+ _ ·x+ _) → p≉q p≈q }

    _≟N_ : Decidable (_≈N_ {n = n})
    zero ≟N zero = yes zero
    poly p₁ ≟N poly p₂
        with p₁ ≟H p₂
    ... | yes p₁≈p₂ = yes (poly p₁≈p₂)
    ... | no p₁≉p₂  = no λ { (poly p₁≈p₂) → p₁≉p₂ p₁≈p₂ }

-- A simplifying variant of `_*x+_·x+`.

_*x+_·x+HN_ : HNF (suc n) → A → Normal n → HNF (suc n)
∅ *x+ c ·x+HN _
    with c ≟R 0R
∅ *x+ c ·x+HN zero     | yes _ = ∅
∅ *x+ c ·x+HN (poly ∅) | yes _ = ∅
∅ *x+ c ·x+HN n | _ = ∅ *x+ c ·x+ n
p@(_ *x+ _ ·x+ _) *x+ c ·x+HN n = p *x+ c ·x+ n

-- scalar product of normal forms

infixr 10 _·H_ _·N_
mutual
    _·H_ : A → HNF (suc n) → HNF (suc n)
    c ·H _ with c ≟R 0R
    ...                  | yes _  = ∅
    _ ·H ∅               | no _ = ∅
    c ·H (p *x+ d ·x+ n) | no _ = (c ·H p) *x+ (c *R d) ·x+HN (c ·N n)

    _·N_ : A → Normal n → Normal n
    _ ·N zero = zero
    -- _ ·N (poly ∅) = poly ∅
    c ·N (poly p) = poly (c ·H p)

-- Addition of normal forms

mutual
    infixr 9 _+H_ _+N_

    _+H_ : HNF (suc n) → HNF (suc n) → HNF (suc n)
    ∅ +H p = p
    p +H ∅ = p
    (p₁ *x+ c₁ ·x+ n₁) +H (p₂ *x+ c₂ ·x+ n₂)
        -- use the simplifying variant of _*x+_·x+_
        = (p₁ +H p₂) *x+ (c₁ +R c₂) ·x+HN (n₁ +N n₂)

    _+N_ : Normal n → Normal n → Normal n
    zero +N zero = zero
    poly p₁ +N poly p₂ = poly (p₁ +H p₂)

-- A simplifying variant of `_*x+_`.

_*x+HN_ : HNF (suc n) → Normal n → HNF (suc n)
∅ *x+HN n with n ≟N 0N
... | yes _  = 0H
... | no _ = 0H *x+ 0R ·x+ n
p *x+HN n = p *x+ 0R ·x+ n

infixr 9 _+HN_
_+HN_ : HNF (suc n) → Normal n → HNF (suc n)
∅ +HN n = ∅ *x+ 0R ·x+HN n
(p *x+ c ·x+ n) +HN n′ = p *x+ c ·x+HN (n +N n′)

-- Multiplication of normal forms

mutual
    infixr 10 _*H_ _*N_ _*HN_ _*NH_

    _*NH_ : Normal n → HNF (suc n) → HNF (suc n)
    _ *NH ∅ = 0H
    n *NH (p *x+ c ·x+ n′)
        with n ≟N 0N
    ... | yes _ = 0H
    ... | _
        with c ≟R 0R
    ... | yes _ = (n *NH p) *x+HN (n *N n′)
    ... | _ = ((n *NH p) +HN (c ·N n)) *x+HN (n *N n′)

    _*HN_ : HNF (suc n) → Normal n → HNF (suc n)
    ∅ *HN _ = 0H
    (p *x+ c ·x+ n) *HN n′
        with n′ ≟N 0N
    ... | yes _ = 0H
    ... | _
        with c ≟R 0R
    ... | yes _ = (p *HN n′) *x+HN (n *N n′)
    ... | _ = ((p *HN n′) +HN (c ·N n′)) *x+HN (n *N n′)

    _*H_ : HNF (suc n) → HNF (suc n) → HNF (suc n)
    ∅ *H _ = 0H
    _ *H ∅ = 0H
    -- x^2: p₁p₂ + p₁c₂ + c₁p₂ + c₁c₂
    -- x: p₁n₂ + c₁n₂ + n₁p₂ + n₁c₂, also (p₁+c₁)n₂ + (p₂+c₂)n₁
    -- ((p₁p₂ + p₁c₂ + c₁p₂ + c₁c₂) * x + p₁n₂ + c₁n₂ + n₁p₂ + n₁c₂) * x + n₁n₂
    -- constant: n₁n₂
    (p₁ *x+ c₁ ·x+ n₁) *H (p₂ *x+ c₂ ·x+ n₂) =
        ((p₁ *H p₂ +H c₂ ·H p₁ +H c₁ ·H p₂) *x+ c₁ *R c₂ ·x+HN (c₁ ·N n₂ +N c₂ ·N n₁) +H p₁ *HN n₂ +H n₁ *NH p₂) *x+HN (n₁ *N n₂)
        
    _*N_ : Normal n → Normal n → Normal n
    zero *N zero = zero
    poly p₁ *N poly p₂ = poly (p₁ *H p₂)

-- _*x+HN_ is equal to _*x+_.
*x+HN≈*x+ :
    (p : HNF (suc n)) (m : Normal n) →
    ----------------------------------
    ⟦ p *x+HN m ⟧H ≈ ⟦ p *x+ 0R ·x+ m ⟧H

*x+HN≈*x+ (_ *x+ _ ·x+ _) n = ≈-refl
*x+HN≈*x+ ∅ n with n ≟N 0N
... | yes n≈0 =
    begin
        0T
            ≈⟨ ≈-↑ (0≈N⟦0⟧ n≈0) ⟩
        ⟦ n ⟧N ↑
            ≈⟨ lemma₆ _ _ _ ⟨
        0T * x + 0R · x + ⟦ n ⟧N ↑
    ∎ where open EqP
... | no _ = ≈-refl

open AlgebraicProperties

∅*x+HN-hom :
    (m : Normal n) →
    ----------------------
    ⟦ ∅ *x+HN m ⟧H ≈ ⟦ m ⟧N ↑

∅*x+HN-hom n with n ≟N 0N
... | yes n≈0 = ≈-↑ (0≈N⟦0⟧ n≈0)
... | no _ = lemma₆ _ _ _

*x+·x+HN-hom :
    ∀ {k} (p : HNF (suc k)) c (n : Normal k) →
    ----------------------------------------
    ⟦ p *x+ c ·x+HN n ⟧H ≈ ⟦ p ⟧H * x + c · x + ⟦ n ⟧N ↑

*x+·x+HN-hom ∅ c _
    with c ≟R 0R
*x+·x+HN-hom ∅ c zero     | yes c≈0 = ≈-sym (lemma₁ ≈-refl c≈0 ≈-refl)
*x+·x+HN-hom ∅ c (poly ∅) | yes c≈0 = ≈-sym (lemma₁ ≈-refl c≈0 ≈-refl)
*x+·x+HN-hom ∅ c (poly (_ *x+ _ ·x+ _)) | yes _ = ≈-refl
*x+·x+HN-hom ∅ _ _        | no _ = ≈-refl
*x+·x+HN-hom (_ *x+ _ ·x+ _) c n = ≈-refl

mutual
    ·H-hom :
        ∀ c (p : HNF (suc k)) →
        -----------------------
        ⟦ c ·H p ⟧H ≈ c · ⟦ p ⟧H

    ·H-hom c p with c ≟R 0R
    ... | yes c≈0 = 
        begin
            0T
                ≈⟨ ·-zero _ ⟨
            0R · ⟦ p ⟧H
                ≈⟨ (c≈0 ⟨ ·-cong ⟩ ≈-refl) ⟨
            c · ⟦ p ⟧H
        ∎ where open EqP
    ·H-hom c ∅ | no _ = ·-zero′ c
    ·H-hom c (p *x+ d ·x+ n) | no _ =
        begin
            ⟦ (c ·H p) *x+ c *R d ·x+HN (c ·N n) ⟧H
                ≈⟨ *x+·x+HN-hom _ _ _ ⟩
            ⟦ c ·H p ⟧H * x + (c *R d) · x + ⟦ c ·N n ⟧N ↑
                ≈⟨ +-cong₃ aux (*-·-distrib _ _ _) (·N-hom↑ c n) ⟩
            c · (⟦ p ⟧H * x) + c · (d · x) + c · (⟦ n ⟧N ↑)
                ≈⟨ ·-+-distrib₃ _ _ _ _ ⟨
            c · (⟦ p ⟧H * x + d · x + ⟦ n ⟧N ↑)
        ∎ where
            open EqP

            aux : ⟦ c ·H p ⟧H * x ≈ c · ⟦ p ⟧H * x
            aux =
                begin
                    ⟦ c ·H p ⟧H * x
                        ≈⟨ ·H-hom c p ⟨ *-cong ⟩ ≈-refl ⟩
                    (c · ⟦ p ⟧H) * x
                        ≈⟨ ·-*-distrib _ _ _ ⟩
                    c · (⟦ p ⟧H * x)
                ∎

    ·N-hom :
        ∀ c (n : Normal k) →
        -----------------------
        ⟦ c ·N n ⟧N ≈ c · ⟦ n ⟧N

    ·N-hom c zero = ·-zero′ c
    ·N-hom c (poly p) = ·H-hom c p

    ·N-hom↑ :
        ∀ c (n : Normal k) →
        -----------------------
        ⟦ c ·N n ⟧N ↑ ≈ c · ⟦ n ⟧N ↑

    ·N-hom↑ c n = ≈-↑ (·N-hom c n)

mutual
    +H-hom :
        (p₁ p₂ : HNF (suc n)) →
        -------------------------------
        ⟦ p₁ +H p₂ ⟧H ≈ ⟦ p₁ ⟧H + ⟦ p₂ ⟧H

    +H-hom ∅ _ = ≈-sym (+-zeroˡ _)
    +H-hom (p *x+ c ·x+ n) ∅ = ≈-sym (+-zeroʳ _)
    +H-hom (p₁ *x+ c₁ ·x+ n₁) (p₂ *x+ c₂ ·x+ n₂) = 
        begin
            ⟦ (p₁ +H p₂) *x+ (c₁ +R c₂) ·x+HN (n₁ +N n₂) ⟧H
                ≈⟨ *x+·x+HN-hom _ _ _  ⟩
            ⟦ p₁ +H p₂ ⟧H * x + (c₁ +R c₂) · x + ⟦ n₁ +N n₂ ⟧N ↑
                ≈⟨ +-cong₃ (*x-cong (+H-hom _ _)) (+-·-distrib _ _ _) (+N-hom↑ n₁ n₂) ⟩
            (⟦ p₁ ⟧H + ⟦ p₂ ⟧H) * x + (c₁ · x + c₂ · x) + (⟦ n₁ ⟧N ↑ + ⟦ n₂ ⟧N ↑)
                ≈⟨ +-cong₃ (*-distribʳ _ _ _) ≈-refl ≈-refl ⟩
            (⟦ p₁ ⟧H * x + ⟦ p₂ ⟧H * x) + (c₁ · x + c₂ · x) + (⟦ n₁ ⟧N ↑ + ⟦ n₂ ⟧N ↑)
                ≈⟨ lemma₀ _ _ _ _ _ _ ⟩
            ⟦ p₁ *x+ c₁ ·x+ n₁ ⟧H + ⟦ p₂ *x+ c₂ ·x+ n₂ ⟧H
        ∎ where open EqP

    +N-hom :
        ∀ {n} (p₁ p₂ : Normal n) →
        -------------------------------
        ⟦ p₁ +N p₂ ⟧N ≈ ⟦ p₁ ⟧N + ⟦ p₂ ⟧N

    +N-hom zero zero  = ≈-sym (+-zeroˡ _)
    +N-hom (poly p₁) (poly p₂) = +H-hom p₁ p₂

    +N-hom↑ :
        ∀ {n} (p₁ p₂ : Normal n) →
        -------------------------------------
        ⟦ p₁ +N p₂ ⟧N ↑ ≈ ⟦ p₁ ⟧N ↑ + ⟦ p₂ ⟧N ↑

    +N-hom↑ m n = ≈-↑ (+N-hom m n)
  
    +HN-hom :
        (p : HNF (suc n)) (n : Normal n) →
        ----------------------------------
        ⟦ p +HN n ⟧H ≈ ⟦ p ⟧H + ⟦ n ⟧N ↑

    +HN-hom ∅ n =
        begin
            ⟦ ∅ *x+ 0R ·x+HN n ⟧H
                ≈⟨ *x+·x+HN-hom _ _ _ ⟩
            ⟦ ∅ ⟧H * x + 0R · x + ⟦ n ⟧N ↑
                ≈⟨ +-cong₃ (*-zeroˡ _) (·-zero _) ≈-refl ⟩
            0T + 0T + ⟦ n ⟧N ↑
                ≈⟨ +-zero₃ _ ⟩
            ⟦ n ⟧N ↑
                ≈⟨ +-zeroˡ _ ⟨
            ⟦ ∅ ⟧H + ⟦ n ⟧N ↑
        ∎ where open EqP

    +HN-hom (p *x+ c ·x+ m) n =
        begin
            ⟦ p *x+ c ·x+HN (m +N n) ⟧H
                ≈⟨ *x+·x+HN-hom _ _ _ ⟩
            ⟦ p ⟧H * x + c · x + ⟦ m +N n ⟧N ↑
                ≈⟨ +-cong₃ ≈-refl ≈-refl (+N-hom↑ m n) ⟩
            ⟦ p ⟧H * x + c · x + (⟦ m ⟧N ↑ + ⟦ n ⟧N ↑)
                ≈⟨ lemma₅ _ _ _ _ ⟩
            (⟦ p ⟧H * x + c · x + ⟦ m ⟧N ↑) + ⟦ n ⟧N ↑
                ≈⟨⟩
            ⟦ p *x+ c ·x+ m ⟧H + ⟦ n ⟧N ↑
        ∎ where open EqP

+H-hom₃ :
        (p₁ p₂ p₃ : HNF (suc n)) →
        -------------------------------
        ⟦ p₁ +H p₂ +H p₃ ⟧H ≈ ⟦ p₁ ⟧H + ⟦ p₂ ⟧H + ⟦ p₃ ⟧H

+H-hom₃ p₁ p₂ p₃ =
    begin
        ⟦ p₁ +H p₂ +H p₃ ⟧H
            ≈⟨ +H-hom _ _ ⟩
        ⟦ p₁ ⟧H + ⟦ p₂ +H p₃ ⟧H
            ≈⟨ ≈-refl ⟨ +-cong ⟩ +H-hom _ _  ⟩
        ⟦ p₁ ⟧H + ⟦ p₂ ⟧H + ⟦ p₃ ⟧H
    ∎ where open EqP

*x+HN-hom :
    ∀ (p : HNF (suc k)) (n : Normal k) →
    ----------------------------------------
    ⟦ p *x+HN n ⟧H ≈ ⟦ p ⟧H * x + ⟦ n ⟧N ↑

*x+HN-hom ∅ n with n ≟N 0N
... | yes n≈0  = ≈-sym (+-≈zeroˡʳ (*-zeroˡ _) (≈-sym (≈-↑ (0≈N⟦0⟧ n≈0))))
... | no _ = 
    begin
        0T * x + 0R · x + ⟦ n ⟧N ↑
            ≈⟨ +-≈zero₃ (*-zeroˡ _) (·-zero _) ⟩
        ⟦ n ⟧N ↑
            ≈⟨ +-≈zeroˡ (*-zeroˡ _) ⟨
        0T * x + ⟦ n ⟧N ↑
    ∎ where open EqP
*x+HN-hom p@(_ *x+ _ ·x+ _) n =
    begin
        ⟦ p *x+ 0R ·x+ n ⟧H
            ≈⟨⟩
        ⟦ p ⟧H * x + 0R · x + ⟦ n ⟧N ↑
            ≈⟨ +-≈zero₃-mid (·-zero _) ⟩
        ⟦ p ⟧H * x + ⟦ n ⟧N ↑
    ∎ where open EqP

mutual
    *NH-hom :
        (n : Normal k) (p : HNF (suc k)) →
        ----------------------------------
        ⟦ n *NH p ⟧H ≈ ⟦ n ⟧N ↑ * ⟦ p ⟧H

    *NH-hom n ∅ = ≈-sym (*-zeroʳ _)
    *NH-hom n (p *x+ c ·x+ m)
        with n ≟N 0N
    ... | yes n≈0 = 
        begin
            0T
                ≈⟨ *-zeroˡ _ ⟨
            0T * (⟦ p ⟧H * x + c · x + ⟦ m ⟧N ↑)
                ≈⟨ *x-cong (≈-↑ (⟦0⟧≈N0 n≈0)) ⟨
            ⟦ n ⟧N ↑ * (⟦ p ⟧H * x + c · x + ⟦ m ⟧N ↑)
        ∎ where open EqP

    ... | no _
        with c ≟R 0R
    ... | yes c≈0 = 
        begin
            ⟦ (n *NH p) *x+HN (n *N m) ⟧H
                ≈⟨ *x+HN-hom _ _ ⟩
            ⟦ n *NH p ⟧H * x + ⟦ n *N m ⟧N ↑
                ≈⟨ *x+-cong (*NH-hom n p) (*N-hom↑ n m) ⟩
            (⟦ n ⟧N ↑ * ⟦ p ⟧H) * x + (⟦ n ⟧N * ⟦ m ⟧N) ↑
                ≈⟨ lemma₂ _ _ _ _ ⟩
            ⟦ n ⟧N ↑ * (⟦ p ⟧H * x + ⟦ m ⟧N ↑)
                ≈⟨ x*-cong (x+-cong (·+-≈zeroˡ c≈0)) ⟨
            ⟦ n ⟧N ↑ * (⟦ p ⟧H * x + c · x + ⟦ m ⟧N ↑)
        ∎ where open EqP
        
    ... | no _ =
        begin
            ⟦ ((n *NH p) +HN (c ·N n)) *x+HN (n *N m) ⟧H
                ≈⟨ *x+HN-hom _ _ ⟩
            ⟦ (n *NH p) +HN (c ·N n) ⟧H * x + ⟦ n *N m ⟧N ↑
                ≈⟨ *x+-cong (+HN-hom _ _) ≈-refl ⟩
            (⟦ n *NH p ⟧H + ⟦ c ·N n ⟧N ↑) * x + ⟦ n *N m ⟧N ↑
                ≈⟨ *x+-cong (*NH-hom n p ⟨ +-cong ⟩ ·N-hom↑ c n) (*N-hom↑ n m) ⟩
            (⟦ n ⟧N ↑ * ⟦ p ⟧H + c · ⟦ n ⟧N ↑) * x + ⟦ n ⟧N ↑ * ⟦ m ⟧N ↑
                ≈⟨ lemma₃ _ _ _ _ _ ⟩
            ⟦ n ⟧N ↑ * (⟦ p ⟧H * x + c · x + ⟦ m ⟧N ↑)
        ∎ where open EqP

    *HN-hom :
        (p : HNF (suc k)) (n : Normal k) →
        ----------------------------------
        ⟦ p *HN n ⟧H ≈ ⟦ p ⟧H * ⟦ n ⟧N ↑

    *HN-hom ∅ n = ≈-sym (*-zeroˡ _)
    *HN-hom (p *x+ c ·x+ m) n
        with n ≟N 0N
    ... | yes n≈0 =
        begin
            0T
                ≈⟨ *-zeroʳ _ ⟨
            (⟦ p ⟧H * x + c · x + ⟦ m ⟧N ↑) * 0T
                ≈⟨ x*-cong (≈-↑ (⟦0⟧≈N0 n≈0)) ⟨
            (⟦ p ⟧H * x + c · x + ⟦ m ⟧N ↑) * ⟦ n ⟧N ↑
        ∎ where open EqP
        
    ... | no _
        with c ≟R 0R
    ... | yes c≈0 =
        begin
            ⟦ (p *HN n) *x+HN (m *N n) ⟧H
                ≈⟨ *x+HN-hom _ _ ⟩
            ⟦ p *HN n ⟧H * x + ⟦ m *N n ⟧N ↑
                ≈⟨ *x+-cong (*HN-hom _ _) (*N-hom↑ m n) ⟩
            (⟦ p ⟧H * ⟦ n ⟧N ↑) * x + ⟦ m ⟧N ↑ * ⟦ n ⟧N ↑
                ≈⟨ lemma₄ _ _ _ _ ⟩
            (⟦ p ⟧H * x + ⟦ m ⟧N ↑) * ⟦ n ⟧N ↑
                ≈⟨ *x-cong (x+-cong (·+-≈zeroˡ c≈0)) ⟨
            (⟦ p ⟧H * x + c · x + ⟦ m ⟧N ↑) * ⟦ n ⟧N ↑
        ∎ where open EqP
        
    ... | no _ =
        begin
            ⟦ ((p *HN n) +HN (c ·N n)) *x+HN (m *N n) ⟧H
                ≈⟨ *x+HN-hom _ _ ⟩
            ⟦ (p *HN n) +HN (c ·N n) ⟧H * x + ⟦ m *N n ⟧N ↑
                ≈⟨ *x+-cong (+HN-hom _ _) (*N-hom↑ m n) ⟩
            (⟦ p *HN n ⟧H + ⟦ c ·N n ⟧N ↑) * x + ⟦ m ⟧N ↑ * ⟦ n ⟧N ↑
                ≈⟨ *x+-cong (*HN-hom _ _ ⟨ +-cong ⟩ ·N-hom↑ c n) ≈-refl ⟩
            (⟦ p ⟧H * ⟦ n ⟧N ↑ + c · ⟦ n ⟧N ↑) * x + ⟦ m ⟧N ↑ * ⟦ n ⟧N ↑
                ≈⟨ lemma₃′ _ _ _ _ _ ⟩
            (⟦ p ⟧H * x + c · x + ⟦ m ⟧N ↑) * ⟦ n ⟧N ↑
        ∎ where open EqP

    *H-hom :
        (p₁ p₂ : HNF (suc k)) →
        -------------------------------
        ⟦ p₁ *H p₂ ⟧H ≈ ⟦ p₁ ⟧H * ⟦ p₂ ⟧H

    -- this is the longest proof
    *H-hom ∅ _ = ≈-sym (*-zeroˡ _)
    *H-hom (_ *x+ _ ·x+ _) ∅ = ≈-sym (*-zeroʳ _)
    *H-hom (p₁ *x+ c₁ ·x+ n₁) (p₂ *x+ c₂ ·x+ n₂) =
        begin
            ⟦ (p₁ *x+ c₁ ·x+ n₁) *H (p₂ *x+ c₂ ·x+ n₂) ⟧H
                ≈⟨⟩
            ⟦ ((p₁ *H p₂ +H c₂ ·H p₁ +H c₁ ·H p₂) *x+ c₁ *R c₂ ·x+HN (c₁ ·N n₂ +N c₂ ·N n₁) +H p₁ *HN n₂ +H n₁ *NH p₂) *x+HN (n₁ *N n₂) ⟧H
                ≈⟨ *x+HN-hom _ _ ⟩
            ⟦ (p₁ *H p₂ +H c₂ ·H p₁ +H c₁ ·H p₂) *x+ c₁ *R c₂ ·x+HN (c₁ ·N n₂ +N c₂ ·N n₁) +H p₁ *HN n₂ +H n₁ *NH p₂ ⟧H * x + ⟦ n₁ *N n₂ ⟧N ↑
                ≈⟨ *x+-cong (+H-hom₃ _ _ _) (*N-hom↑ n₁ n₂) ⟩
            (⟦ (p₁ *H p₂ +H c₂ ·H p₁ +H c₁ ·H p₂) *x+ c₁ *R c₂ ·x+HN (c₁ ·N n₂ +N c₂ ·N n₁) ⟧H + ⟦ p₁ *HN n₂ ⟧H + ⟦ n₁ *NH p₂ ⟧H) * x + m₁ * m₂
                ≈⟨ *x+-cong (+-cong₃ (*x+·x+HN-hom _ _ _) (*HN-hom _ _) (*NH-hom _ _)) ≈-refl ⟩
            ((⟦ p₁ *H p₂ +H c₂ ·H p₁ +H c₁ ·H p₂ ⟧H * x + (c₁ *R c₂) · x + ⟦ c₁ ·N n₂ +N c₂ ·N n₁ ⟧N ↑) + q₁ * m₂ + m₁ * q₂) * x + m₁ * m₂
                ≈⟨ *x+-cong (+-cong₃ (+-cong₃ (*x-cong (+H-hom₃ _ _ _)) ≈-refl (+N-hom↑ (c₁ ·N n₂) _)) ≈-refl ≈-refl) ≈-refl ⟩
            (((⟦ p₁ *H p₂ ⟧H + ⟦ c₂ ·H p₁ ⟧H + ⟦ c₁ ·H p₂ ⟧H) * x + (c₁ *R c₂) · x + (⟦ c₁ ·N n₂ ⟧N ↑ + ⟦ c₂ ·N n₁ ⟧N ↑)) + q₁ * m₂ + m₁ * q₂) * x + m₁ * m₂
                ≈⟨ *x+-cong (+-cong₃ (+-cong₃ (*x-cong (+-cong₃ (*H-hom _ _) (·H-hom _ _) (·H-hom _ _))) ≈-refl (+-cong (·N-hom↑ _ n₂) (·N-hom↑ _ n₁))) ≈-refl ≈-refl) ≈-refl ⟩
            (((q₁ * q₂ + c₂ · q₁ + c₁ · q₂) * x + (c₁ *R c₂) · x + c₁ · m₂ + c₂ · m₁) + q₁ * m₂ + m₁ * q₂) * x + m₁ * m₂
                ≈⟨ lemma₇ _ _ _ _ _ _ _ ⟩
            (q₁ * x + c₁ · x + m₁) * (q₂ * x + c₂ · x + m₂)
               ≈⟨⟩
            ⟦ p₁ *x+ c₁ ·x+ n₁ ⟧H * ⟦ p₂ *x+ c₂ ·x+ n₂ ⟧H
        ∎ where
            open EqP
            q₁ = ⟦ p₁ ⟧H
            q₂ = ⟦ p₂ ⟧H
            m₁ = ⟦ n₁ ⟧N ↑
            m₂ = ⟦ n₂ ⟧N ↑

    *N-hom :
        (p₁ p₂ : Normal k) →
        -------------------------------
        ⟦ p₁ *N p₂ ⟧N ≈ ⟦ p₁ ⟧N * ⟦ p₂ ⟧N

    *N-hom zero zero = ≈-sym (*-zeroˡ _)
    *N-hom (poly p₁) (poly p₂) = *H-hom p₁ p₂

    *N-hom↑ :
        (p₁ p₂ : Normal k) →
        -------------------------------------
        ⟦ p₁ *N p₂ ⟧N ↑ ≈ ⟦ p₁ ⟧N ↑ * ⟦ p₂ ⟧N ↑

    *N-hom↑ m n = ≈-↑ (*N-hom m n)
```

Conversion to normal forms

```
normalise-var : Fin k → Normal k
normalise-var zero = poly (∅ *x+ 1R ·x+ 0N)
normalise-var (suc x) = poly (∅ *x+ 0R ·x+ normalise-var x)

normalise : Term′ k → Normal k
normalise 0T = 0N
normalise (var x) = normalise-var x
normalise (c · t) = c ·N normalise t
normalise (t₁ + t₂) = normalise t₁ +N normalise t₂
normalise (t₁ * t₂) = normalise t₁ *N normalise t₂

⟦_⟧↓ : Term′ k → Term′ k
⟦ t ⟧↓ = ⟦ normalise t ⟧N

normalise-var-zero : ∀ (x : Fin k) → ¬ (normalise-var x ≈N 0N)
normalise-var-zero zero (poly ())
normalise-var-zero (suc x) (poly eq) with normalise-var x ≟N 0N
... | yes x≈0 = normalise-var-zero x x≈0
normalise-var-zero (suc x) (poly ()) | no _

sound-var : ∀ x → ⟦ normalise-var {n} x ⟧N ≈ var x
sound-var zero =
    begin
        0T * x + 1R · x + ⟦ 0N ⟧N ↑
            ≈⟨ +-≈zero₃ˡʳ (*-zeroˡ _) 0N-hom↑ ⟩
        1R · x
            ≈⟨ ·-one _ ⟩
        x
    ∎ where open EqP

sound-var (suc y)
    with normalise-var y ≟N 0N in eq
... | yes x≈0 = ⊥-elim (normalise-var-zero _ x≈0)
... | no _ =
    begin
        0T * x + 0R · x + (⟦ normalise-var y ⟧N ↑)
            ≈⟨ +-cong₃ (*-zeroˡ _) (·-zero _) (≈-↑ (sound-var y)) ⟩
        0T + 0T + var y ↑
            ≈⟨ +-zero₃ _ ⟩
        var (suc y)
    ∎ where open EqP

soundN : (p : Term′ k) → ⟦ normalise p ⟧N ≈ p
soundN 0T = 0N-hom
soundN (var x) = sound-var x
soundN (c · p) =
    begin
        ⟦ c ·N normalise p ⟧N
            ≈⟨ ·N-hom _ (normalise p) ⟩
        c · ⟦ normalise p ⟧N
            ≈⟨ ·-cong R-refl (soundN p) ⟩
        c · p
    ∎ where open EqP
soundN (p + q) = 
    begin
        ⟦ normalise p +N normalise q ⟧N
            ≈⟨ +N-hom (normalise p) (normalise q) ⟩
        ⟦ normalise p ⟧N + ⟦ normalise q ⟧N
            ≈⟨ soundN p ⟨ +-cong ⟩ soundN q ⟩
        p + q
    ∎ where open EqP
soundN (p * q) =
    begin
        ⟦ normalise p *N normalise q ⟧N
            ≈⟨ *N-hom (normalise p) (normalise q) ⟩
        ⟦ normalise p ⟧N * ⟦ normalise q ⟧N
            ≈⟨ soundN p ⟨ *-cong ⟩ soundN q ⟩
    p * q
    ∎ where open EqP

sound :
    {p q : Term′ k} →
    normalise p ≈N normalise q →
    ----------------------------
    p ≈ q

sound {p = p} {q} eq =
    begin
        p ≈⟨ soundN p ⟨
        ⟦ normalise p ⟧N ≈⟨ reflectN eq ⟩
        ⟦ normalise q ⟧N ≈⟨ soundN q ⟩
        q
    ∎ where open EqP

infix 4 _≟_
_≟_ : ∀ {k} → WeaklyDecidable (_≈_ {Fin k})
p ≟ q with normalise p ≟N normalise q
... | yes eq = just (sound eq)
... | no _ = nothing
```
