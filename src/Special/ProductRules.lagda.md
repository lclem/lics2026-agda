---
title: "Special product rules"
---

```
{-# OPTIONS --guardedness --sized-types #-}
-- {-# OPTIONS --allow-unsolved-metas #-}

open import Preliminaries.Base
module Special.ProductRules (R : CommutativeRing) where

open import Preliminaries.Algebra R
open import Preliminaries.PolyExpr R using (con)
open import General.Terms R
open import General.ProductRules R
open import Special.Polynomials R

open AlgebraicProperties
```

These are the axioms satisfied by special product rules.

```
record Special (P : ProductRule) : Set where

    field

        P-add :
            [ P ]⟨ x + y , x′ + y′ , z , z′ ⟩ ≈₆
            [ P ]⟨ x , x′ , z , z′ ⟩ + [ P ]⟨ y , y′ , z , z′ ⟩
        
        P-assoc :
            [ P ]⟨ x * y , [ P ]⟨ x , x′ , y , y′ ⟩ ,  z , z′ ⟩ ≈₆
            [ P ]⟨ x , x′ , y * z , [ P ]⟨ y , y′ , z , z′ ⟩ ⟩

        P-comm :
            [ P ]⟨ x , x′ , y , y′ ⟩ ≈₄
            [ P ]⟨ y , y′ , x , x′ ⟩


        -- P-compat :
        --     [ P ]⟨ z * x , z * x′ , y , y′ ⟩ ≈₅
        --     z * [ P ]⟨ x , x′ , y , y′ ⟩

        P-compat : ∀ c →
            [ P ]⟨ c · x , c · x′ , y , y′ ⟩ ≈₄
            c · [ P ]⟨ x , x′ , y , y′ ⟩

    -- P-compat′ c = ?
        -- begin
        --     [ P ]⟨ c · x , c · x′ , y , y′ ⟩
        --         ≈⟨ subst-inv′ᵥ P (·-one-* _ _ ∷-≈ ·-one-* _ _ ∷-≈ ≈-refl ∷-≈ ≈-refl ∷-≈ []-≈) ⟨
        --     [ P ]⟨ (c · 1T) * x , (c · 1T) * x′ , y , y′ ⟩
        --         ≡⟨ substᵥ-substᵥ P (_ ∷ _ ∷ _ ∷ _ ∷ []) (_ ∷ _ ∷ _ ∷ _ ∷ _ ∷ []) ⟨
        --     [ [ P ]⟨ z * x , z * x′ , y , y′ ⟩ ]⟨ x , x′ , y , y′ , c · 1T ⟩
        --         ≈⟨ subst-invᵥ (_ ∷ _ ∷ _ ∷ _ ∷ _ ∷ []) P-compat ⟩
        --     [ z * [ P ]⟨ x , x′ , y , y′ ⟩ ]⟨ x , x′ , y , y′ , c · 1T ⟩ 
        --         ≈⟨⟩
        --     (c · 1T) * [ [ P ]⟨ x , x′ , y , y′ ⟩ ]⟨ x , x′ , y , y′ , c · 1T ⟩ 
        --         ≡⟨ cong ((c · 1T) *_) (substᵥ-substᵥ P (_ ∷ _ ∷ _ ∷ _ ∷ []) (_ ∷ _ ∷ _ ∷ _ ∷ _ ∷ [])) ⟩
        --     (c · 1T) * [ P ]⟨ x , x′ , y , y′ ⟩
        --         ≈⟨ ·-one-* _ _ ⟩
        --     c · [ P ]⟨ x , x′ , y , y′ ⟩
        -- ∎ where open EqP

open Special public

-- need ≟₆ to decide the following
-- module ZeroSpecial where

--     open ProductRule ruleZero

--     P-assoc-special :
--         ∃ λ proof → 
--         ([ P ]⟨ x * y , [ P ]⟨ x , x′ , y , y′ ⟩ , z , z′ ⟩ ≟₆
--         [ P ]⟨ x , x′ , y * z , [ P ]⟨ y , y′ , z , z′ ⟩ ⟩) ≡ just proof
--     P-assoc-special = _ ,, refl

--     P-comm-special :
--         ∃ λ proof → 
--         ([ P ]⟨ x , x′ , y , y′ ⟩ ≟₄
--         [ P ]⟨ y , y′ , x , x′ ⟩) ≡ just proof
--     P-comm-special = _ ,, refl
    
--     P-add-special :
--         ∃ λ proof → 
--         ([ P ]⟨ x + y , x′ + y′ , z , z′ ⟩ ≟₆
--         [ P ]⟨ x , x′ , z , z′ ⟩ + [ P ]⟨ y , y′ , z , z′ ⟩) ≡ just proof
--     P-add-special = _ ,, refl

--     P-compat-special :
--         ∃ λ proof → 
--         ([ P ]⟨ z * x , z * x′ , y , y′ ⟩ ≟₅
--         z * [ P ]⟨ x , x′ , y , y′ ⟩) ≡ just proof
--     P-compat-special = _ ,, refl

-- module ConstNotSpecial where

--     open ProductRule ruleConst

--     P-assoc-special :
--         ∃ λ proof → 
--         ([ P ]⟨ x * y , [ P ]⟨ x , x′ , y , y′ ⟩ , z , z′ ⟩ ≟₆
--         [ P ]⟨ x , x′ , y * z , [ P ]⟨ y , y′ , z , z′ ⟩ ⟩) ≡ just proof
--     P-assoc-special = _ ,, refl

--     P-comm-special :
--         ∃ λ proof → 
--         ([ P ]⟨ x , x′ , y , y′ ⟩ ≟₄
--         [ P ]⟨ y , y′ , x , x′ ⟩) ≡ just proof
--     P-comm-special = _ ,, refl
    
--     P-add-special :
--         ∃ λ proof → 
--         ([ P ]⟨ x + y , x′ + y′ , z , z′ ⟩ ≟₆
--         [ P ]⟨ x , x′ , z , z′ ⟩ + [ P ]⟨ y , y′ , z , z′ ⟩) ≡ just proof
--     P-add-special = _ ,, refl

--     P-compat-special :
--         ∃ λ proof → 
--         ([ P ]⟨ z * x , z * x′ , y , y′ ⟩ ≟₅
--         z * [ P ]⟨ x , x′ , y , y′ ⟩) ≡ just proof
--     P-compat-special = _ ,, refl

-- module HadamardSpecial where

--     open ProductRule ruleHadamard

--     P-assoc-special :
--         ∃ λ proof → 
--         ([ P ]⟨ x * y , [ P ]⟨ x , x′ , y , y′ ⟩ , z , z′ ⟩ ≟₆
--         [ P ]⟨ x , x′ , y * z , [ P ]⟨ y , y′ , z , z′ ⟩ ⟩) ≡ just proof
--     P-assoc-special = _ ,, refl

--     P-comm-special :
--         ∃ λ proof → 
--         ([ P ]⟨ x , x′ , y , y′ ⟩ ≟₄
--         [ P ]⟨ y , y′ , x , x′ ⟩) ≡ just proof
--     P-comm-special = _ ,, refl
    
--     P-add-special :
--         ∃ λ proof → 
--         ([ P ]⟨ x + y , x′ + y′ , z , z′ ⟩ ≟₆
--         [ P ]⟨ x , x′ , z , z′ ⟩ + [ P ]⟨ y , y′ , z , z′ ⟩) ≡ just proof
--     P-add-special = _ ,, refl

--     P-compat-special :
--         ∃ λ proof → 
--         ([ P ]⟨ z * x , z * x′ , y , y′ ⟩ ≟₅
--         z * [ P ]⟨ x , x′ , y , y′ ⟩) ≡ just proof
--     P-compat-special = _ ,, refl

--     special : Special ruleHadamard
--     special = record
--         { P-oneʳ = fst P-one-special
--         ; P-assoc = fst P-assoc-special
--         ; P-comm = fst P-comm-special
--         ; P-add = fst P-add-special
--         ; P-compat = fst P-compat-special
--         }

-- module ShuffleSpecial where

--     open ProductRule ruleShuffle


--     P-assoc-special :
--         ∃ λ proof → 
--         ([ P ]⟨ x * y , [ P ]⟨ x , x′ , y , y′ ⟩ , z , z′ ⟩ ≟₆
--         [ P ]⟨ x , x′ , y * z , [ P ]⟨ y , y′ , z , z′ ⟩ ⟩) ≡ just proof
--     P-assoc-special = _ ,, refl

--     P-comm-special :
--         ∃ λ proof → 
--         ([ P ]⟨ x , x′ , y , y′ ⟩ ≟₄
--         [ P ]⟨ y , y′ , x , x′ ⟩) ≡ just proof
--     P-comm-special = _ ,, refl
    
--     P-add-special :
--         ∃ λ proof → 
--         ([ P ]⟨ x + y , x′ + y′ , z , z′ ⟩ ≟₆
--         [ P ]⟨ x , x′ , z , z′ ⟩ + [ P ]⟨ y , y′ , z , z′ ⟩) ≡ just proof
--     P-add-special = _ ,, refl

--     P-compat-special :
--         ∃ λ proof → 
--         ([ P ]⟨ z * x , z * x′ , y , y′ ⟩ ≟₅
--         z * [ P ]⟨ x , x′ , y , y′ ⟩) ≡ just proof
--     P-compat-special = _ ,, refl

--     special : Special ruleShuffle
--     special = record
--         { P-oneʳ = fst P-one-special
--         ; P-assoc = fst P-assoc-special
--         ; P-comm = fst P-comm-special
--         ; P-add = fst P-add-special
--         ; P-compat = fst P-compat-special
--         }

-- module InfiltrationSpecial where

--     open ProductRule ruleInfiltration

--     P-assoc-special :
--         ∃ λ proof → 
--         ([ P ]⟨ x * y , [ P ]⟨ x , x′ , y , y′ ⟩ , z , z′ ⟩ ≟₆
--         [ P ]⟨ x , x′ , y * z , [ P ]⟨ y , y′ , z , z′ ⟩ ⟩) ≡ just proof
--     P-assoc-special = _ ,, refl

--     P-comm-special :
--         ∃ λ proof → 
--         ([ P ]⟨ x , x′ , y , y′ ⟩ ≟₄
--         [ P ]⟨ y , y′ , x , x′ ⟩) ≡ just proof
--     P-comm-special = _ ,, refl
    
--     P-add-special :
--         ∃ λ proof → 
--         ([ P ]⟨ x + y , x′ + y′ , z , z′ ⟩ ≟₆
--         [ P ]⟨ x , x′ , z , z′ ⟩ + [ P ]⟨ y , y′ , z , z′ ⟩) ≡ just proof
--     P-add-special = _ ,, refl

--     P-compat-special :
--         ∃ λ proof → 
--         ([ P ]⟨ z * x , z * x′ , y , y′ ⟩ ≟₅
--         z * [ P ]⟨ x , x′ , y , y′ ⟩) ≡ just proof
--     P-compat-special = _ ,, refl

--     special : Special ruleInfiltration
--     special = record
--         { P-oneʳ = fst P-one-special
--         ; P-assoc = fst P-assoc-special
--         ; P-comm = fst P-comm-special
--         ; P-add = fst P-add-special
--         ; P-compat = fst P-compat-special
--         }

-- module AntiInfiltrationSpecial where

--     ruleAntiInfiltration : ProductRule
--     ruleAntiInfiltration =
--         record {
--             U = 0T;
--             P = x′ * y + (x + (1T + 1T + 1T) * x′) * y′
--         }

--     open ProductRule ruleAntiInfiltration

--     P-one-special :
--         ∃ λ proof → 
--         ([ P ]⟨ x , x′ , 1T , [ U ]⟨ 1T ⟩ ⟩ ≟₄ x′) ≡ just proof
--     P-one-special = _ ,, refl

--     P-assoc-special :
--         ∃ λ proof → 
--         ([ P ]⟨ x * y , [ P ]⟨ x , x′ , y , y′ ⟩ , z , z′ ⟩ ≟₆
--         [ P ]⟨ x , x′ , y * z , [ P ]⟨ y , y′ , z , z′ ⟩ ⟩) ≡ just proof
--     P-assoc-special = _ ,, refl

--     P-comm-special :
--         ∃ λ proof → 
--         ([ P ]⟨ x , x′ , y , y′ ⟩ ≟₄
--         [ P ]⟨ y , y′ , x , x′ ⟩) ≡ just proof
--     P-comm-special = _ ,, refl
    
--     P-add-special :
--         ∃ λ proof → 
--         ([ P ]⟨ x + y , x′ + y′ , z , z′ ⟩ ≟₆
--         [ P ]⟨ x , x′ , z , z′ ⟩ + [ P ]⟨ y , y′ , z , z′ ⟩) ≡ just proof
--     P-add-special = _ ,, refl

--     P-compat-special :
--         ∃ λ proof → 
--         ([ P ]⟨ z * x , z * x′ , y , y′ ⟩ ≟₅
--         z * [ P ]⟨ x , x′ , y , y′ ⟩) ≡ just proof
--     P-compat-special = _ ,, refl

--     special : Special ruleAntiInfiltration
--     special = record
--         { P-oneʳ = fst P-one-special
--         ; P-assoc = fst P-assoc-special
--         ; P-comm = fst P-comm-special
--         ; P-add = fst P-add-special
--         ; P-compat = fst P-compat-special
--         }

-- module GeneralisedInfiltrationSpecial where

--     P : Term′ 5
--     P = x′ * y + (x + z * x′) * y′

--     P-one-special :
--         ∃ λ proof → 
--         ([ P ]⟨ x , x′ , 1T , [ U ]⟨ 1T ⟩ , z ⟩ ≟₅ x′) ≡ just proof
--     P-one-special = _ ,, refl

--     P-assoc-special :
--         ∃ λ proof → 
--         ([ P ]⟨ x * y , [ P ]⟨ x , x′ , y , y′ , t ⟩ , z , z′ , t ⟩ ≟₇
--         [ P ]⟨ x , x′ , y * z , [ P ]⟨ y , y′ , z , z′ , t ⟩ , t ⟩) ≡ just proof
--     P-assoc-special = _ ,, refl

--     P-comm-special :
--         ∃ λ proof → 
--         ([ P ]⟨ x , x′ , y , y′ ,  z ⟩ ≟₅
--         [ P ]⟨ y , y′ , x , x′ , z ⟩) ≡ just proof
--     P-comm-special = _ ,, refl
    
--     P-add-special :
--         ∃ λ proof → 
--         ([ P ]⟨ x + y , x′ + y′ , z , z′ , t ⟩ ≟₇
--         [ P ]⟨ x , x′ , z , z′ , t ⟩ + [ P ]⟨ y , y′ , z , z′ , t ⟩) ≡ just proof
--     P-add-special = _ ,, refl

--     P-compat-special :
--         ∃ λ proof → 
--         ([ P ]⟨ z * x , z * x′ , y , y′ , t ⟩ ≟₇
--         z * [ P ]⟨ x , x′ , y , y′ , t ⟩) ≡ just proof
--     P-compat-special = _ ,, refl
```