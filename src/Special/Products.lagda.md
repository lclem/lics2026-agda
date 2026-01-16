---
title: "Special products 🚧"
---

```
{-# OPTIONS --guardedness --sized-types #-}
-- --allow-unsolved-metas

open import Size
open import Preliminaries.Base

module Special.Products
    (R : CommutativeRing)
    (Σ : Set)
    where

open import Preliminaries.Algebra R
open import Preliminaries.PolyExpr R
    using (con; var; ≈-eval₀)

open import General.Series R Σ
open import General.Terms R
    renaming (_+_ to _[+]_; _*_ to _[*]_; _·_ to _[·]_; -_ to [-]_; _-_ to _[-]_)
open import General.ProductRules R

import Special.Polynomials R as P
open import Special.ProductRules R

private variable
    X Y : Set
    i : Size
    m n : ℕ
```

We are interested in the following algebraic properties of produts of series.

```
module ProductProperties 
    {P : ProductRule}
    (special : Special P)

    where

    open import General.Products R Σ
    open Product P

    *-Assoc : Size → Set
    *-Assoc i = ∀ (f g h : A ⟪ Σ ⟫) → (f * g) * h ≈[ i ] f * (g * h)

    *-Comm : Size → Set
    *-Comm i = ∀ (f g : A ⟪ Σ ⟫) → f * g ≈[ i ] g * f

    Distribʳ : Size → Set
    Distribʳ i = ∀ (f g h : A ⟪ Σ ⟫) → (g + h) * f ≈[ i ] (g * f) + (h * f)

    Distribˡ : Size → Set
    Distribˡ i = ∀ (f g h : A ⟪ Σ ⟫) → f * (g + h) ≈[ i ] (f * g) + (f * h)

    *-Zeroʳ : Size → Set
    *-Zeroʳ i = ∀ (f : A ⟪ Σ ⟫) → f * 𝟘 ≈[ i ] 𝟘

    ·-*-Distrib : Size → Set
    ·-*-Distrib i = ∀ (c : A) (f g : A ⟪ Σ ⟫) → (c · f) * g ≈[ i ] c · (f * g)

    -- these two already hold (by definition of scalar multiplication and sum)
    -- +-·-Distr : Size → Set
    -- +-·-Distr i = ∀ (c d : A) (f : A ⟪ Σ ⟫) → (c +R d) · f ≈[ i ] c · f + d · f

    -- *-·-Distr : Size → Set
    -- *-·-Distr i = ∀ (c d : A) (f : A ⟪ Σ ⟫) → (c *R d) · f ≈[ i ] c · (d · f)
```

We show that whenever the product specification is special,
then we obtain a commutative algebra of series.

```
    mutual
        
        *-assoc : *-Assoc i
        ν-≈ (*-assoc f g h) = *R-assoc (ν f) (ν g) (ν h)
        δ-≈ (*-assoc f g h) a =
            let ϱ = f ∷ δ f a ∷ g ∷ δ g a ∷ h ∷ δ h a ∷ [] in
            begin
                δ ((f * g) * h) a
                    ≈⟨⟩
                ⟦ P ⟧⟨ f * g , ⟦ P ⟧⟨ f , δ f a , g , δ g a ⟩ , h , δ h a ⟩
                    ≈⟨ ⟦ P ⟧≈ᵥ  [ ≈-refl , eval-substᵥ P {_ ∷ _ ∷ _ ∷ _ ∷ []} , ≈-refl , ≈-refl ] ⟨
                ⟦ P ⟧⟨ ⟦ x [*] y ⟧ᵥ ϱ , ⟦ [ P ]⟨ x , x′ , y , y′ ⟩ ⟧ᵥ ϱ , ⟦ z ⟧ᵥ ϱ , ⟦ z′ ⟧ᵥ ϱ ⟩
                    ≈⟨ eval-substᵥ P {_ ∷ _ ∷ _ ∷ _ ∷ []} ⟨
                ⟦ [ P ]⟨ x [*] y , [ P ]⟨ x , x′ , y , y′ ⟩ , z , z′ ⟩ ⟧ᵥ ϱ
                    ≈⟨ invariance (P-assoc special) ⟩
                ⟦ [ P ]⟨ x , x′ , y [*] z , [ P ]⟨ y , y′ , z , z′ ⟩ ⟩ ⟧ᵥ ϱ
                    ≈⟨ eval-substᵥ P {_ ∷ _ ∷ _ ∷ _ ∷ []} ⟩
                ⟦ P ⟧⟨ f , δ f a , g * h , ⟦ [ P ]⟨ y , y′ , z , z′ ⟩ ⟧ᵥ ϱ ⟩
                    ≈⟨ ⟦ P ⟧≈ᵥ [ ≈-refl , ≈-refl , ≈-refl , eval-substᵥ P {_ ∷ _ ∷ _ ∷ _ ∷ []} ] ⟩
                ⟦ P ⟧⟨ f , δ f a , g * h , ⟦ P ⟧⟨ g , δ g a , h , δ h a ⟩ ⟩
                    ≈⟨⟩
                δ (f * (g * h)) a
                ∎ where open EqS

        *-comm : *-Comm i
        ν-≈ (*-comm f g) = *R-comm (ν f) (ν g)
        δ-≈ (*-comm f g) a =
            let ϱ = f ∷ δ f a ∷ g ∷ δ g a ∷ [] in
            begin
                ⟦ P ⟧ᵥ ϱ
                    ≈⟨ eval-substᵥ P {_ ∷ _ ∷ _ ∷ _ ∷ []} ⟨
                ⟦ [ P ]⟨ x , x′ , y , y′ ⟩ ⟧ᵥ ϱ
                    ≈⟨ invariance (P-comm special) ⟩
                ⟦ [ P ]⟨ y , y′ , x , x′ ⟩ ⟧ᵥ ϱ
                    ≈⟨ eval-substᵥ P {_ ∷ _ ∷ _ ∷ _ ∷ []} ⟩
                ⟦ P ⟧⟨ g , δ g a , f , δ f a ⟩
                ∎ where open EqS

        *-distribʳ : Distribʳ i
        ν-≈ (*-distribʳ f g h) = R-distribʳ (ν f) (ν g) (ν h)
        δ-≈ (*-distribʳ h f g) a =
            let ϱ = f ∷ δ f a ∷ g ∷ δ g a ∷ h ∷ δ h a ∷ [] in
            begin
                ⟦ P ⟧⟨ f + g , δ f a + δ g a , h , δ h a ⟩
                    ≈⟨⟩
                ⟦ P ⟧⟨ ⟦ x [+] y ⟧ᵥ ϱ , ⟦ x′ [+] y′ ⟧ᵥ ϱ , ⟦ z ⟧ᵥ ϱ , ⟦ z′ ⟧ᵥ ϱ ⟩
                    ≈⟨ eval-substᵥ P {_ ∷ _ ∷ _ ∷ _ ∷ []} ⟨
                ⟦ [ P ]⟨ x [+] y , x′ [+] y′ , z , z′ ⟩ ⟧ᵥ ϱ
                    ≈⟨ invariance (P-distr special) ⟩
                ⟦ [ P ]⟨ x , x′ , z , z′ ⟩ [+] [ P ]⟨ y , y′ , z , z′ ⟩ ⟧ᵥ ϱ
                    ≈⟨  (eval-substᵥ P {_ ∷ _ ∷ _ ∷ _ ∷ []}
                            ⟨ +-cong ⟩
                        eval-substᵥ P {_ ∷ _ ∷ _ ∷ _ ∷ []}) ⟩
                ⟦ P ⟧⟨ f , δ f a , h , δ h a ⟩ + ⟦ P ⟧⟨ g , δ g a , h , δ h a ⟩
            ∎ where open EqS

        -- follows from *-distrʳ and commutativity
        *-distribˡ : Distribˡ i
        *-distribˡ f g h =
            begin
                f * (g + h)
                    ≈⟨ *-comm _ _ ⟩
                (g + h) * f
                    ≈⟨ *-distribʳ _ _ _ ⟩
                g * f + h * f
                    ≈⟨ +-cong (*-comm _ _) (*-comm _ _) ⟩
                f * g + f * h
            ∎ where open EqS

        ·-*-distrib : ·-*-Distrib i
        ν-≈ (·-*-distrib c f g) = *R-assoc _ _ _
        δ-≈ (·-*-distrib c f g) a =
            let ϱ = f ∷ δ f a ∷ g ∷ δ g a ∷ [] in
            begin
                δ ((c · f) * g) a
                    ≈⟨⟩
                ⟦ P ⟧⟨ c · f , c · δ f a , g , δ g a ⟩
                    ≈⟨⟩
                ⟦ P ⟧⟨ c · ⟦ x ⟧ᵥ ϱ , c · ⟦ x′ ⟧ᵥ ϱ , ⟦ y ⟧ᵥ ϱ , ⟦ y′ ⟧ᵥ ϱ ⟩
                    ≈⟨⟩
                ⟦ P ⟧⟨ ⟦ c [·] x ⟧ᵥ ϱ , ⟦ c [·] x′ ⟧ᵥ ϱ , ⟦ y ⟧ᵥ ϱ , ⟦ y′ ⟧ᵥ ϱ ⟩
                    ≈⟨ eval-substᵥ P {_ ∷ _ ∷ _ ∷ _ ∷ _} ⟨
                ⟦ [ P ]⟨ c [·] x , c [·] x′ , y , y′ ⟩ ⟧ᵥ ϱ
                    ≈⟨ invariance (P-compat special c) ⟩
                ⟦ c [·] [ P ]⟨ x , x′ , y , y′ ⟩ ⟧ᵥ ϱ
                    ≈⟨⟩
                c · ⟦ [ P ]⟨ x , x′ , y , y′ ⟩ ⟧ᵥ ϱ
                    ≈⟨ ·-cong R-refl (eval-substᵥ P {_ ∷ _ ∷ _ ∷ _ ∷ []}) ⟩
                c · ⟦ P ⟧⟨ ⟦ x ⟧ᵥ ϱ , ⟦ x′ ⟧ᵥ ϱ , ⟦ y ⟧ᵥ ϱ , ⟦ y′ ⟧ᵥ ϱ ⟩
                    ≈⟨⟩
                c · ⟦ P ⟧⟨ f , δ f a , g , δ g a ⟩
                    ≈⟨⟩
                δ (c · (f * g)) a
            ∎ where open EqS

        -- the semantics of polynomial expressions is invariant under the equivalence
        -- generated by associativity, commutativity, and distributivity
        -- (provided that the product has the same properties)
        invariance :
            ∀ {p q : Term X} {ϱ : SEnv X} →
            p P.≈ q →
            ---------------------------------
            ⟦ p ⟧ ϱ ≈[ i ] ⟦ q ⟧ ϱ
        
        invariance P.≈-refl = ≈-refl
        invariance (P.≈-sym w) = ≈-sym (invariance w)
        invariance (P.≈-trans u v)= ≈-trans (invariance u) (invariance v)
        invariance (P.·-cong c≈d p≈q) = ·-cong c≈d (invariance p≈q)
        invariance (P.·-one _) = ·-one _
        invariance (P.·-+-distrib c p q)  = ·-+-distrib _ _ _ where open Properties
        invariance (P.+-·-distrib p c d)  = +-·-distrib _ _ _ where open Properties
        invariance (P.·-*-distrib c p q)  = ·-*-distrib _ _ _
        invariance (P.*-·-distrib c d p)  = *-·-distrib _ _ _ where open Properties
        invariance (P.+-cong P0≈P1 Q0≈Q1) = +-cong (invariance P0≈P1) (invariance Q0≈Q1)
        invariance (P.+-zeroʳ p) = +-identityʳ _
        invariance (P.+-assoc p q r) = +-assoc _ _ _
        invariance (P.+-comm p q) = +-comm _ _
        invariance (P.+-invʳ p) = -‿inverseʳ _
        invariance (P.*-cong P0≈P1 Q0≈Q1) = *-cong (invariance P0≈P1) (invariance Q0≈Q1)
        invariance (P.*-assoc _ _ _) = *-assoc _ _ _
        invariance (P.*-comm _ _) = *-comm _ _
        invariance (P.*-distribʳ _ _ _) = *-distribʳ _ _ _

    -- TODO: remove identity
    -- *-isMonoid : IsMonoid _≈_ _*_ 𝟙
    -- *-isMonoid = record {
    --         isSemigroup = record {
    --             isMagma = record {
    --                 isEquivalence = isEquivalence-≈;
    --                 ∙-cong = *-cong
    --                 };
    --             assoc = *-assoc
    --             };
    --         identity = *-identity
    --     }

    -- isRing : IsRing _≈_ _+_ _*_ -_ 𝟘 𝟙
    -- isRing = record
    --     { +-isAbelianGroup = +-isAbelianGroup
    --     ; *-cong = *-cong
    --     ; *-assoc = *-assoc
    --     ; *-identity = *-identity
    --     ; distrib = record { fst = *-distribˡ ; snd = *-distribʳ }
    --     }

    -- isCommutativeRing : IsCommutativeRing _≈_ _+_ _*_ -_ 𝟘 𝟙
    -- isCommutativeRing = record {
    --         isRing = isRing ;
    --         *-comm = *-comm 
    --     }

    -- isSeriesAlgebra : IsAlgebra _≈_ _+_ _*_ -_ 𝟘 𝟙 _·_
    -- isSeriesAlgebra = record {
    --       isRing = isCommutativeRing
    --     ; isLeftModule = isLeftModule
    --     ; compatible = ·-*-distrib }
```

# Applications

We recover that the known series products are commutative algebras.

```
-- open Examples Σ
-- module HadamardAlgebra where

--     open import General.Products R Σ
--     open Product ruleHadamard
--     open ProductProperties HadamardSpecial.special
--     open Hadamard

--     _ : IsAlgebra _≈_ _+_ _⊙_ -_ 𝟘 𝟙 _·_
--     _ = ≈-algebra _≈_ isEquivalence-≈ isSeriesAlgebra agree

-- module ShuffleAlgebra where

--     open import General.Products R Σ
--     open Product ruleShuffle
--     open ProductProperties ShuffleSpecial.special
--     open Shuffle

--     _ : IsAlgebra _≈_ _+_ _⧢_ -_ 𝟘 𝟙 _·_
--     _ = ≈-algebra _≈_ isEquivalence-≈ isSeriesAlgebra agree

-- module InfiltrationAlgebra where

--     open import General.Products R Σ
--     open Product ruleInfiltration
--     open ProductProperties InfiltrationSpecial.special
--     open Infiltration

--     _ : IsAlgebra _≈_ _+_ _↑_ -_ 𝟘 𝟙 _·_
--     _ = ≈-algebra _≈_ isEquivalence-≈ isSeriesAlgebra agree
```