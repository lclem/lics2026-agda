---
title: Reversal of formal series 🚧
---

```
{-# OPTIONS --guardedness --sized-types #-}
-- {-# OPTIONS --allow-unsolved-metas #-}

open import Preliminaries.Base hiding (_++_)
module General.Reversal
    (R : CommutativeRing)
    (Σ : Set)
    where

open import Size
open import Preliminaries.Algebra R
open import Preliminaries.PolyExpr R
    using (PolyExpr; con)
    renaming (subst to P-subst; ⟦_⟧_ to P⟦_⟧_)

open import General.Terms R
    renaming (_+_ to _[+]_; _*_ to _[*]_; _·_ to _[·]_)
    
open import General.Series R Σ
open import General.ProductRules R
open import General.Products R Σ

private variable
    i : Size
    n : ℕ
```

# Right derivative

```
δʳ : ∀ {j : Size< i} → Σ → A ⟪ Σ ⟫ i → A ⟪ Σ ⟫ j
ν (δʳ a f) = ν (δˡ a f)
δ (δʳ a f) b = δʳ a (δˡ b f)
```

```
module _ where
    open import Preliminaries.List

      -- homomorphic extension to all words
    δʳ* : Σ * → A ⟪ Σ ⟫ → A ⟪ Σ ⟫
    δʳ* ε f = f
    δʳ* (a ∷ w) f = δʳ* w (δʳ a f)
```

```
δˡ-δʳ : ∀ (f : A ⟪ Σ ⟫) a b → δˡ a (δʳ b f) ≈ δʳ b (δˡ a f)
δˡ-δʳ f a b = ≈-refl

δʳ-cong :
    ∀ {f g : A ⟪ Σ ⟫} a →
    f ≈[ i ] g →
    ------------------------------------
    {j : Size< i} → δʳ a f ≈[ j ] δʳ a g

-- δʳ-cong : ∀ {f g : A ⟪ Σ ⟫} a → f ≈ g → δʳ a f ≈ δʳ a g
ν-≈ (δʳ-cong a f≈g) = ν-≈ (δ-≈ f≈g a)
δ-≈ (δʳ-cong a f≈g) b = δʳ-cong a (δ-≈ f≈g b)
```

## Properties of the right derivative

```
open Properties

δʳ-end-𝟘 : ∀ a → Endomorphic-𝟘 (δʳ a)
ν-≈ (δʳ-end-𝟘 a) = R-refl
δ-≈ (δʳ-end-𝟘 a) b = δʳ-end-𝟘 a

δʳ-end-+ : ∀ a → Endomorphic-+ (δʳ a)
ν-≈ (δʳ-end-+ a f g) = R-refl
δ-≈ (δʳ-end-+ a f g) b = δʳ-end-+ _ _ _

δʳ-end-· : ∀ a → Endomorphic-· (δʳ a)
ν-≈ (δʳ-end-· a f g) = R-refl
δ-≈ (δʳ-end-· a f g) b = δʳ-end-· _ _ _

```

```
-- δʳ-⟨⟩ : ∀ ∀ {f g : A ⟪ Σ ⟫} a w → δʳ a f ⟨ w ⟩ ≈R (unravel λ w → f ⟨ w ++ [ a ] ⟩) ⟨ w ⟩
```

```
module _ where
    open Inductive

    δʳ-coeff : ∀ a w f → δʳ a f ⟨ w ⟩ ≡ f ⟨ w ∷ʳ a ⟩
    δʳ-coeff a ε f = refl
    δʳ-coeff a (b ∷ w) f = δʳ-coeff a w (δˡ b f)

    -- analogous to coeff-δˡ* : ∀ (u v : List Σ) (f : A ⟪ Σ ⟫) → δˡ* u f ⟨ v ⟩ ≡ f ⟨ u ++ v ⟩
    coeff-δʳ* : ∀ u v f → δʳ* u f ⟨ v ⟩ ≡ f ⟨ v ++ reverse u ⟩
    coeff-δʳ* ε v f =
        begin
            δʳ* ε f ⟨ v ⟩ ≡⟨⟩
            f ⟨ v ⟩ ≡⟨ cong (λ w → f ⟨ w ⟩) (++-identityʳ v) ⟨
            f ⟨ v ++ ε ⟩ ≡⟨⟩
            f ⟨ v ++ reverse ε ⟩
        ∎ where open ≡-Eq
    coeff-δʳ* (a ∷ u) v f = 
        begin
            δʳ* (a ∷ u) f ⟨ v ⟩ ≡⟨⟩
            δʳ* u (δʳ a f) ⟨ v ⟩ ≡⟨ coeff-δʳ* u v _ ⟩
            δʳ a f ⟨ v ++ reverse u ⟩ ≡⟨ δʳ-coeff a (v ++ reverse u) f ⟩
            f ⟨ (v ++ reverse u) ∷ʳ a ⟩ ≡⟨ cong (λ x → f ⟨ x ⟩) (++-assoc v (reverse u) _) ⟩
            f ⟨ v ++ (reverse u ∷ʳ a) ⟩ ≡⟨ cong (λ x → f ⟨ v ++ x ⟩) (unfold-reverse a u) ⟨
            f ⟨ v ++ reverse (a ∷ u) ⟩
        ∎ where open ≡-Eq

    -- δʳ-δʳ* : ∀ b u v f → δʳ b (δʳ* v f) ≡ δˡ* u (δʳ* (v ∷ʳ b) f)
    -- δʳ-δʳ* = {!   !}

    δʳ-δʳ* : ∀ a w f → δʳ a (δʳ* w f) ≡ δʳ* (w ∷ʳ a) f  
    δʳ-δʳ* a ε f = refl
    δʳ-δʳ* a (b ∷ w) f = δʳ-δʳ* a w (δʳ b f)

    δʳ-δˡ* : ∀ f a w → δʳ a (δˡ* w f) ≈ δˡ* w (δʳ a f)
    δʳ-δˡ* f a ε = ≈-refl
    δʳ-δˡ* f a (_ ∷ w) = δʳ-δˡ* _ a w

    coeff-δˡ*-δʳ* :
        ∀ u v f w →
        -------------------------------------------------
        δˡ* u (δʳ* v f) ⟨ w ⟩ ≡ f ⟨ u ++ w ++ reverse v ⟩
        
    coeff-δˡ*-δʳ* u v f w =
        begin
            δˡ* u (δʳ* v f) ⟨ w ⟩
            ≡⟨ coeff-δˡ* u w _ ⟩
            δʳ* v f ⟨ u ++ w ⟩
            ≡⟨ coeff-δʳ* v (u ++ w) _ ⟩
            f ⟨ (u ++ w) ++ reverse v ⟩
            ≡⟨ cong (λ x → f ⟨ x ⟩) (++-assoc u w (reverse v)) ⟩
            f ⟨ u ++ (w ++ reverse v) ⟩
        ∎ where open ≡-Eq
```

# Reversal

```
rev : A ⟪ Σ ⟫ → A ⟪ Σ ⟫
ν (rev f) = ν f
δ (rev f) a = rev (δʳ a f)
```

## Basic properties of reversal

```
-- holds by definition
rev-δʳ : ∀ (f : A ⟪ Σ ⟫) a → rev (δʳ a f) ≈ δˡ a (rev f)
rev-δʳ f a = ≈-refl

-- the other direction we need to prove
δʳ-rev : ∀ (f : A ⟪ Σ ⟫) a → δʳ a (rev f) ≈[ i ] rev (δˡ a f)
ν-≈ (δʳ-rev f a) = R-refl
δ-≈ (δʳ-rev f a) b = δʳ-rev (δʳ b f) a
```

```
-- rev-⟨⟩ : ∀ (f : A ⟪ Σ ⟫) (w : Σ *) → rev f ⟨ w ⟩ ≈R f ⟨ reverse w ⟩
-- rev-⟨⟩ f ε = R-refl
-- rev-⟨⟩ f (a ∷ w) =
--   begin
--     rev (δʳ a f) ⟨ w ⟩
--         ≈⟨ rev-⟨⟩ (δʳ a f) w ⟩
--     δʳ a f ⟨ reverse w ⟩
--         ≈⟨ {!   !} ⟩
--     (unravel λ w → f ⟨ w ++ [ a ] ⟩) ⟨ reverse w ⟩
--         ≈⟨ {!   !} ⟩
--     f ⟨ reverse w ++ [ a ] ⟩
--         ≈⟨ {!   !} ⟩
--     f ⟨ reverse (a ∷ w) ⟩ ∎
--   where open EqR
```

```
rev-cong :
    ∀ {f g : A ⟪ Σ ⟫} →
    f ≈[ i ] g →
    -------------------
    rev f ≈[ i ] rev g

ν-≈ (rev-cong f≈g) = ν-≈ f≈g
δ-≈ (rev-cong f≈g) a = rev-cong (δʳ-cong a f≈g)
```

```
rev-rev : ∀ (f : A ⟪ Σ ⟫) → rev (rev f) ≈[ i ] f
ν-≈ (rev-rev f) = R-refl
δ-≈ (rev-rev f) a = 
  begin
    δˡ a (rev (rev f))
      ≈⟨⟩
    rev (δʳ a (rev f))
      ≈⟨ rev-cong (δʳ-rev f a) ⟩
    rev (rev (δˡ a f))
      ≈⟨ rev-rev _ ⟩
    δˡ a f
  ∎ where open EqS
```

```
δʳ-rev-rev :
    ∀ (f : A ⟪ Σ ⟫) a →
    --------------------------------
    δʳ a f ≈[ i ] rev (δˡ a (rev f))

δʳ-rev-rev f a =
    begin
        δʳ a f ≈⟨ rev-rev _ ⟨
        rev (rev (δʳ a f))
            ≈⟨ rev-cong (rev-δʳ _ _) ⟩
        rev (δˡ a (rev f))
    ∎ where open EqS
```

```
rev-end-𝟘 : Endomorphic-𝟘 rev
ν-≈ rev-end-𝟘 = R-refl
δ-≈ rev-end-𝟘 a =
    begin
        rev (δʳ a 𝟘) ≈⟨ rev-cong (δʳ-end-𝟘 _) ⟩
        rev 𝟘 ≈⟨ rev-end-𝟘 ⟩
        𝟘
    ∎ where open EqS

rev-end-+ : Endomorphic-+ rev
ν-≈ (rev-end-+ f g) = R-refl
δ-≈ (rev-end-+ f g) a =
    begin
        δˡ a (rev (f + g))
            ≈⟨⟩
        rev (δʳ a (f + g))
            ≈⟨ rev-cong (δʳ-end-+ _ _ _) ⟩
        rev (δʳ a f + δʳ a g)
            ≈⟨ rev-end-+ (δʳ a f) (δʳ a g) ⟩
        rev (δʳ a f) + rev (δʳ a g)
            ≈⟨⟩
        δˡ a (rev f) + δˡ a (rev g)
    ∎ where open EqS
```

```
rev-end-· : Endomorphic-· rev
ν-≈ (rev-end-· c f) = R-refl
δ-≈ (rev-end-· c f) a =
    begin
        δˡ a (rev (c · f))
            ≈⟨⟩
        rev (δʳ a (c · f))
            ≈⟨ rev-cong (δʳ-end-· _ _ _) ⟩
        rev (c · (δʳ a f))
            ≈⟨ rev-end-· c (δʳ a f) ⟩
        c · rev (δʳ a f)
            ≈⟨⟩
        δˡ a (c · rev f)
    ∎ where open EqS
```

# Product rule for right derivatives

# Product rule for reversal

```
module Reversal (P : ProductRule) where

    open Product P -- renaming (⟦_⟧⟨_,_,_,_⟩ to)

    P-Rev : Set
    P-Rev = ∀ {i} f g a → δʳ a (f * g) ≈[ i ] ⟦ P ⟧⟨ f , δʳ a f , g , δʳ a g ⟩
```

We show that if reversal is an endomorphism,
then the equation `P-Rev` holds.

```
    module RevEnd→PU-Rev (rev-end : IsEndomorphism rev) where

        end-rev :
            ∀ (p : Term′ n) (ϱ : SEnvᵥ n) →
            ---------------------------------------
            rev (⟦ p ⟧ᵥ (map rev ϱ)) ≈[ i ] ⟦ p ⟧ᵥ ϱ

        end-rev p ϱ =
            begin
                rev (⟦ p ⟧ᵥ (map rev ϱ))
                    ≈⟨ rev-cong (endᵥ p ϱ rev-end) ⟨
                rev (rev (⟦ p ⟧ᵥ ϱ))
                    ≈⟨ rev-rev _ ⟩
                ⟦ p ⟧ᵥ ϱ
            ∎ where open EqS
        
        p-rev : P-Rev
        p-rev f g a =
            begin
                δʳ a (f * g)
                    ≈⟨ δʳ-rev-rev _ _ ⟩
                rev (δˡ a (rev (f * g)))
                    ≈⟨ rev-cong (δ-≈ (*-end rev-end f g) a) ⟩
                rev (δˡ a (rev f * rev g))
                    ≈⟨⟩
                rev ⟦ P ⟧⟨ rev f , δˡ a (rev f) , rev g , δˡ a (rev g) ⟩
                    ≈⟨⟩
                rev ⟦ P ⟧⟨ rev f , rev (δʳ a f) , rev g , rev (δʳ a g) ⟩
                    ≈⟨ end-rev P (_ ∷ _ ∷ _ ∷ _ ∷ []) ⟩
                ⟦ P ⟧⟨ f , δʳ a f , g , δʳ a g ⟩
            ∎ where open EqS
```

We show that if the equation `P-Rev` holds,
then reversal is an endomorphism.

```
    module _
        (ass-* : P-Rev)
        where

        mutual
            rev-end-* : Endomorphic-* rev {i}
            ν-≈ (rev-end-* f g) = R-refl
            δ-≈ (rev-end-* f g) a =
                begin
                    δˡ a (rev (f * g))
                        ≈⟨⟩
                    rev (δʳ a (f * g))
                        ≈⟨ rev-cong (ass-* f g a) ⟩
                    rev ⟦ P ⟧⟨ f , δʳ a f , g , δʳ a g ⟩
                        ≈⟨ endᵥ P (_ ∷ _ ∷ _ ∷ _ ∷ []) rev-end ⟩
                    ⟦ P ⟧⟨ rev f , rev (δʳ a f) , rev g , rev (δʳ a g) ⟩
                        ≈⟨⟩
                    ⟦ P ⟧⟨ rev f , δˡ a (rev f) , rev g , δˡ a (rev g) ⟩
                        ≈⟨⟩
                    δˡ a (rev f * rev g)
                ∎ where open EqS

            rev-end : IsEndomorphism rev {i}
            rev-end = record {
                𝟘-end = rev-end-𝟘;
                ·-end = rev-end-·;
                +-end = rev-end-+;
                *-end = rev-end-*
                }
```

# Closure under right derivatives

We show that if reversal is an endomorphism,
then `*`-finite series are closed under right derivatives.

TODO: prove it

```
    -- P-fin-δʳ : P-fin f k → ∀ b → P-fin (δʳ b f) (m +ℕ m)
    -- P-fin-δʳ *-fin b = ?
```