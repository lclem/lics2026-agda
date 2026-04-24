---
title: Reversal of formal series
---

In this section we define right derivatives and reversal of formal series,
and discuss their basic properties.

```
{-# OPTIONS --guardedness --sized-types #-}

open import Preliminaries.Base hiding (_++_) -- renaming (_++_ to _++ᵥ_)
module General.Reversal
    (R : CommutativeRing)
    (Σ : Set)
    where

open import Preliminaries.Algebra R
open import Preliminaries.Vector 

open import General.Terms R
    renaming (_+_ to _[+]_; _*_ to _[*]_; _·_ to _[·]_)
    
open import General.Series R Σ
open import General.ProductRules R
open import General.Products R Σ

private variable
    i : Size
    m n k ℓ : ℕ
    f g : A ⟪ Σ ⟫ i
```

# Right derivative

We begin by defining the *right derivative* of a formal series,
which is the operation symmetric to the left derivative.

```
δʳ : ∀ {j : Size< i} → Σ → A ⟪ Σ ⟫ i → A ⟪ Σ ⟫ j
ν (δʳ a f) = ν (δˡ a f)
δ (δʳ a f) b = δʳ a (δˡ b f)
```

The additional size parameters allow Agda to verify that the definition is productive.

We define the homomorphic extension `δʳ*` of the right derivative to all finite words.

```
module _ where
    open import Preliminaries.List renaming (_++ℓ_ to _++_)

      -- homomorphic extension to all words
    δʳ* : Σ * → A ⟪ Σ ⟫ → A ⟪ Σ ⟫
    δʳ* ε f = f
    δʳ* (a ∷ w) f = δʳ* w (δʳ a f)
```

## Properties of right derivatives

Left and right derivatives commute by definition,
however it is useful to state this explicitly.

```
δˡ-δʳ : ∀ (f : A ⟪ Σ ⟫) a b → δˡ a (δʳ b f) ≈ δʳ b (δˡ a f)
δˡ-δʳ f a b = ≈-refl
```

Right derivatives preserve series equivalence.

```
δʳ-cong :
    ∀ a →
    f ≈[ i ] g →
    {j : Size< i} →
    --------------------
    δʳ a f ≈[ j ] δʳ a g

ν-≈ (δʳ-cong a f≈g) = ν-≈ (δ-≈ f≈g a)
δ-≈ (δʳ-cong a f≈g) b = δʳ-cong a (δ-≈ f≈g b)

δʳ-inv : ∀ a → Congruent₁ _≈_ (δʳ a)
δʳ-inv a f≈g = δʳ-cong a f≈g
```

We show that right derivatives preserve the vector space structure.

```
open DistributivityProperties

δʳ-end-𝟘 : ∀ a → Endomorphic-𝟘 (δʳ a)
ν-≈ (δʳ-end-𝟘 a) = R-refl
δ-≈ (δʳ-end-𝟘 a) b = δʳ-end-𝟘 a

δʳ-end-+ : ∀ a → Endomorphic-+ (δʳ a)
ν-≈ (δʳ-end-+ a f g) = R-refl
δ-≈ (δʳ-end-+ a f g) b = δʳ-end-+ _ _ _

δʳ-end-· : ∀ a → Endomorphic-· (δʳ a)
ν-≈ (δʳ-end-· a c f) = R-refl
δ-≈ (δʳ-end-· a c f) b = δʳ-end-· _ _ _
```

We show how right derivatives interact with the coefficient extraction operation.

```
module _ where
    open Inductive renaming (_++ℓ_ to _++_)

    δʳ-coeff : ∀ a w f → δʳ a f ⟨ w ⟩ ≡ f ⟨ w ∷ʳ a ⟩
    δʳ-coeff a ε f = refl
    δʳ-coeff a (b ∷ w) f = δʳ-coeff a w (δˡ b f)

    -- analogous to coeff-δˡ* :
    -- ∀ (u v : List Σ) (f : A ⟪ Σ ⟫) → δˡ* u f ⟨ v ⟩ ≡ f ⟨ u ++ v ⟩
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

We define the *reversal* of a formal series,
which intuitively means that the series reads the input words backwards.

```
rev : A ⟪ Σ ⟫ → A ⟪ Σ ⟫
ν (rev f) = ν f
δ (rev f) a = rev (δʳ a f)
```

## Properties of reversal

The following rule connecting reversal, left and right derivatives holds by definition,
however it is useful to state it explicitly.

```
rev-δʳ : ∀ (f : A ⟪ Σ ⟫) a → rev (δʳ a f) ≈ δˡ a (rev f)
rev-δʳ f a = ≈-refl
```

The following variation is also useful, and we need to prove it explicitly.

```
δʳ-rev : ∀ (f : A ⟪ Σ ⟫) a → δʳ a (rev f) ≈[ i ] rev (δˡ a f)
ν-≈ (δʳ-rev f a) = R-refl
δ-≈ (δʳ-rev f a) b = δʳ-rev (δʳ b f) a
```

Reversal preserves series equivalence.

```
rev-cong :
    f ≈[ i ] g →
    ------------------
    rev f ≈[ i ] rev g

ν-≈ (rev-cong f≈g) = ν-≈ f≈g
δ-≈ (rev-cong f≈g) a = rev-cong (δʳ-cong a f≈g)
```

Reversal is an involution.

```
rev-rev :
    ∀ (f : A ⟪ Σ ⟫) →
    --------------------
    rev (rev f) ≈[ i ] f

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

We can express right derivatives in terms of left derivatives and a double reversal.

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

Reversal respects the vector space structure.

```
rev-end-𝟘 : Endomorphic-𝟘 rev
ν-≈ rev-end-𝟘 = R-refl
δ-≈ rev-end-𝟘 a =
    begin
        rev (δʳ a 𝟘) ≈⟨ rev-cong (δʳ-end-𝟘 _) ⟩
        rev 𝟘 ≈⟨ rev-end-𝟘 ⟩
        𝟘
    ∎ where open EqS
```

```
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
