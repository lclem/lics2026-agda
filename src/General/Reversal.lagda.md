---
title: Reversal of formal series 🚧
---

In this section we define right derivatives and reversal of formal series,
and discuss their basic properties.

```
{-# OPTIONS --guardedness --sized-types #-}

open import Preliminaries.Base renaming (_++_ to _++ᵥ_)
module General.Reversal
    (R : CommutativeRing)
    (Σ : Set)
    where

open import Size
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
    open import Preliminaries.List

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

δʳ-inv : ∀ a → ≈-Invariance (δʳ a)
δʳ-inv a f≈g = δʳ-cong a f≈g
```

We show that right derivatives preserve the vector space structure.

```
open Properties

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
    open Inductive

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

# Product rules

In this section we study the connection between

- product rules satisfied by right derivatives, and
- reversal preserving the product operation.

```
module Reversal (P : ProductRule) where

    open Product P

    δʳ-sat-P : Set
    δʳ-sat-P = ∀ a → (δʳ a) satisfies P
```

## From reversal to a product rule

We show that if reversal is an endomorphism,
then the equation `δʳ-sat-P` holds.

``` 
    end→P-rev : (end : IsEndomorphism rev) → δʳ-sat-P
    end→P-rev end a f g =
        begin
            δʳ a (f * g)
                ≈⟨ δʳ-rev-rev _ _ ⟩
            rev (δˡ a (rev (f * g)))
                ≈⟨ rev-cong (δ-≈ (*-end end f g) a) ⟩
            rev (δˡ a (rev f * rev g))
                ≈⟨⟩
            rev ⟦ P ⟧⟨ rev f , δˡ a (rev f) , rev g , δˡ a (rev g) ⟩
                ≈⟨⟩
            rev ⟦ P ⟧⟨ rev f , rev (δʳ a f) , rev g , rev (δʳ a g) ⟩
                ≈⟨ endᵥ P (_ ∷ _ ∷ _ ∷ _ ∷ []) end ⟩
            ⟦ P ⟧⟨ rev (rev f) , rev (rev (δʳ a f)) , rev (rev g) , rev (rev (δʳ a g)) ⟩
                ≈⟨ ⟦ P ⟧≈ᵥ [ rev-rev _ , rev-rev _ , rev-rev _ , rev-rev _ ] ⟩
            ⟦ P ⟧⟨ f , δʳ a f , g , δʳ a g ⟩
        ∎ where open EqS
```

## From product rule to reversal

Viceversa, if the equation `δʳ-sat-P` holds,
then reversal is an endomorphism.

```
    P-rev→end : (p-rev : δʳ-sat-P) → IsEndomorphism rev {i}
    P-rev→end p-rev = record {
        𝟘-end = rev-end-𝟘;
        ·-end = rev-end-·;
        +-end = rev-end-+;
        *-end = rev-end-*
        } where

        rev-end-* : Endomorphic-* rev {i}
        ν-≈ (rev-end-* f g) = R-refl
        δ-≈ (rev-end-* f g) a =
            begin
                δˡ a (rev (f * g))
                    ≈⟨⟩
                rev (δʳ a (f * g))
                    ≈⟨ rev-cong (p-rev a f g) ⟩
                rev ⟦ P ⟧⟨ f , δʳ a f , g , δʳ a g ⟩
                    ≈⟨ endᵥ P (_ ∷ _ ∷ _ ∷ _ ∷ []) (P-rev→end p-rev)⟩
                ⟦ P ⟧⟨ rev f , rev (δʳ a f) , rev g , rev (δʳ a g) ⟩
                    ≈⟨⟩
                ⟦ P ⟧⟨ rev f , δˡ a (rev f) , rev g , δˡ a (rev g) ⟩
                    ≈⟨⟩
                δˡ a (rev f * rev g)
            ∎ where open EqS
```

## Unary operators satisfying a product rule

Let `F` be a unary operator on series.
If `F` satisfy a product rule,
then `F` of `⟦ u ⟧ᵥ ϱ`
is a polynomial function of `ϱ` and its image under `F`.

### Primed variables

We begin by defining a facility to extend variables and terms.
If `x` is a variable, then `x ′` is a copy of `x` on the right.

```
    infix 10 _′
    _′ : Var k → Var (ℓ +ℕ k)
    _′ {ℓ = ℓ} x =  ℓ ↑ʳ x
```

The fundamental property of primed variables is the following.

```
    prime-lemma₀ :
        ∀ (x : Var k) (ϱ : Vec (A ⟪ Σ ⟫) ℓ) η →
        ---------------------------------------
        ⟦ var x ⟧ᵥ η ≈ ⟦ var (x ′) ⟧ᵥ (ϱ ++ᵥ η)
    
    prime-lemma₀ x [] η = ≈-refl
    prime-lemma₀ x (_ ∷ ϱ) η = prime-lemma₀ x ϱ η
```

We will use the following specialisation of `prime-lemma₀`.

```
    prime-lemma :
        ∀ (x : Var k) F ϱ →
        ------------------------------------------------
        F (⟦ var x ⟧ᵥ ϱ) ≈ ⟦ var (x ′) ⟧ᵥ (ϱ ++ᵥ map F ϱ)

    prime-lemma x F ϱ =
        begin
            F (⟦ var x ⟧ᵥ ϱ)
                ≈⟨⟩
            F (lookup ϱ x)
                ≡⟨ lookup-map F ϱ x ⟨
            lookup (map F ϱ) x
                ≈⟨⟩
            ⟦ var x ⟧ᵥ map F ϱ
                ≈⟨ prime-lemma₀ x ϱ (map F ϱ) ⟩
            ⟦ var (x ′) ⟧ᵥ (ϱ ++ᵥ map F ϱ)
        ∎ where open EqS
```

### Extended terms

We allow variables to appear in larger sets of variables.
We keep the same index but in a larger finite set.

```
    infix 10 ′_
    ′_ : Var k → Var (k +ℕ ℓ)
    ′_ {ℓ = ℓ} x = x ↑ˡ ℓ
```

The following is the crucial property of `′ x`.

```
    ext-var-lem :
        ∀ (x : Var k) ϱ (η : Vec (A ⟪ Σ ⟫) ℓ) →
        --------------------------------------------
        ⟦ var x ⟧ᵥ ϱ ≈ ⟦ var (′ x) ⟧ᵥ (ϱ ++ᵥ η)

    ext-var-lem zero ϱ η =
        begin
            lookup ϱ zero
                ≡⟨ lookup-zero-++ ϱ η ⟩
            lookup (ϱ ++ᵥ η) zero
        ∎ where open EqS
        
    ext-var-lem (suc x) (_ ∷ ϱ) η = ext-var-lem x ϱ η
```

We extend this operation to all terms.

```
    ext : Term′ k → Term′ (k +ℕ k)
    ext 0T = 0T
    ext (var x) = var (′ x)
    ext (c [·] u) = c [·] ext u
    ext (u [+] v) = ext u [+] ext v
    ext (u [*] v) = ext u [*] ext v
```

The crucial property is that the semantics of the extended term
equals the semantics of the original one.

```
    ext-lem :
        ∀ (u : Term′ k) ϱ η →
        ------------------------------
        ⟦ u ⟧ᵥ ϱ ≈ ⟦ ext u ⟧ᵥ (ϱ ++ᵥ η)

    ext-lem 0T ϱ η = ≈-refl

    ext-lem (var x) ϱ η = ext-var-lem x ϱ η

    ext-lem (c [·] u) ϱ η
        with ext-lem u ϱ η
    ... | ass = R-refl ·≈ ass

    ext-lem (u [+] v) ϱ η
        with ext-lem u ϱ η | ext-lem v ϱ η
    ... | ass-u | ass-v = ass-u +≈ ass-v

    ext-lem (u [*] v) ϱ η
        with ext-lem u ϱ η | ext-lem v ϱ η
    ... | ass-u | ass-v = ass-u *≈ ass-v
```

### `Q`-extensions

Let `Q` be a product rule and `F` a unary operator on series.
If `F` is a `Q`-extension, then we can extend the product rule to arbitrary terms.

```
    extension-lem :
        ∀ ϱ {F Q} →
        F IsExt Q →
        (u : Term′ k) →
        -------------------------------------------
        ∃[ v ] F (⟦ u ⟧ᵥ ϱ) ≈ ⟦ v ⟧ᵥ (ϱ ++ᵥ map F ϱ)
    
    extension-lem ϱ isExt 0T = 0T ,, isExt .𝟘-ext

    extension-lem ϱ isExt (var x) = var (x ′) ,, prime-lemma x _ ϱ

    extension-lem ϱ {F} isExt (c [·] u)
        with extension-lem ϱ isExt u
    ... | u′ ,, ass = c [·] u′ ,, it where
        it =
            begin
                F (⟦ c [·] u ⟧ᵥ ϱ)
                    ≈⟨⟩
                F (c · (⟦ u ⟧ᵥ ϱ))
                    ≈⟨ isExt .·-ext _ _ ⟩
                 c · F (⟦ u ⟧ᵥ ϱ)
                    ≈⟨ R-refl ·≈ ass ⟩
                c · ⟦ u′ ⟧ᵥ (ϱ ++ᵥ map F ϱ)
                    ≈⟨⟩
                ⟦ c [·] u′ ⟧ᵥ (ϱ ++ᵥ map F ϱ)
            ∎ where open EqS

    extension-lem ϱ {F} isExt (u [+] v)
        with extension-lem ϱ isExt u | extension-lem ϱ isExt v
    ... | u′ ,, ass-u | v′ ,, ass-v = (u′ [+] v′) ,, it where

            it = begin
                F (⟦ u [+] v ⟧ᵥ ϱ)
                    ≈⟨⟩
                F (⟦ u ⟧ᵥ ϱ + ⟦ v ⟧ᵥ ϱ)
                    ≈⟨ isExt .+-ext _ _ ⟩
                F (⟦ u ⟧ᵥ ϱ) + F (⟦ v ⟧ᵥ ϱ)
                    ≈⟨ ass-u +≈ ass-v ⟩
                ⟦ u′ ⟧ᵥ (ϱ ++ᵥ map F ϱ) + ⟦ v′ ⟧ᵥ (ϱ ++ᵥ map F ϱ)
                    ≈⟨⟩
                ⟦ u′ [+] v′ ⟧ᵥ (ϱ ++ᵥ map F ϱ)
                ∎ where open EqS

    extension-lem ϱ {F} {Q} isExt (u [*] v)
        with extension-lem ϱ isExt u | extension-lem ϱ isExt v
    ... | u′ ,, ass-u | v′ ,, ass-v
        = [ Q ]⟨ ext u , u′ , ext v , v′ ⟩ ,, it where

        η = ϱ ++ᵥ map F ϱ

        ext-u = ext-lem u ϱ (map F ϱ)
        ext-v = ext-lem v ϱ (map F ϱ)

        it = begin
            F (⟦ u [*] v ⟧ᵥ ϱ)
                ≈⟨⟩
            F (⟦ u ⟧ᵥ ϱ * ⟦ v ⟧ᵥ ϱ)
                ≈⟨ isExt .*-ext _ _ ⟩
            ⟦ Q ⟧⟨ ⟦ u ⟧ᵥ ϱ , F (⟦ u ⟧ᵥ ϱ) , ⟦ v ⟧ᵥ ϱ , F (⟦ v ⟧ᵥ ϱ) ⟩
                ≈⟨ ⟦ Q ⟧≈ᵥ [ ext-u , ass-u , ext-v , ass-v ] ⟩
            ⟦ Q ⟧⟨ ⟦ ext u ⟧ᵥ η , ⟦ u′ ⟧ᵥ η , ⟦ ext v ⟧ᵥ η , ⟦ v′ ⟧ᵥ η ⟩
                ≈⟨ eval-substᵥ Q {_ ∷ _ ∷ _ ∷ _ ∷ []} ⟨
            ⟦ [ Q ]⟨ ext u , u′ , ext v , v′ ⟩ ⟧ᵥ η
            ∎ where open EqS
```

# Closure under right derivatives

We show that if right derivatives satisfy *any* product rule (not necessarily `P`),
then `P`-finite series are closed under right derivatives.

In particular, by the previous section this is the case when reversal is an endomorphism.

```
    open import Data.Product.Base using (∃; ∃-syntax; _,_)
    open import Data.Product using (_×_)
    open import Preliminaries.Vector
    open import General.FinitelyGenerated R Σ P
```

We begin with a general lemma, showing that if `F` is a `Q`-extension
and `f` is generated by `ϱ`,
then `F f` is generated by the same set together with their images under `F`.

```
    F-closed :
        ∀ {ϱ : Vec (A ⟪ Σ ⟫) k} {f} {F} {Q} →
        F IsExt Q →
        f ∈[ ϱ ] →
        -------------------------------------
        F f ∈[ ϱ ++ᵥ map F ϱ ]

    F-closed {ϱ = ϱ} {f} {F} {Q} isExt f∈[ϱ] = step₁ where

        ϱ′ = map F ϱ
        ϱ′′ = ϱ ++ᵥ ϱ′

        -- witnessing term of f ∈[ ϱ ]
        α : Term′ _
        α = fst (extract _ _ f∈[ϱ])

        α-sound : f ≈ ⟦ α ⟧ᵥ ϱ
        α-sound = snd (extract _ _ f∈[ϱ])
    
        β : Term′ _
        β = fst (extension-lem ϱ isExt α)

        β-sound : F (⟦ α ⟧ᵥ ϱ) ≈ ⟦ β ⟧ᵥ ϱ′′
        β-sound = snd (extension-lem ϱ isExt α)

        αβ-sound : F f ≈ ⟦ β ⟧ᵥ ϱ′′
        αβ-sound =
            begin
                F f
                    ≈⟨ isExt .≈-ext α-sound ⟩
                F (⟦ α ⟧ᵥ ϱ)
                    ≈⟨ β-sound ⟩
                ⟦ β ⟧ᵥ ϱ′′
            ∎ where open EqS

        step₀ : ⟦ β ⟧ᵥ ϱ′′ ∈[ ϱ′′ ]
        step₀ = subalgebraᵥ β

        step₁ :  F f ∈[ ϱ′′ ]
        step₁ = αβ-sound ≈∈ step₀
```

We apply this lemma to show closure under right derivatives,
whenever they satisfy *any* product rule (not necessarily `P`).

```
    δʳ-closed :
        ∀ Q {b} {ϱ : Vec (A ⟪ Σ ⟫) k} {f} →
        (∀ a → δʳ a satisfies Q) →
        f ∈[ ϱ ] →
        ----------------------------------
        δʳ b f ∈[ ϱ ++ᵥ map (δʳ b) ϱ ]
    
    δʳ-closed Q {b} δʳ-sat f∈[ϱ] = F-closed xt f∈[ϱ] where

        xt : (δʳ b) IsExt Q
        xt = record {
            ≈-ext = δʳ-inv b ;
            𝟘-ext = δʳ-end-𝟘 b ; 
            ·-ext = δʳ-end-· b ; 
            +-ext = δʳ-end-+ b ; 
            *-ext = δʳ-sat b }
```

Consequently, `P`-finite series are closed under right derivatives,
whenever the latter satisfy a product rule.
This relies on the fact that left and right derivatives commute.

```
    P-fin-δʳ :
        ∀ Q →
        (∀ a → δʳ a satisfies Q) →
        P-fin f k →
        ∀ b → 
        --------------------------
        P-fin (δʳ b f) (k +ℕ k)

    P-fin-δʳ {f = f} {k = k} Q p-δʳ F b =
        P-fin[ fs ++ᵥ gs , lem1 , lem2 ]
        where

        fs gs : Vec (A ⟪ Σ ⟫) k
        fs = gen F
        gs = map (δʳ b) fs

        lem1 : δʳ b f ∈[ fs ++ᵥ gs ]
        lem1 = δʳ-closed Q p-δʳ (memb F)

        -- g ∈ gs means that g is of the form δʳ b h for some h ∈ fs
        wit : g ∈ gs → ∃[ h ] h ∈ fs × g ≡ δʳ b h
        wit g∈gs = ∈-map⁻ g∈gs

        -- closure under left derivatives of generators
        lem2 : ∀ a {g} → g ∈ fs ++ᵥ gs → δ g a ∈[ fs ++ᵥ gs ]
        lem2 a {g} g∈ with ∈ᵥ-++ {as = fs} g∈
        ... | inj₁ g∈fs = ++-∈ˡ (closed F a g∈fs)
        ... | inj₂ g∈gs = δga∈[fs++gs] where

            h : A ⟪ Σ ⟫
            h = fst (wit g∈gs)

            h∈fs : h ∈ fs
            h∈fs = fst (snd (wit g∈gs))

            g≡δʳbh : g ≡ δʳ b h
            g≡δʳbh = snd (snd (wit g∈gs))

            -- left and right derivatives commute
            δˡg≈δʳδˡh : δ g a ≈ δʳ b (δ h a)
            δˡg≈δʳδˡh =
                begin
                    δ g a
                        ≡⟨ cong (\ f → δ f a) g≡δʳbh ⟩
                    δ (δʳ b h) a
                        ≈⟨⟩
                    δʳ b (δ h a)
                ∎ where open EqS

            δˡh∈[fs] : δ h a ∈[ fs ]
            δˡh∈[fs] = closed F a h∈fs

            δʳδˡh∈[fs++gs] : δʳ b (δ h a) ∈[ fs ++ᵥ gs ]
            δʳδˡh∈[fs++gs] = δʳ-closed Q p-δʳ δˡh∈[fs]

            δga∈[fs++gs] : δ g a ∈[ fs ++ᵥ gs ]
            δga∈[fs++gs] = δˡg≈δʳδˡh ≈∈ δʳδˡh∈[fs++gs]
```
