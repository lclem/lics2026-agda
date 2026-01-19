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
    ϱ : Vec (A ⟪ Σ ⟫) k
    Q : ProductRule
    F : A ⟪ Σ ⟫ → A ⟪ Σ ⟫
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

# Right derivatives, reversal, and product rules {#sec:rev-product_rule}

In this section we study the connection between

- reversal preserving the product operation.
- right derivatives satisfying a product rule.

To this end, we fix a product rule `P` in order to fix the `P`-product operation.

```
module Reversal (P : ProductRule) where

    open Product P
```

We introduce an abbreviation for the property that right derivatives satisfy an arbitrary product rule.

```
    δʳ-satisfies_ : ProductRule → Set
    δʳ-satisfies Q = ∀ a → (δʳ a) satisfies Q
```

## Characterisation {#sec:rev-product_rule-characterisation}

The main result of this section is the following characterisation

```
    rev-end↔δʳ-P : IsEndomorphism rev iff δʳ-satisfies P
```

We prove the two directions separately.

## From reversal to a product rule {#sec:rev-to-product_rule}

We show that if reversal is an endomorphism,
then the right derivatives satisfy the same product rule `P` as left derivatives.

``` 
    rev-end→δʳ-P : IsEndomorphism rev → δʳ-satisfies P
    rev-end→δʳ-P end a f g =
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

## From product rule to reversal {#sec:product_rule-to-rev}

Viceversa, if right derivatives satisfy the same product rule `P` as left derivatives,
then reversal is an endomorphism.

```
    δʳ-P→rev-end : δʳ-satisfies P → IsEndomorphism rev {i}
    δʳ-P→rev-end p-rev = record {
        𝟘-end = rev-end-𝟘;
        ·-end = rev-end-·;
        +-end = rev-end-+;
        *-end = rev-end-*
        } where
```

The additional size parameter `i` is used to enable Agda to witness productivity.

```
        rev-end-* : Endomorphic-* rev
        ν-≈ (rev-end-* f g) = R-refl
        δ-≈ (rev-end-* f g) a =
            begin
                δˡ a (rev (f * g))
                    ≈⟨⟩
                rev (δʳ a (f * g))
                    ≈⟨ rev-cong (p-rev a f g) ⟩
                rev ⟦ P ⟧⟨ f , δʳ a f , g , δʳ a g ⟩
                    ≈⟨ endᵥ P (_ ∷ _ ∷ _ ∷ _ ∷ []) (δʳ-P→rev-end p-rev)⟩
                ⟦ P ⟧⟨ rev f , rev (δʳ a f) , rev g , rev (δʳ a g) ⟩
                    ≈⟨⟩
                ⟦ P ⟧⟨ rev f , δˡ a (rev f) , rev g , δˡ a (rev g) ⟩
                    ≈⟨⟩
                δˡ a (rev f * rev g)
            ∎ where open EqS
```

The proof is concluded by putting together the two directions above.

```
    rev-end↔δʳ-P = rev-end→δʳ-P ,, δʳ-P→rev-end
```

# Unary operators satisfying a product rule {#sec:unary-operators-product-rules}

Let `F` be a unary operator on series and let `Q` be a product rule.
If `F` is a `Q`-extension, then we can extend the product rule to arbitrary terms.

```
    ext-lem :
        ∀ ϱ →
        F IsExt Q →
        (u : Term′ k) →
        -------------------------------------------
        ∃[ v ] F (⟦ u ⟧ᵥ ϱ) ≈ ⟦ v ⟧ᵥ (ϱ ++ᵥ map F ϱ)
```

In order to prove the lemma,
we will to introduce some auxiliary notions.

## Primed variables

We begin by defining a facility to extend variables and terms.
If `x` is a variable belonging to a set of `k` variables,
then `x ′` is a (right) copy of `x` in a set of `ℓ + k` variables.

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

## Extended terms

We allow variables to appear in larger sets of variables,
by keeping the same index but in a larger finite set.
Thus if `x` is a variable in a set of `k` variables,
then `′-var x` is the same variable in a set of `k + ℓ` variables. 

```
    ′-var : Var k → Var (k +ℕ ℓ)
    ′-var {ℓ = ℓ} x = x ↑ˡ ℓ
```

The following is the crucial property of `′-var x`.

```
    ′-var-lem :
        ∀ (x : Var k) ϱ (η : Vec (A ⟪ Σ ⟫) ℓ) →
        --------------------------------------------
        ⟦ var x ⟧ᵥ ϱ ≈ ⟦ var (′-var x) ⟧ᵥ (ϱ ++ᵥ η)

    ′-var-lem zero ϱ η =
        begin
            lookup ϱ zero
                ≡⟨ lookup-zero-++ ϱ η ⟩
            lookup (ϱ ++ᵥ η) zero
        ∎ where open EqS
        
    ′-var-lem (suc x) (_ ∷ ϱ) η = ′-var-lem x ϱ η
```

We extend this operation to all terms.

```
    infix 30 ′_
    ′_ : Term′ k → Term′ (k +ℕ k)
    ′ 0T = 0T
    ′ (var x) = var (′-var x)
    ′ (c [·] u) = c [·] ′ u
    ′ (u [+] v) = ′ u [+] ′ v
    ′ (u [*] v) = ′ u [*] ′ v
```

The crucial property is that the semantics of the extended term (in any environment extension)
equals the semantics of the original one.

```
    ′-lem :
        ∀ (u : Term′ k) ϱ η →
        ------------------------------
        ⟦ u ⟧ᵥ ϱ ≈ ⟦ ′ u ⟧ᵥ (ϱ ++ᵥ η)

    ′-lem 0T ϱ η = ≈-refl

    ′-lem (var x) ϱ η = ′-var-lem x ϱ η

    ′-lem (c [·] u) ϱ η
        with ′-lem u ϱ η
    ... | ass = R-refl ·≈ ass

    ′-lem (u [+] v) ϱ η
        with ′-lem u ϱ η | ′-lem v ϱ η
    ... | ass-u | ass-v = ass-u +≈ ass-v

    ′-lem (u [*] v) ϱ η
        with ′-lem u ϱ η | ′-lem v ϱ η
    ... | ass-u | ass-v = ass-u *≈ ass-v
```

## `Q`-extensions

We are finally ready to prove `ext-lem`.

```   
    ext-lem ϱ isExt 0T = 0T ,, isExt .𝟘-ext

    ext-lem ϱ isExt (var x) = var (x ′) ,, prime-lemma x _ ϱ

    ext-lem {F = F} ϱ isExt (c [·] u)
        with ext-lem ϱ isExt u
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

    ext-lem {F = F} ϱ isExt (u [+] v)
        with ext-lem ϱ isExt u | ext-lem ϱ isExt v
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

    ext-lem {F = F} {Q} ϱ isExt (u [*] v)
        with ext-lem ϱ isExt u | ext-lem ϱ isExt v
    ... | u′ ,, ass-u | v′ ,, ass-v
        = [ Q ]⟨ ′ u , u′ , ′ v , v′ ⟩ ,, it where

        η = ϱ ++ᵥ map F ϱ

        ext-u = ′-lem u ϱ (map F ϱ)
        ext-v = ′-lem v ϱ (map F ϱ)

        it = begin
            F (⟦ u [*] v ⟧ᵥ ϱ)
                ≈⟨⟩
            F (⟦ u ⟧ᵥ ϱ * ⟦ v ⟧ᵥ ϱ)
                ≈⟨ isExt .*-ext _ _ ⟩
            ⟦ Q ⟧⟨ ⟦ u ⟧ᵥ ϱ , F (⟦ u ⟧ᵥ ϱ) , ⟦ v ⟧ᵥ ϱ , F (⟦ v ⟧ᵥ ϱ) ⟩
                ≈⟨ ⟦ Q ⟧≈ᵥ [ ext-u , ass-u , ext-v , ass-v ] ⟩
            ⟦ Q ⟧⟨ ⟦ ′ u ⟧ᵥ η , ⟦ u′ ⟧ᵥ η , ⟦ ′ v ⟧ᵥ η , ⟦ v′ ⟧ᵥ η ⟩
                ≈⟨ eval-substᵥ Q {_ ∷ _ ∷ _ ∷ _ ∷ []} ⟨
            ⟦ [ Q ]⟨ ′ u , u′ , ′ v , v′ ⟩ ⟧ᵥ η
            ∎ where open EqS
```

# Closure under right derivatives

We show that if right derivatives satisfy *any* product rule (not necessarily `P`),
then `P`-finite series are closed under right derivatives.

In particular, by the [previous section](#sec:rev-to-product_rule) this is the case when reversal is an endomorphism.

```
    open import Data.Product.Base using (∃; ∃-syntax; _,_)
    open import Data.Product using (_×_)
    open import Preliminaries.Vector
    open import General.FinitelyGenerated R Σ P
```

## General case

We begin with a general lemma, showing that if `F` is a `Q`-extension
and `f` is generated by `ϱ`,
then `F f` is generated by the same set together with their images under `F`.

```
    F-closed :
        F IsExt Q →
        f ∈[ ϱ ] →
        -------------------------------------
        F f ∈[ ϱ ++ᵥ map F ϱ ]
```

The proof uses `ext-lem` from the [previous section](#sec:unary-operators-product-rules).

```
    F-closed {F = F} {Q = Q} {f = f} {ϱ = ϱ} isExt f∈[ϱ] = step₁ where

        ϱ′ = map F ϱ
        ϱ′′ = ϱ ++ᵥ ϱ′

        -- witnessing term of f ∈[ ϱ ]
        α-all = extract _ _ f∈[ϱ]

        α : Term′ _
        α = fst α-all

        α-sound : f ≈ ⟦ α ⟧ᵥ ϱ
        α-sound = snd α-all
    
        β-all = ext-lem ϱ isExt α

        β : Term′ _
        β = fst β-all

        β-sound : F (⟦ α ⟧ᵥ ϱ) ≈ ⟦ β ⟧ᵥ ϱ′′
        β-sound = snd β-all

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

## Right derivatives {#sec:closure-right-derivatives}

We apply `F-closed` to show closure under right derivatives,
whenever they satisfy *any* product rule `Q` (not necessarily `P`).

```
    δʳ-closed :
        ∀ Q b →
        δʳ-satisfies Q →
        f ∈[ ϱ ] →
        ----------------------------------
        δʳ b f ∈[ ϱ ++ᵥ map (δʳ b) ϱ ]
```

The proof is just an application of `F-closed` with `F = δʳ b`.

```
    δʳ-closed Q b δʳ-sat f∈[ϱ] = F-closed xt f∈[ϱ] where

        xt : (δʳ b) IsExt Q
        xt = record {
            ≈-ext = δʳ-inv b ;
            𝟘-ext = δʳ-end-𝟘 b ; 
            ·-ext = δʳ-end-· b ; 
            +-ext = δʳ-end-+ b ; 
            *-ext = δʳ-sat b }
```

## `P`-finiteness {#sec:right-derivatives-P-fin}

Consequently, `P`-finite series are closed under right derivatives,
whenever the latter satisfy any product rule `Q`.
For instance, this is the case when reversal is an endomorphism.
This relies on the fact that left and right derivatives commute.

```
    P-fin-δʳ :
        ∀ Q →
        δʳ-satisfies Q →
        P-fin f k →
        ∀ b →
        -----------------------
        P-fin (δʳ b f) (k +ℕ k)
```

The proof proceeds as follows.
Let `fs` be the generators for `f`, and let `gs` be their right derivative.
Then the right derivative of `f` is generated by `fs ++ᵥ gs`.

```
    P-fin-δʳ {f = f} {k = k} Q p-δʳ F b =
        P-fin[ fs ++ᵥ gs , lem1 , lem2 ]
        where

        fs gs : Vec (A ⟪ Σ ⟫) k
        fs = gen F
        gs = map (δʳ b) fs

        lem1 : δʳ b f ∈[ fs ++ᵥ gs ]
        lem1 = δʳ-closed Q b p-δʳ (memb F)

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
            δʳδˡh∈[fs++gs] = δʳ-closed Q b p-δʳ δˡh∈[fs]

            δga∈[fs++gs] : δ g a ∈[ fs ++ᵥ gs ]
            δga∈[fs++gs] = δˡg≈δʳδˡh ≈∈ δʳδˡh∈[fs++gs]
```

## Putting it all together {#sec:rev-end-right-derivatives-P-fin}

By combining all the results above,
we have that if reversal is an endomorphism,
then `P`-finite series are closed under right derivatives.

Formally, we have the following

```
    rev-end→P-fin :
        IsEndomorphism rev →
        P-fin f k →
        ∀ b →
        -----------------------
        P-fin (δʳ b f) (k +ℕ k)
    
    rev-end→P-fin rev-end f-P-fin b =
        P-fin-δʳ P (rev-end→δʳ-P rev-end) f-P-fin b
```
