---
title: Products of power series
---

In this section we define products of formal series obeying a product rule.
Our development is parametrised by a commutative ring `R` and an input alphabet `Σ`.

```
{-# OPTIONS --guardedness --sized-types #-}

open import Preliminaries.Base
module General.Products (R : CommutativeRing) (Σ : Set) where

open import Size
open import Preliminaries.Algebra R
open import Preliminaries.Vector

open import General.Series R Σ hiding (≡→≈)

-- we need to rename term constructors to avoid name clashes
-- with the corresponding series operations
open import General.Terms R
    renaming (_+_ to _[+]_; _*_ to _[*]_; _·_ to _[·]_)

open import General.ProductRules R

private variable
    i : Size
    m n : ℕ
    X Y : Set
```

# `P`-products

Let `P` be a product rule.
We define a *`P`-product* of formal series as the unique binary operation satisfying the product rule `P`.

```
module Product (P : ProductRule) where
```

We simultaneously define the product `_*_`
and the semantics of terms over series.
This is necessary since we need to capture arbitrary product rules.

```
    infixr 7 _*_
    _*_ : A ⟪ Σ ⟫ i → A ⟪ Σ ⟫ i → A ⟪ Σ ⟫ i
    ⟦_⟧_ : Term X → SEnv {i} X → A ⟪ Σ ⟫ i
```

To make the case of the product rule more readable,
we introduce a special notation for the semantics of terms with four variables

```
    ⟦_⟧⟨_,_,_,_⟩ : Term′ 4 → A ⟪ Σ ⟫ i → A ⟪ Σ ⟫ i → A ⟪ Σ ⟫ i → A ⟪ Σ ⟫ i → A ⟪ Σ ⟫ i
```

The `P`-product `f * g` of two series `f ` and `g` is defined coinductively as follows.

- At the constant term, it is just the product of constant terms.
- The left derivative of a product is obtained by evaluating the product rule `P` on the input series and their derivatives.

```
    ν (f * g) = ν f *R ν g
    δ (f * g) a = ⟦ P ⟧⟨ f , δ f a , g , δ g a ⟩
```

The semantics `⟦ u ⟧ ϱ` of a term `u` over a series environment `ϱ` is defined by structural induction on terms.
In the last case, the definition depends on the product of series.

```
    ⟦ 0T ⟧ ϱ = 𝟘
    ⟦ c [·] u ⟧ ϱ = c · ⟦ u ⟧ ϱ
    ⟦ var x ⟧ ϱ = ϱ x
    ⟦ u [+] v ⟧ ϱ = ⟦ u ⟧ ϱ + ⟦ v ⟧ ϱ
    ⟦ u [*] v ⟧ ϱ = ⟦ u ⟧ ϱ * ⟦ v ⟧ ϱ
```

We also define the semantics of terms with `n` variables, together with a special syntax.

```
    ⟦_⟧ᵥ_ : ∀ {n} → Term′ n → SEnvᵥ {i} n → A ⟪ Σ ⟫ i
    ⟦ p ⟧ᵥ fs = ⟦ p ⟧ (lookup fs)

    ⟦ p ⟧⟨ f₀ , f₁ , f₂ , f₃ ⟩ = ⟦ p ⟧ᵥ (f₀ ∷ f₁ ∷ f₂ ∷ f₃ ∷ [])
```

It will also be convenient to have a special syntax for six variables.

```
    ⟦_⟧⟨_,_,_,_,_,_⟩ : Term′ 6 → A ⟪ Σ ⟫ i → A ⟪ Σ ⟫ i → A ⟪ Σ ⟫ i →
        A ⟪ Σ ⟫ i → A ⟪ Σ ⟫ i → A ⟪ Σ ⟫ i → A ⟪ Σ ⟫ i
    ⟦ p ⟧⟨ f₀ , f₁ , f₂ , f₃ , f₄ , f₅ ⟩ = ⟦ p ⟧ᵥ (f₀ ∷ f₁ ∷ f₂ ∷ f₃ ∷ f₄ ∷ f₅ ∷ [])
```

# `Q`-extensions

For future use, we formalise what it means for a unary operation `F` on series (such as left derivatives)
to *satisfy* a product rule `Q`.

```
    infix 10 _satisfies_
    _satisfies_ : (A ⟪ Σ ⟫ → A ⟪ Σ ⟫) → ProductRule → Set
    F satisfies Q = ∀ (f g : A ⟪ Σ ⟫) → F (f * g) ≈ ⟦ Q ⟧⟨ f , F f , g , F g ⟩
```

A *`Q`-extension* is a linear endofunction on series
that respects equivalence of series and satisfies the product rule `Q`.

```
    infix 10 _IsExt_
    record _IsExt_ (F : A ⟪ Σ ⟫ → A ⟪ Σ ⟫) (Q : ProductRule) : Set where
        field
            ≈-ext : ≈-Invariance F
            𝟘-ext : Endomorphic-𝟘 F
            ·-ext : Endomorphic-· F
            +-ext : Endomorphic-+ F
            *-ext : F satisfies Q

    open _IsExt_ public
```

This is designed so that, by definition,
left derivatives are `P`-extensions.

```
    δˡ-sat-P : ∀ a → (δˡ a) satisfies P
    δˡ-sat-P a f g = ≈-refl

    δˡ-ext : ∀ a → (δˡ a) IsExt P
    δˡ-ext a = record {
        ≈-ext = \ x → δ-≈ x a ;
        𝟘-ext = δˡ-end-𝟘 a ;
        ·-ext = δˡ-end-· a ;
        +-ext = δˡ-end-+ a ;
        *-ext = δˡ-sat-P a
        }
```

# Invariance

We show that the product and, more generally, the semantics of terms resepects equivalence of series.
Again, we need a mutual corecursion.

```
    infix 20 _*≈_
    _*≈_ *-cong : Congruent₂ (λ f g → f ≈[ i ] g) _*_
    *-cong = _*≈_

    infix 30 ⟦_⟧≈_ sem-cong
    ⟦_⟧≈_ :
        ∀ {ϱ₀ ϱ₁ : SEnv X} (p : Term X) →
        ϱ₀ ≈ϱ[ i ] ϱ₁ →
        ---------------------------------
        ⟦ p ⟧ ϱ₀ ≈[ i ] ⟦ p ⟧ ϱ₁

    sem-cong = ⟦_⟧≈_
```

We use a convenient syntax for terms with finitely many variables.

```
    infix 30 ⟦_⟧≈ᵥ_
    ⟦_⟧≈ᵥ_ :
        ∀ {fs gs : SEnvᵥ n} (p : Term′ n) →
        fs ≈ᵥ[ i ] gs →
        -----------------------------------
        ⟦ p ⟧ᵥ fs ≈[ i ] ⟦ p ⟧ᵥ gs
```

We begin with invariance of the product.
In the base case, we use invariance of the underlying ring multiplication.
In the coinductive case, 

```
    ν-≈ (f≈g *≈ h≈i) = *R-cong (ν-≈ f≈g) (ν-≈ h≈i)
    δ-≈ (f≈g *≈ h≈i) a = ⟦ P ⟧≈ᵥ [ f≈g , δ-≈ f≈g a , h≈i , δ-≈ h≈i a ]
```

Invariance of the semantics of terms is proved by structural induction,
where the case of product refers to the above.
        
```
    ⟦ 0T ⟧≈ _ = ≈-refl
    ⟦ var x ⟧≈ ϱ₀≈ϱ₁ = ϱ₀≈ϱ₁ x
    ⟦ c [·] p ⟧≈ ϱ₀≈ϱ₁ = R-refl ·≈ (⟦ p ⟧≈ ϱ₀≈ϱ₁)
    ⟦ p [+] q ⟧≈ ϱ₀≈ϱ₁ = ⟦ p ⟧≈ ϱ₀≈ϱ₁ +≈ ⟦ q ⟧≈ ϱ₀≈ϱ₁
    ⟦ p [*] q ⟧≈ ϱ₀≈ϱ₁ = ⟦ p ⟧≈ ϱ₀≈ϱ₁ *≈ ⟦ q ⟧≈ ϱ₀≈ϱ₁
```

The definition is concluded by the case of finitely-many variables.

```     
    ⟦ p ⟧≈ᵥ fs≈gs = ⟦ p ⟧≈ build-≈ϱ fs≈gs
```

# `nu` is a homomorphism {#lem:constant-term-homomorphism-lemma}

```
    open Semantics
        -- we need to rename term semantics operations
        -- to avoid name clashes
        renaming (⟦_⟧_ to T⟦_⟧_; ⟦_⟧ᵥ_ to T⟦_⟧ᵥ_; ⟦_⟧≈_ to T⟦_⟧≈_)
```

We show that the operation of constant term extraction `ν` is a homomorphism
from the series algebra to the underlying ring `R`.

```
    ν-hom :
        ∀ (p : Term X) (ϱ : SEnv X) →
        -----------------------------
        ν (⟦ p ⟧ ϱ) ≈R T⟦ p ⟧ (ν ∘ ϱ)
```

The proof is by structural induction on terms.

```   
    ν-hom 0T ϱ = R-refl
    ν-hom (var x) ϱ = R-refl
    ν-hom (c [·] q) ϱ = R-refl ⟨ *R-cong ⟩ ν-hom q ϱ
    ν-hom (p [+] q) ϱ = ν-hom p ϱ ⟨ +R-cong ⟩ ν-hom q ϱ
    ν-hom (p [*] q) ϱ = ν-hom p ϱ ⟨ *R-cong ⟩ ν-hom q ϱ
```

We state a corresponding lemma for terms over finitely many variables.
Its proof is by reduction to `ν-hom`.

```
    ν-homᵥ :
        ∀ (p : Term′ n) (ϱ : SEnvᵥ n) →
        -------------------------------
        ν (⟦ p ⟧ᵥ ϱ) ≈R T⟦ p ⟧ᵥ (map ν ϱ)

    ν-homᵥ p ϱ =
        begin
            ν (⟦ p ⟧ᵥ ϱ)
                ≈⟨ ν-hom p (lookup ϱ) ⟩
            T⟦ p ⟧ (ν ∘ lookup ϱ)
                ≈⟨ T⟦ p ⟧≈ (λ x → ≡→≈ $ sym $ lookup-map ν ϱ x) ⟩
            T⟦ p ⟧ (lookup $ map ν ϱ)
                ≈⟨⟩
            T⟦ p ⟧ᵥ (map ν ϱ)
        ∎ where open EqR
```

# Substitution and evaluation

If we have a term `p` over variables `X`, a substitution from `X` to terms over `Y`,
and a series environment `env` over `Y`, we can either

- substitute and evaluate, obtaining `⟦ subst ϱ p ⟧ env `, or
- evaluate in an updated environment, obtaining ⟦ p ⟧ (⟦_⟧ env ∘ ϱ).

These two operations produce the same result.

```
    eval-subst :
        ∀ (p : Term X) {ϱ : Subst X Y} {env : SEnv Y} →
        -----------------------------------------------
        ⟦ subst ϱ p ⟧ env ≈ ⟦ p ⟧ (⟦_⟧ env ∘ ϱ)
```

The proof is by structural induction on terms,
relying on invariance properties of series operations.

```
    eval-subst 0T = ≈-refl
    eval-subst (var x) = ≈-refl
    eval-subst (c [·] q) = R-refl ·≈ eval-subst q
    eval-subst (p [+] q) = eval-subst p +≈ eval-subst q
    eval-subst (p [*] q) = eval-subst p *≈ eval-subst q
```

We find it convenient to state a finite variable version of `eval-subst`,
which is proved by reduction to the latter.

```
    eval-substᵥ :
        ∀ (p : Term′ m) {qs : Substᵥ m X} {fs : SEnv X} →
        -------------------------------------------------
        ⟦ substᵥ qs p ⟧ fs ≈ ⟦ p ⟧ᵥ (map (⟦_⟧ fs) qs)

    eval-substᵥ p {qs} {fs} =
        begin
            ⟦ substᵥ qs p ⟧ fs 
                ≈⟨⟩
            ⟦ subst (lookup qs) p ⟧ fs 
                ≈⟨ eval-subst p {ϱ = lookup qs} {env = fs} ⟩
            ⟦ p ⟧ (λ x → ⟦ lookup qs x ⟧ fs)
                ≈⟨ ⟦ p ⟧≈ (≡→≈ϱ (lookup-map _ qs)) ⟨
            ⟦ p ⟧ (lookup (map (⟦_⟧ fs) qs))
                ≈⟨⟩
            ⟦ p ⟧ᵥ (map (λ q → ⟦ q ⟧ fs) qs)
        ∎ where open EqS
```

# Endomorphism lemma

We define what it means for an endofunction on series `F : A ⟪ Σ ⟫ → A ⟪ Σ ⟫`  to be an endomorphism.
Informally, this means that `F` respects the series operations.

```
    open Properties

    Endomorphic-* : (F : A ⟪ Σ ⟫ → A ⟪ Σ ⟫) {i : Size} → Set
    Endomorphic-* F {i} = ∀ f g → F (f * g) ≈[ i ] F f * F g

    record IsEndomorphism (F : A ⟪ Σ ⟫ → A ⟪ Σ ⟫) {i : Size} : Set where
        field
            ·-end : Endomorphic-· F
            +-end : Endomorphic-+ F
            𝟘-end : Endomorphic-𝟘 F
            *-end : Endomorphic-* F {i}

    open IsEndomorphism public

    private variable F : A ⟪ Σ ⟫ → A ⟪ Σ ⟫
```

We can then show that endomorphisms `F` commute with the semantics of terms. 

```
    end :
        ∀ (p : Term X) {ϱ : SEnv X} →
        IsEndomorphism F {i} →
        -------------------------------
        F (⟦ p ⟧ ϱ) ≈[ i ] ⟦ p ⟧ (F ∘ ϱ)
```

The proof is by structural induction on terms.

```
    end 0T endF = endF .𝟘-end

    end (var x) _ = ≈-refl

    end {F = F} (c [·] p) {ϱ} endF =
        begin
            F (⟦ c [·] p ⟧ ϱ)
                ≈⟨⟩
            F (c · ⟦ p ⟧ ϱ)
                ≈⟨ ·-end endF _ _ ⟩
            c · F (⟦ p ⟧ ϱ)
                ≈⟨ R-refl ·≈ end p endF ⟩
            c · ⟦ p ⟧ (F ∘ ϱ)
                ≈⟨⟩
            ⟦ c [·] p ⟧ (F ∘ ϱ)
        ∎ where open EqS

    end {F = F} (p [+] q) {ϱ} endF =
        begin
            F (⟦ p [+] q ⟧ ϱ)
                ≈⟨⟩
            F (⟦ p ⟧ ϱ + ⟦ q ⟧ ϱ)
                ≈⟨ +-end endF _ _ ⟩
            F (⟦ p ⟧ ϱ) + F (⟦ q ⟧ ϱ)
                ≈⟨ end p endF +≈ end q endF ⟩
            (⟦ p ⟧ (F ∘ ϱ)) + (⟦ q ⟧ (F ∘ ϱ))
                ≈⟨⟩
            ⟦ p [+] q ⟧ (F ∘ ϱ)
        ∎ where open EqS

    end {F = F} (p [*] q) {ϱ} endF =
        begin
            F (⟦ p [*] q ⟧ ϱ)
                ≈⟨⟩
            F (⟦ p ⟧ ϱ * ⟦ q ⟧ ϱ)
                ≈⟨ *-end endF _ _ ⟩
            F (⟦ p ⟧ ϱ) * F (⟦ q ⟧ ϱ)
                ≈⟨ end p endF *≈ end q endF ⟩
            (⟦ p ⟧ (F ∘ ϱ)) * (⟦ q ⟧ (F ∘ ϱ))
                ≈⟨⟩
            ⟦ p [*] q ⟧ (F ∘ ϱ)
        ∎ where open EqS
```

We state a corresponding finite-variable version,
which is proved by reduction to `end`.

```
    endᵥ :
        ∀ (p : Term′ n) (ϱ : SEnvᵥ n) →
        IsEndomorphism F {i} →
        -----------------------------------
        F (⟦ p ⟧ᵥ ϱ) ≈[ i ] ⟦ p ⟧ᵥ (map F ϱ)

    endᵥ {F = F} p ϱ endF =
        begin
            F (⟦ p ⟧ᵥ ϱ)
                ≈⟨⟩
            F (⟦ p ⟧ (lookup ϱ))
                ≈⟨ end p endF ⟩
            ⟦ p ⟧ (F ∘ (lookup ϱ))
                ≈⟨ ⟦ p ⟧≈ (≡→≈ϱ (lookup-map F ϱ)) ⟨
            ⟦ p ⟧ (lookup (map F ϱ))
                ≈⟨⟩
            ⟦ p ⟧ᵥ (map F ϱ)
        ∎ where open EqS
```

# Examples

```
open Examples Σ
```

In this section we instantiate the above development to the three [example product rules](../ProductRules/\#sec:product-rules-examples)
for the Hadamard, shuffle, and infiltration products,
and show that we recover the corresponding products.

## Hadamard product

```
module Hadamard where

    open Product ruleHadamard

    agree : ∀ (f g : A ⟪ Σ ⟫) → f * g ≈[ i ] f ⊙ g
    ν-≈ (agree f g) = R-refl
    δ-≈ (agree f g) a =
        begin
            δ (f * g) a ≈⟨⟩
            δ f a * δ g a ≈⟨ agree _ _ ⟩
            δ f a ⊙ δ g a ≈⟨⟩
            δ (f ⊙ g) a
        ∎ where open EqS            
```

## Shuffle product

```
module Shuffle where

    open Product ruleShuffle

    agree : ∀ (f g : A ⟪ Σ ⟫) → f * g ≈[ i ] f ⧢ g
    ν-≈ (agree f g) = R-refl
    δ-≈ (agree f g) a =
        begin
            δ (f * g) a ≈⟨⟩
            δ f a * g + f * δ g a ≈⟨ agree _ _ ⟨ +-cong ⟩ agree _ _ ⟩
            δ f a ⧢ g + f ⧢ δ g a ≈⟨⟩
            δ (f ⧢ g) a
        ∎ where open EqS   
```

## Infiltration product

```
module Infiltration where

    open Product ruleInfiltration

    agree : ∀ (f g : A ⟪ Σ ⟫) → f * g ≈[ i ] f ↑ g
    ν-≈ (agree f g) = R-refl
    δ-≈ (agree f g) a =
        begin
            δ (f * g) a
                ≈⟨⟩
            δ f a * g + f * δ g a + δ f a * δ g a
                ≈⟨ +-cong₃ (agree _ _) (agree _ _) (agree _ _) ⟩
            δ f a ↑ g + f ↑ δ g a + δ f a ↑ δ g a
                ≈⟨⟩
            δ (f ↑ g) a
        ∎ where open EqS   
```
