---
title: "Terms"
---

In this section we define the syntax of terms and their semantics.

```
{-# OPTIONS --guardedness --sized-types #-}
{-# OPTIONS --backtracking-instance-search --instance-search-depth 1 #-}

open import Preliminaries.Base
module General.Terms (R : CommutativeRing) where
open import Preliminaries.Algebra R
```

# Terms {#sec:terms}

Let `X` be the type of variables.
Recall that `A` is the carrier set of the commutative ring `R`.
We define the type `Term X` of terms over `X`.
A *term over `X`* is either

- the zero term `0T`,
- a variable `var x` for `x : X`,
- a scalar multiplication `c · u` for `c : A` and `u : Term X`,
- a sum `u + v` for `u v : Term X`, or
- a product `u * v` for `u v : Term X`.

This is formalised as follows.

```
module Terms (X : Set) where

  infixr 9 _+_
  infixr 10 _*_ _·_

  data Term : Set where
    0T : Term
    var : (x : X) → Term
    _·_ : (c : A) (u : Term) → Term
    _+_ _*_ : (u v : Term) → Term

open Terms public

private variable
  X Y Z : Set
```

Note that we do not allow constant terms of the form `con c` for `c : A`.
Therefore, terms have no "constant coefficient"
and the only way to introduce coefficients in terms is via scalar multiplication.

We define additive inverses as a convenient syntactic sugar.

```
infix 3 -_
-_ : Term X → Term X
- p = (-R 1R) · p

infixl 9 _-_
_-_ : Term X → Term X → Term X
p - q = p + (- q)
```

## Term substitutions

A *term substitution* from `X` to `Y` is a function mapping every variable from `X` to a term over `Y`.

```
Subst : Set → Set → Set
Subst X Y = X → Term Y
```

We can apply a substitution to a term over `X`, obtaining a term over `Y`.

```
subst : Subst X Y → Term X → Term Y
subst ϱ 0T = 0T
subst ϱ (var x) = ϱ x
subst ϱ (c · p) = c · subst ϱ p
subst ϱ (p + q) = subst ϱ p + subst ϱ q
subst ϱ (p * q) = subst ϱ p * subst ϱ q
```

If two substitutions are pointwise equal, then their application to a term are equal as well.

```
subst-≡ :
  ∀ p (ϱ₀ ϱ₁ : Subst X Y) →
  (∀ x → ϱ₀ x ≡ ϱ₁ x) →
  -------------------------
  subst ϱ₀ p ≡ subst ϱ₁ p

subst-≡ 0T ϱ₀ ϱ₁ ϱ≡ϱ′ = refl
subst-≡ (var x) ϱ₀ ϱ₁ ϱ≡ϱ′ = ϱ≡ϱ′ x
subst-≡ (c · q) ϱ₀ ϱ₁ ϱ≡ϱ′
  rewrite subst-≡ q ϱ₀ ϱ₁ ϱ≡ϱ′ = refl
subst-≡ (p + q) ϱ₀ ϱ₁ ϱ≡ϱ′
  rewrite subst-≡ p ϱ₀ ϱ₁ ϱ≡ϱ′ | subst-≡ q ϱ₀ ϱ₁ ϱ≡ϱ′ = refl
subst-≡ (p * q) ϱ₀ ϱ₁ ϱ≡ϱ′
  rewrite subst-≡ p ϱ₀ ϱ₁ ϱ≡ϱ′ | subst-≡ q ϱ₀ ϱ₁ ϱ≡ϱ′ = refl
```

We can compose substitutions.

```
subst-subst :
  ∀ p (ϱ₀ : Subst X Y) (ϱ₁ : Subst Y Z) →
  -----------------------------------------------
  subst ϱ₁ (subst ϱ₀ p) ≡ subst (subst ϱ₁ ∘ ϱ₀) p

subst-subst 0T _ _ = refl
subst-subst (var x) _ _ = refl
subst-subst (c · p) ϱ₀ ϱ₁ = cong (_·_ c) (subst-subst p ϱ₀ ϱ₁)
subst-subst (p + q) ϱ₀ ϱ₁ = cong₂ _+_ (subst-subst p ϱ₀ ϱ₁) (subst-subst q ϱ₀ ϱ₁)
subst-subst (p * q) ϱ₀ ϱ₁ = cong₂ _*_ (subst-subst p ϱ₀ ϱ₁) (subst-subst q ϱ₀ ϱ₁)
```

## Terms with finitely many variables

Sometimes we will work with terms with finitely many variables.
To this end, let `Var` be the type of finite sets
and, for a natural number `m : ℕ`,
let `Term′ m` be the type of terms with variables from `Var m`.

```
Var = Fin

Term′ : (m : ℕ) → Set
Term′ m = Term (Var m)
```

Let `m : ℕ` be the number of variables.
A *finite substitution* (or *vector substitution*) a vector of terms over `X` of length `m`.

```
open import Preliminaries.Vector
private variable m n k : ℕ

Substᵥ : ℕ → Set → Set
Substᵥ m X = Vec (Term X) m
```

We can apply a finite substitution to a term with `m` variables, obtaining a term over `X`.
The definion relies on the previous definition of `subst`.

```
substᵥ : Substᵥ n X → Term′ n → Term X
substᵥ ϱ p = subst (lookup ϱ) p
```

We introduce a convenient notation for applying finite substitutions.

```
[_]ᵥ_ : Term′ n → Substᵥ n X → Term X
[ p ]ᵥ ϱ = substᵥ ϱ p
```

We can compose a substitution with a finite one.

```
subst-substᵥ :
  ∀ p (ϱ₀ : Substᵥ m X) (ϱ₁ : Subst X Y) →
  -------------------------------------------------------
  subst ϱ₁ (substᵥ ϱ₀ p) ≡ substᵥ (map (subst ϱ₁) ϱ₀) p

subst-substᵥ p ϱ₀ ϱ₁ = 
  subst ϱ₁ (substᵥ ϱ₀ p)
    ≡⟨⟩
  subst ϱ₁ (subst (lookup ϱ₀) p)
    ≡⟨ subst-subst p (lookup ϱ₀) ϱ₁ ⟩
  subst (subst ϱ₁ ∘ lookup ϱ₀) p
    ≡⟨ subst-≡ p _ _ (lookup-map (subst ϱ₁) ϱ₀) ⟨
  subst (lookup (map (subst ϱ₁) ϱ₀)) p
    ≡⟨⟩
  substᵥ (map (subst ϱ₁) ϱ₀) p
  ∎ where open ≡-Eq
```

As a special (useful) case, we can compose two finite substitutions.

```
substᵥ-substᵥ :
  ∀ p (ϱ₀ : Substᵥ m (Var n)) (ϱ₁ : Substᵥ n X) →
  -------------------------------------------------------
  substᵥ ϱ₁ (substᵥ ϱ₀ p) ≡ substᵥ (map (substᵥ ϱ₁) ϱ₀) p

substᵥ-substᵥ p ϱ₀ ϱ₁ = subst-substᵥ p ϱ₀ (lookup ϱ₁)
```

```
private variable
    ϱ η : Substᵥ n X

infix 4 _≡ᵥ_
infixr 5 _∷-≡_
data _≡ᵥ_ {X : Set} : ∀ {m : ℕ} → (ϱ η : Substᵥ m X) → Set where
    []-≡ : [] ≡ᵥ []
    _∷-≡_ : ∀ {p q} (p≡q : p ≡ q) (ϱ≡η : ϱ ≡ᵥ η) → (p ∷ ϱ) ≡ᵥ (q ∷ η)
```

We introduce convenient notations for finite substitutions of certain fixed lengths.

```
infix 101 [_]⟨_,_,_,_⟩
[_]⟨_,_,_,_⟩ : Term′ 4 → Term X → Term X → Term X → Term X → Term X
[ p ]⟨ p0 , p1 , p2 , p3 ⟩ =
  substᵥ (p0 ∷ p1 ∷ p2 ∷ p3 ∷ []) p 

infix 101 [_]⟨_,_,_,_,_⟩
[_]⟨_,_,_,_,_⟩ : Term′ 5 → Term X → Term X → Term X → Term X → Term X → Term X
[ p ]⟨ p0 , p1 , p2 , p3 , p4 ⟩ =
  substᵥ (p0 ∷ p1 ∷ p2 ∷ p3 ∷ p4 ∷ []) p

infix 101 [_]⟨_,_,_,_,_,_⟩
[_]⟨_,_,_,_,_,_⟩ : Term′ 6 → Term X → Term X → Term X → Term X → Term X → Term X → Term X
[ p ]⟨ p0 , p1 , p2 , p3 , p4 , p5 ⟩ =
  substᵥ (p0 ∷ p1 ∷ p2 ∷ p3 ∷ p4 ∷ p5 ∷ []) p
```

## Variables

We define a simple facility `mkVar m : PE n` for constructing the `m`-th variable of type `PE n`.
We use instance arguments to automatically construct a proof that `m < n`.

```
open import Data.Nat.Properties

<-forward : m < n → m < suc n
<-forward m<n = m<n⇒m<1+n m<n

<-sucn : 0 < suc n
<-sucn = s≤s z≤n

<-back : suc m < n → m < n
<-back (s≤s sm≤n) = <-forward sm≤n

instance

  m<sucm+n : ∀ {m n} → m < suc m +ℕ n
  m<sucm+n {zero} {n} =  <-sucn
  m<sucm+n {suc m} {n} = s≤s m<sucm+n

mkVar : ∀ (m : ℕ) → ⦃ m < n ⦄ → Term′ n
mkVar _ ⦃ m<n ⦄ = var (fromℕ< m<n)
```

In this way we define some commonly used variables.

```
x : Term′ (1 +ℕ n)
x  = mkVar 0

x′ : Term′ (2 +ℕ n)
x′ = mkVar 1

y : Term′ (3 +ℕ n)
y  = mkVar 2

y′ :  Term′ (4 +ℕ n)
y′ = mkVar 3

z : Term′ (5 +ℕ n)
z  = mkVar 4

z′ :  Term′ (6 +ℕ n)
z′ = mkVar 5

t :  Term′ (7 +ℕ n)
t = mkVar 6
```

# Semantics

An environment `ϱ : Env X` is a function mapping variables from `X` to coefficients from `A`.

```
module Semantics where

  Env : Set → Set
  Env X = X → A
```

The semantics extends the environment from variables `X` to all terms `Term X`.

```
  infix 200 ⟦_⟧_
  ⟦_⟧_ : Term X → Env X → A
  ⟦ 0T ⟧ _ = 0R
  ⟦ var x ⟧ ϱ = ϱ x
  ⟦ c · p ⟧ ϱ = c *R ⟦ p ⟧ ϱ
  ⟦ p + q ⟧ ϱ = ⟦ p ⟧ ϱ +R ⟦ q ⟧ ϱ
  ⟦ p * q ⟧ ϱ = ⟦ p ⟧ ϱ *R ⟦ q ⟧ ϱ
```

## Terms with finitely many variables

We also define the semantics for terms over finitely many variables.

```
  Envᵥ : ℕ → Set
  Envᵥ n = Vec A n

  infix 200 ⟦_⟧ᵥ_
  ⟦_⟧ᵥ_ : Term′ n → Envᵥ n → A
  ⟦ p ⟧ᵥ ϱ = ⟦ p ⟧ lookup ϱ
```

We introduce a convenient notation for the semantics of terms with four variables.

```
  ⟦_⟧⟨_,_,_,_⟩ : Term′ 4 → A → A → A → A → A
  ⟦ p ⟧⟨ a₀ , a₁ , a₂ , a₃ ⟩ = ⟦ p ⟧ᵥ (a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ [])
```

## Properties of the semantics

The semantics is invariant under the application of pointwise equivalent environments.
Here invariance is understood w.r.t. equivalence `≈R` in the underlying ring.

```
  infix 30 ⟦_⟧≈_
  ⟦_⟧≈_ :
    ∀ {ϱ₀ ϱ₁ : Env X} (p : Term X) →
    (∀ x → ϱ₀ x ≈R ϱ₁ x) →
    --------------------------------
    ⟦ p ⟧ ϱ₀ ≈R ⟦ p ⟧ ϱ₁

  ⟦ 0T ⟧≈ _ = R-refl
  ⟦ var x ⟧≈ ϱ₀≈ϱ₁ = ϱ₀≈ϱ₁ x
  ⟦ c · p ⟧≈ ϱ₀≈ϱ₁ = R-refl ⟨ *R-cong ⟩ ⟦ p ⟧≈ ϱ₀≈ϱ₁
  ⟦ p + q ⟧≈ ϱ₀≈ϱ₁ = ⟦ p ⟧≈ ϱ₀≈ϱ₁ ⟨ +R-cong ⟩ ⟦ q ⟧≈ ϱ₀≈ϱ₁
  ⟦ p * q ⟧≈ ϱ₀≈ϱ₁ = ⟦ p ⟧≈ ϱ₀≈ϱ₁ ⟨ *R-cong ⟩ ⟦ q ⟧≈ ϱ₀≈ϱ₁
```

For convenience we specialise the above property to terms with four variables.

```
  ⟦_⟧≈⟨_,_,_,_⟩ :
    ∀ {a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃} (p : Term′ 4) →
    a₀ ≈R b₀ → a₁ ≈R b₁ → a₂ ≈R b₂ → a₃ ≈R b₃ →
    -----------------------------------------------
    ⟦ p ⟧⟨ a₀ , a₁ , a₂ , a₃ ⟩ ≈R ⟦ p ⟧⟨ b₀ , b₁ , b₂ , b₃ ⟩

  ⟦ p ⟧≈⟨ a₀≈b₀ , a₁≈b₁ , a₂≈b₂ , a₃≈b₃ ⟩ = ⟦ p ⟧≈ go where

    go : (x : Var 4) →
      lookup (_ ∷ _ ∷ _ ∷ _ ∷ []) x ≈R
      lookup (_ ∷ _ ∷ _ ∷ _ ∷ []) x
    go zero = a₀≈b₀
    go (suc zero) = a₁≈b₁
    go (suc (suc zero)) = a₂≈b₂
    go (suc (suc (suc zero))) = a₃≈b₃
```
