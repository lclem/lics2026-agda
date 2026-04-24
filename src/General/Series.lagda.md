---
title: "Series"
---

In this section we introduce the notion of *formal series* in noncommuting variables,
which is the central mathematical object of our formalisation.

Our development is coinductive.
We compare this with the classical inductive definition [at the end](#sec:classic).

# Formal series

The whole development is parametrised by a commutative ring `R`
and a set of input symbols `Σ`.

```
{-# OPTIONS --guardedness --sized-types #-}

open import Preliminaries.Base
module General.Series (R : CommutativeRing) (Σ : Set) where

```

Let `A` be the set of coefficients and `Σ` the set of input symbols.
We denote the set of series by

    A ⟪ Σ ⟫

A series `f` from `A ⟪ Σ ⟫` is defined coinductively by specifying

- its *constant term* `ν f` (in the set of coefficients `A`), and

- for every input symbol `a` from `Σ`,
its *left derivative* `δ f a` (also a series in `A ⟪ Σ ⟫`).

At this point, calling it a "left" derivative is just a convention,
however we will later break symmetry when we introduce ["right" derivatives](../Reversal/index).

This definition is capture in Agda as follows.

```
infix 4 _⟪_⟫_
record _⟪_⟫_ (A Σ : Set) (i : Size) : Set where
  coinductive
  field

    -- constant term
    ν : A

    -- left derivative
    δ : ∀ {j : Size< i} → Σ → A ⟪ Σ ⟫ j

open _⟪_⟫_ public
```

The additional `Size` parameter is used to allow Agda to verify productivity
of more complicated coinductive definitions that occur later.

We define a shorthand notation `A ⟪ Σ ⟫`
for series over alphabet `Σ` and coefficients in `A` for the trivial size parameter.

```
_⟪_⟫ : Set → Set → Set
A ⟪ Σ ⟫ = A ⟪ Σ ⟫ ∞
```

In the rest of the section,
`A` denotes the carrier of the commutative ring `R`,

- `i`, `j` denote sizes,
- `c`, `d` denote scalars from the ring `R`, and
- `f`, `g`, `h`, etc., denote series from `A ⟪ Σ⟫`.

```
open import Preliminaries.Algebra R

private variable
  i j : Size
  c d : A
  f g h f′ g′ h′ : A ⟪ Σ ⟫
```

We are now ready to define some series.
For every `c : A`, `const c : A ⟪ Σ ⟫` is the constant series with value `c`.

```
-- constant series
const : A → A ⟪ Σ ⟫
ν (const c) = c
δ (const c) a = const c
```

For instance, `𝟘` is the series which is zero everywhere.
Note that `0R` is the zero of the underlying ring `R`.

```
𝟘 : A ⟪ Σ ⟫
𝟘 = const 0R
```

Sometimes we will find it useful to have a version of the left derivative
which takes its arguments in the opposite order.

```
δˡ : ∀ {j : Size< i} → Σ → A ⟪ Σ ⟫ i → A ⟪ Σ ⟫ j
δˡ {j = j} a f = δ f {j} a
```

# Equality of series

For two series `f` and `g` we write `f ≈ g` to denote that they are equal.
This notion is defined coinductively as follows:

- their constant terms are equal: `ν f ≈R ν g`; and

- all left derivatives are equal: `δ f a ≈ (δ g a)` for all `a` from `Σ`.

In order to allow Agda to check that definitions involving equality are productive,
we introduce a family of equality relations `f ≈[ i ] g` indexed by a size parameter `i`.

```
infix 4 _≈[_]_
record _≈[_]_ (f : A ⟪ Σ ⟫) (i : Size) (g : A ⟪ Σ ⟫) : Set where
  coinductive
  field
    ν-≈ : ν f ≈R ν g
    δ-≈ : ∀ {j : Size< i} (a : Σ) → δ f a ≈[ j ] (δ g a)
  
open _≈[_]_ public
```

We define a shorthand notation `f ≈ g` for equality of series `f` and `g` at the trivial size parameter.

```
infix 3 _≈_
_≈_ : A ⟪ Σ ⟫ → A ⟪ Σ ⟫ → Set
f ≈ g = f ≈[ ∞ ] g
```

## Equality of series is an equivalence relation

We prove that equality of series is an equivalence relation.
This is a consequence of the fact that equality of coefficients `_≈R_` is an equivalence relation.

In spirit with the definition of equality, all proofs are coinductive.

```
≈-refl : f ≈[ i ] f
ν-≈ ≈-refl = R-refl
δ-≈ ≈-refl _ = ≈-refl

≈-sym : f ≈[ i ] g → g ≈[ i ] f
ν-≈ (≈-sym f≈g) = R-sym (ν-≈ f≈g)
δ-≈ (≈-sym f≈g) a = ≈-sym (δ-≈ f≈g a)

≈-trans : f ≈[ i ] g → g ≈[ i ] h → f ≈[ i ] h
ν-≈ (≈-trans f≈g g≈h) = R-trans (ν-≈ f≈g) (ν-≈ g≈h)
δ-≈ (≈-trans f≈g g≈h) a = ≈-trans (δ-≈ f≈g a) (δ-≈ g≈h a)
```

Reflexivity gives us one way to prove that two series are equal,
by means of definitional equality.

```
≡→≈ : f ≡ g → f ≈ g
≡→≈ _≡_.refl = ≈-refl
```

We can now package these properties together.

```
isEquivalence-≈ : IsEquivalence (_≈[ i ]_)
isEquivalence-≈ = record { refl = ≈-refl; sym = ≈-sym; trans = ≈-trans }

module EqS {i : Size} where
  open import Preliminaries.Equivalence (isEquivalence-≈ {i})
  open Eq public
```

# Sum of series

The sum of two series `f` and `g` is the series `f + g` which is defined coinductively as follows:

- the constant term `ν (f + g)`
is the sum of the constant terms `ν f` and `ν g` in the ring `R`, and

- the left derivative `δ (f + g) a`
is the sum of the left derivatives `δ f a` and `δ g A`,
for every input symbol `a` from `Σ`.

This is captured in Agda as follows.

```
infixr 6 _+_
_+_ : A ⟪ Σ ⟫ i → A ⟪ Σ ⟫ i → A ⟪ Σ ⟫ i
ν (f + g) = ν f +R ν g
δ (f + g) a = δ f a + δ g a
```

## Monoid structure

We show that series with addition `_+_` and zero `𝟘` form a monoid.
In other word, `𝟘` is a left and right identity,
and addition is associative and commutative.

```
+-identityˡ : (f : A ⟪ Σ ⟫) → 𝟘 + f ≈ f
ν-≈ (+-identityˡ f) = +R-identityˡ (ν f)
δ-≈ (+-identityˡ f) a = +-identityˡ (δ f a)

+-identityʳ : (f : A ⟪ Σ ⟫) → f + 𝟘 ≈ f
ν-≈ (+-identityʳ f) = +R-identityʳ (ν f)
δ-≈ (+-identityʳ f) a = +-identityʳ (δ f a)

+-identity : Identity _≈_ 𝟘 _+_
+-identity = +-identityˡ ,, +-identityʳ

+-comm : ∀ f g → f + g ≈ g + f
ν-≈ (+-comm f g) = +R-comm (ν f) (ν g)
δ-≈ (+-comm f g) a = +-comm (δ f a) (δ g a)

+-assoc : ∀ f g h → (f + g) + h ≈ f + g + h
ν-≈ (+-assoc f g h) = +R-assoc (ν f) (ν g) (ν h)
δ-≈ (+-assoc f g h) a = +-assoc (δ f a) (δ g a) (δ h a)
```

We also show that equality of series
is a *congruence* with respect to addition.
This means that addition maps congruent series to congruent series:

    f ≈ g, h ≈ k ==> f + h ≈ g + k.

In fact, we prove that addition is a congruence at every size parameter `i`.
The Agda code follows.

```
+-cong : Congruent₂ (λ f g → f ≈[ i ] g) _+_
ν-≈ (+-cong f≈g h≈i) = +R-cong (ν-≈ f≈g) (ν-≈ h≈i)
δ-≈ (+-cong f≈g h≈i) a = +-cong (δ-≈ f≈g a) (δ-≈ h≈i a)

infix 20 _+≈_
_+≈_ = +-cong
```

It will later be useful to have a ternary version
of the congruence property for addition.

```
+-cong₃ : f ≈[ i ] f′ → g ≈[ i ] g′ → h ≈[ i ] h′ → f + g + h ≈[ i ] f′ + g′ + h′
+-cong₃ f≈f′ g≈g′ h≈h′ = f≈f′ ⟨ +-cong ⟩ (g≈g′ ⟨ +-cong ⟩ h≈h′)
```

We pack together the monoid properties
using the !stdlibRef(Algebra.Structures)(IsMonoid) structure provided by the standard library.

```
+-isMonoid : IsMonoid _≈_ _+_ 𝟘
+-isMonoid = record {
    isSemigroup = record {
      isMagma = record {
        isEquivalence = isEquivalence-≈;
        ∙-cong = +-cong
      };
      assoc = +-assoc
    };
    identity = +-identity
  }
```

The corresponding !stdlibRef(Algebra.Bundles)(Monoid) bundle
packs together the carrier, the operation, the identity, and the monoid properties

```
+S-monoid : Monoid _ _
+S-monoid = record {
    Carrier = A ⟪ Σ ⟫;
    _≈_ = _≈_;
    _∙_ = _+_;
    ε = 𝟘;
    isMonoid = +-isMonoid
  }
```

## Monoid endomorphisms

We define what it means for a function on series to respect addition and zero.

```
Endomorphic-+ Endomorphic-𝟘 : (A ⟪ Σ ⟫ → A ⟪ Σ ⟫) → Set
Endomorphic-+ F = ∀ {i} f g → F (f + g) ≈[ i ] F f + F g
Endomorphic-𝟘 F = ∀ {i} → F 𝟘 ≈[ i ] 𝟘
```

For instance, left derivatives respect to addition and zero,
and thus are an endomorphism of the additive monoid of series.

```
δˡ-end-𝟘 : ∀ a → Endomorphic-𝟘 (δˡ a)
ν-≈ (δˡ-end-𝟘 a) = R-refl
δ-≈ (δˡ-end-𝟘 a) b = δˡ-end-𝟘 a

δˡ-end-+ : ∀ a → Endomorphic-+ (δˡ a)
ν-≈ (δˡ-end-+ a f g) = R-refl
δ-≈ (δˡ-end-+ a f g) b = δˡ-end-+ b (δ f a) (δ g a)
```

# Scalar multiplication

We define the *scalar multiplication* operation `_·_`
which takes a scalar `c` from the coefficient ring `R` and a series `f`
and produces a new series `c · f`. It is defined coinductively as follows:

- the constant term `ν (c · f)` is the product of `c`
and the constant term `ν f` in the ring `R`, and

- the left derivative `δ (c · f) a` is the scalar multiplication of `c` and the left derivative `δ f a`, for every input symbol `a` from `Σ`.

The Agda definition is as follows.

```
infixr 7 _·_
_·_ : A → A ⟪ Σ ⟫ i → A ⟪ Σ ⟫ i
ν (c · f) = c *R ν f
δ (c · f) a = c · δ f a
```

## Properties of scalar multiplication

We investigate some basic properties connecting scalar multiplication and addition.

First of all, multipliying a series by the zero scalar gives the zero series.

```
·-zero :
    ∀ (f : A ⟪ Σ ⟫) →
    -----------------
    0R · f ≈ 𝟘

ν-≈ (·-zero f) = R-zeroˡ _
δ-≈ (·-zero f) a = ·-zero (δ f a)
```

Analogously, multiplying a series by the unit scalar gives the same series.

```
·-one :
    ∀ (f : A ⟪ Σ ⟫) →
    -----------------
    1R · f ≈ f

ν-≈ (·-one f) = *R-identityˡ (ν f)
δ-≈ (·-one f) a = ·-one (δ f a)
```

We also show that scalar multiplication is a congruence with respect to series equality
(and the underling congruence `_≈R_` on the coefficient ring `R`).

```
infix 20 _·≈_
·-cong _·≈_ :
    c ≈R d →
    f ≈[ i ] g →
    ------------------
    c · f ≈[ i ] d · g

ν-≈ (c≈d ·≈ f≈g) = *R-cong c≈d (ν-≈ f≈g)
δ-≈ (c≈d ·≈ f≈g) a = c≈d ·≈ δ-≈ f≈g a

·-cong = _·≈_
```

We also define what it means for a map of series to respect scalar multiplication.

```
Endomorphic-· : (A ⟪ Σ ⟫ → A ⟪ Σ ⟫) → Set
Endomorphic-· F = ∀ {i} c f → F (c · f) ≈[ i ] c · F f
```

For instance, left derivatives respect scalar multiplication.

```
δˡ-end-· : ∀ a → Endomorphic-· (δˡ a)
ν-≈ (δˡ-end-· a c f) = R-refl
δ-≈ (δˡ-end-· a c f) b = δˡ-end-· b c (δ f a)
```

We also show distributivity properties.
We define them in a spearate module to avoid name clashes

``` 
module DistributivityProperties where
```

First we show that scalar multiplication distributes over addition of series.

```
  ·-+-distrib :
    ∀ (c : A) (f g : A ⟪ Σ ⟫) →
    ---------------------------
    c · (f + g) ≈ c · f + c · g

  ν-≈ (·-+-distrib c f g) = R-distribˡ c (ν f) (ν g)
  δ-≈ (·-+-distrib c f g) a = ·-+-distrib c (δ f a) (δ g a)
```

Second, we show distributivity of ring addition over scalar multiplication.

```
  +-·-distrib :
    ∀ (f : A ⟪ Σ ⟫) (c d : A) →
    --------------------------------
    (c +R d) · f ≈ c · f + d · f

  ν-≈ (+-·-distrib f c d) = R-distribʳ (ν f) c d
  δ-≈ (+-·-distrib f c d) a = +-·-distrib (δ f a) c d
```

Finally, we show that the multiplication operation `_*R_` of the underlying coefficient ring `R` is compatible with scalar multiplication of series.

```
  *-·-distrib :
    ∀ (c d : A) (f : A ⟪ Σ ⟫) →
    ---------------------------
    (c *R d) · f ≈ c · (d · f)

  ν-≈ (*-·-distrib c d f) = *R-assoc c d (ν f)
  δ-≈ (*-·-distrib c d f) a = *-·-distrib c d (δ f a)
```

# Additive inverses

We can use scalar multiplication to define additive inverses.
For a series `f`, its additive inverse `- f` is defined as the scalar multiplication of `f` by the additive inverse `-R 1R` of the unit scalar in the ring `R`.

```
infixl 3 -_
-_ : A ⟪ Σ ⟫ → A ⟪ Σ ⟫
- f = (-R 1R) · f
```

In turn, this allows us to define subtraction of series in the expected way.

```
infixr 6 _-_
_-_ : A ⟪ Σ ⟫ → A ⟪ Σ ⟫ → A ⟪ Σ ⟫
f - g = f + (- g)
```

## Properties of additive inverses

The unary minus operator is a congruence.

```
-‿cong : Congruent₁ _≈_ (-_)
-‿cong f≈g = ·-cong R-refl f≈g
```

The unary minus operator gives rise to right additive inverses with respect to addition.

```
-‿inverseʳ : RightInverse _≈_ 𝟘 (-_) _+_
-‿inverseʳ f =
  begin
    f - f
      ≈⟨ ·-one f ⟨ +-cong ⟩ ≈-refl ⟨
    1R · f + (-R 1R) · f
      ≈⟨ +-·-distrib _ _ _ ⟨
    (1R -R 1R) · f
      ≈⟨ (-R-inverseʳ _ ⟨ ·-cong ⟩ ≈-refl) ⟩
    0R · f
      ≈⟨ ·-zero _ ⟩
    𝟘
  ∎ where open EqS; open DistributivityProperties
```

Since addition is commutative,
we also obtain left additive inverses.

```
-‿inverseˡ : LeftInverse _≈_ 𝟘 (-_) _+_
-‿inverseˡ f = begin
    (- f) + f
        ≈⟨ +-comm _ _ ⟩
    f - f
        ≈⟨ -‿inverseʳ f ⟩
    𝟘
    ∎ where open EqS
```


Inverses are packaged together with the !stdlibRef(Algebra.Definitions)(Inverse) structure provided by the standard library.

```
-‿inverse : Inverse _≈_ 𝟘 (-_) _+_
-‿inverse = -‿inverseˡ ,, -‿inverseʳ
```

Therefore, series with addition, zero, and unary minus form a (commutative) group.

```
+-isGroup : IsGroup _≈_ _+_ 𝟘 (-_)
+-isGroup = record {
  isMonoid = +-isMonoid;
  inverse = -‿inverse;
  ⁻¹-cong = -‿cong
  }

+-isAbelianGroup : IsAbelianGroup _≈_ _+_ 𝟘 (-_)
+-isAbelianGroup = record {
  isGroup = +-isGroup;
  comm = +-comm
  }
```

We aggregate the above properties by showing that
series with zero, addition, and scalar multiplication
form a left module over the ring `R`.

```
open DistributivityProperties

isLeftModule : IsLeftModule _≈_ _+_ -_ 𝟘 _·_
isLeftModule = record
  { +-isAbelianGroup = +-isAbelianGroup
  ; ·-cong = ·-cong
  ; distribˡ = ·-+-distrib
  ; distribʳ = +-·-distrib
  ; combatible = *-·-distrib
  ; identity = ·-one
  }
```

# Classic (inductive) approach to series {#sec:classic}

```
module Inductive where
  open import Preliminaries.List public
```

Classically, formal series are defined as functions
from finite words over the alphabet `Σ` to the carrier of the coefficient ring `R`.

```
  Series : Set → Set → Set
  Series A Σ = Σ * → A
```

We can convert a coinductively defined series to a classically defined one.
To this end, let `δˡ*` be the homomorphic extension of the left derivative `δˡ` to all finite words.

```
  δˡ* : Σ * → A ⟪ Σ ⟫ → A ⟪ Σ ⟫
  δˡ* ε f = f
  δˡ* (a ∷ w) f = δˡ* w (δˡ a f)
```

A coinductively defined series `f : A ⟪ Σ ⟫`
can now be converted to a classically defined one
thanks to the following *coefficient extraction* operation.

```
  infix 12 _⟨_⟩
  _⟨_⟩ : A ⟪ Σ ⟫ → Series A Σ
  f ⟨ w ⟩ = ν (δˡ* w f)
```

The following *extensionality principle* for series
shows that series are completely determined by their coefficients.

```
  series-ext :
    (∀ w → f ⟨ w ⟩ ≈R g ⟨ w ⟩) →
    ----------------------------
    f ≈ g

  ν-≈ (series-ext ass) = ass ε
  δ-≈ (series-ext ass) a = series-ext λ w → ass (a ∷ w)
```

A nice property connects `δˡ*` and `_⟨_⟩`.

```
  coeff-δˡ* : ∀ u v f → δˡ* u f ⟨ v ⟩ ≡ f ⟨ u ++ℓ v ⟩
  coeff-δˡ* ε v f = refl
  coeff-δˡ* (a ∷ u) v f = coeff-δˡ* u v (δˡ a f)
```

We can also convert a classical series to a coinductive one,
however we will not need this in the rest of the development.
