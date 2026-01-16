---
title: "Series 🚧"
---

# Formal series

In this section we introduce formal series in a coinductive way.
The definitions are parametrised by a commutative ring `R` and a set of input symbols `Σ`.

```
{-# OPTIONS --guardedness --sized-types #-}

open import Preliminaries.Base hiding (_++_)
module General.Series (R : CommutativeRing) (Σ : Set) where

open import Size
open import Preliminaries.Algebra R
```

A series `f` is coinductively defined by its constant term `ν f` (in `R`)
and its left derivative `δ f a`, for every input symbol `a` from `Σ`.

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

The additional `Size` parameter is used to ensure productivity
of certain more complicated coinductive definitions that occur later.
We define a shorthand notation `A ⟪ Σ ⟫` for series over alphabet `Σ` and coefficients in `A` for the trivial size parameter.

```
_⟪_⟫ : Set → Set → Set
A ⟪ Σ ⟫ = A ⟪ Σ ⟫ ∞
```

We will denote sizes by `i`, `j`, and series by `f`, `g`, `h`, etc.

```
private variable
  i j : Size
  f f′ g g′ h h′ : A ⟪ Σ ⟫
```

In the rest of the section `A` is the carrier of the commutative ring `R`.
We are now ready to define some series.
For every `c : A`, `const c : A ⟪ Σ ⟫` is the constant series with value `c`.

```
-- constant series
const : A → A ⟪ Σ ⟫
ν (const c) = c
δ (const c) a = const c
```

For instance, `𝟘` is the series which is zero everywhere.

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

We define what it means for two series to be equal in an coinductive way,
by requiring that their constant terms are equal and that their left derivatives are equal.

```
infix 4 _≈[_]_
record _≈[_]_ (f : A ⟪ Σ ⟫) (i : Size) (g : A ⟪ Σ ⟫) : Set where
  coinductive
  field
    ν-≈ : ν f ≈R ν g
    δ-≈ : ∀ {j : Size< i} (a : Σ) → δ f a ≈[ j ] (δ g a)
  
open _≈[_]_ public
```

The additional `Size` parameter is use to ensure productivity of the definition.
We define a shorthand notation `f ≈ g` for equality of series `f` and `g` at the trivial size parameter.

```
infix 3 _≈_
_≈_ : A ⟪ Σ ⟫ → A ⟪ Σ ⟫ → Set
f ≈ g = f ≈[ ∞ ] g
```

## Properties of equality

We prove that equality of series is an equivalence relation.
Reflexivity is straightforward.

```
≈-refl : {f : A ⟪ Σ ⟫} → f ≈ f
ν-≈ ≈-refl = R-refl
δ-≈ ≈-refl _ = ≈-refl
```

Reflexivity gives us one way to prove that two series are equal,
by means of definitional equality.

```
≡→≈ : f ≡ g → f ≈ g
≡→≈ _≡_.refl = ≈-refl
```

We prove symmetry and transitivity at every size,
which will help us later to ensure productivity.

```
≈-sym : {f g : A ⟪ Σ ⟫} → f ≈[ i ] g → g ≈[ i ] f
ν-≈ (≈-sym f≈g) = R-sym (ν-≈ f≈g)
δ-≈ (≈-sym f≈g) a = ≈-sym (δ-≈ f≈g a)

≈-trans : {f g h : A ⟪ Σ ⟫} → f ≈[ i ] g → g ≈[ i ] h → f ≈[ i ] h
ν-≈ (≈-trans f≈g g≈h) = R-trans (ν-≈ f≈g) (ν-≈ g≈h)
δ-≈ (≈-trans f≈g g≈h) a = ≈-trans (δ-≈ f≈g a) (δ-≈ g≈h a)
```

We can now package these properties together.

```
isEquivalence-≈ : IsEquivalence (_≈[ i ]_)
isEquivalence-≈ = record { refl = ≈-refl; sym = ≈-sym; trans = ≈-trans }

module EqS {i : Size} where
  open import Preliminaries.Equivalence (isEquivalence-≈ {i})
  open Eq public
```

## Extensions of equality

We extend equality of series to environments and vectors of series.

### Extension to environments

An *environment* is a mapping from a set of variables `X` to series `A ⟪ Σ ⟫`.

```
SEnv : {i : Size} → Set → Set
SEnv {i} X = X → A ⟪ Σ ⟫ i
```

We extend equality of series to environments point-wise.

```
private variable X : Set

infix 4 _≈ϱ[_]_
_≈ϱ[_]_ : ∀ (ϱ : SEnv X) i (ϱ′ : SEnv X) → Set
ϱ ≈ϱ[ i ] ϱ′ = ∀ x → ϱ x ≈[ i ] ϱ′ x
```

For instance, we can show that two environments are equal if they are point-wise definitionally so.

```
≡→≈ϱ :
  ∀ {ϱ ϱ′ : SEnv X} →
  (∀ x → ϱ x ≡ ϱ′ x) →
  ----------------------------
  ϱ ≈ϱ[ i ] ϱ′

≡→≈ϱ ϱ≡ϱ′ x rewrite ϱ≡ϱ′ x = ≈-refl
```

### Extension to vectors

We denote by `SEnvᵥ n` the type of `n`-tuples of series.

```
SEnvᵥ : {Size} → ℕ → Set
SEnvᵥ {i} n = Vec (A ⟪ Σ ⟫ i) n
```

We define equality of vectors of series point-wise.

```
private variable
  n : ℕ
  fs gs : SEnvᵥ n

infix 4 _≈ᵥ[_]_
infixr 5 _∷≈_
infixr 6 _∎≈

data _≈ᵥ[_]_ : ∀ (fs : SEnvᵥ n) (i : Size) (gs : SEnvᵥ n) → Set where
    []≈ : [] ≈ᵥ[ i ] []
    _∷≈_ : (f≈g : f ≈[ i ] g) (fs≈gs : fs ≈ᵥ[ i ] gs) → (f ∷ fs) ≈ᵥ[ i ] (g ∷ gs)

_∎≈ : (f≈g : f ≈[ i ] g) → (f ∷ []) ≈ᵥ[ i ] (g ∷ [])
f≈g ∎≈ = f≈g ∷≈ []≈
```

We introduce some convenient abbreviations to denote vector equalities of certain lengths.

```
infix 5 [_,_,_,_] [_,_,_,_,_,_]
[_,_,_,_] :
  ∀ {f₀ f₁ f₂ f₃ g₀ g₁ g₂ g₃ : A ⟪ Σ ⟫} →
    (f₀ ≈[ i ] g₀) →
    (f₁ ≈[ i ] g₁) →
    (f₂ ≈[ i ] g₂) →
    (f₃ ≈[ i ] g₃) →
    (f₀ ∷ f₁ ∷ f₂ ∷ f₃ ∷ []) ≈ᵥ[ i ]  (g₀ ∷ g₁ ∷ g₂ ∷ g₃ ∷ [])
[ f₀≈g₀ , f₁≈g₁ , f₂≈g₂ , f₃≈g₃ ] =
    f₀≈g₀ ∷≈ f₁≈g₁ ∷≈ f₂≈g₂ ∷≈ f₃≈g₃ ∎≈

[_,_,_,_,_,_] :
  ∀ {f₀ f₁ f₂ f₃ f₄ f₅ g₀ g₁ g₂ g₃ g₄ g₅ : A ⟪ Σ ⟫} →
    (f₀ ≈[ i ] g₀) →
    (f₁ ≈[ i ] g₁) →
    (f₂ ≈[ i ] g₂) →
    (f₃ ≈[ i ] g₃) →
    (f₄ ≈[ i ] g₄) →
    (f₅ ≈[ i ] g₅) →
    (f₀ ∷ f₁ ∷ f₂ ∷ f₃ ∷ f₄ ∷ f₅ ∷ []) ≈ᵥ[ i ] (g₀ ∷ g₁ ∷ g₂ ∷ g₃ ∷ g₄ ∷ g₅ ∷ [])
[ f₀≈g₀ , f₁≈g₁ , f₂≈g₂ , f₃≈g₃ , f₄≈g₄ , f₅≈g₅ ] =
    f₀≈g₀ ∷≈ f₁≈g₁ ∷≈ f₂≈g₂ ∷≈ f₃≈g₃ ∷≈ f₄≈g₄ ∷≈ f₅≈g₅ ∎≈
```

## Auxiliary definitions

We can convert vector equalities to environment equalities.

```
build-≈ϱ :
  fs ≈ᵥ[ i ] gs →
  ---------------------------
  lookup fs ≈ϱ[ i ] lookup gs

build-≈ϱ (f≈g ∷≈ _) zero = f≈g
build-≈ϱ (_ ∷≈ h) (suc x) = build-≈ϱ h x
```

```
map-cong :
  ∀ (f g : SEnv X) (xs : Vec X n) →
  (∀ x → f x ≈[ i ] g x) →
  ---------------------------------
  map f xs ≈ᵥ[ i ] map g xs

map-cong f g [] ass = []≈
map-cong f g (x ∷ xs) ass = ass x ∷≈ map-cong f g xs ass
```

# Sum of series

The sum of two series `f` and `g` is the series `f + g` which is defined coinductively as follows.

```
infixr 6 _+_
_+_ : A ⟪ Σ ⟫ i → A ⟪ Σ ⟫ i → A ⟪ Σ ⟫ i
ν (f + g) = ν f +R ν g
δ (f + g) a = δ f a + δ g a
```

## Properties of sum

We show that series with addition `_+_` and zero `𝟘` form a monoid.

```
+-identityˡ : (f : A ⟪ Σ ⟫) → 𝟘 + f ≈ f
ν-≈ (+-identityˡ f) = +R-identityˡ (ν f)
δ-≈ (+-identityˡ f) a = +-identityˡ (δ f a)

+-identityʳ : (f : A ⟪ Σ ⟫) → f + 𝟘 ≈ f
ν-≈ (+-identityʳ f) = +R-identityʳ (ν f)
δ-≈ (+-identityʳ f) a = +-identityʳ (δ f a)

+-identity : Identity _≈_ 𝟘 _+_
+-identity = +-identityˡ ,, +-identityʳ

+-comm : (f g : A ⟪ Σ ⟫) → f + g ≈ g + f
ν-≈ (+-comm f g) = +R-comm (ν f) (ν g)
δ-≈ (+-comm f g) a = +-comm (δ f a) (δ g a)

+-assoc : (f g h : A ⟪ Σ ⟫) → (f + g) + h ≈ f + g + h
ν-≈ (+-assoc f g h) = +R-assoc (ν f) (ν g) (ν h)
δ-≈ (+-assoc f g h) a = +-assoc (δ f a) (δ g a) (δ h a)

+-cong : Congruent₂ (λ f g → _≈[_]_ f i g) _+_
ν-≈ (+-cong f≈g h≈i) = +R-cong (ν-≈ f≈g) (ν-≈ h≈i)
δ-≈ (+-cong f≈g h≈i) a = +-cong (δ-≈ f≈g a) (δ-≈ h≈i a)

infix 20 _+≈_
_+≈_ = +-cong
```

We can prove a ternary version of the congruence property for addition.

```
+-cong₃ : f ≈[ i ] f′ → g ≈[ i ] g′ → h ≈[ i ] h′ → f + g + h ≈[ i ] f′ + g′ + h′
+-cong₃ f≈f′ g≈g′ h≈h′ = f≈f′ ⟨ +-cong ⟩ (g≈g′ ⟨ +-cong ⟩ h≈h′)
```

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

+S-monoid : Monoid _ _
+S-monoid = record {
    Carrier = A ⟪ Σ ⟫;
    _≈_ = _≈_;
    _∙_ = _+_;
    ε = 𝟘;
    isMonoid = +-isMonoid
  }
```

We define what it means for a function on series to be an endomorphism with respect to addition and zero.

```
Endomorphic-+ Endomorphic-𝟘 : (A ⟪ Σ ⟫ → A ⟪ Σ ⟫) → Set
Endomorphic-+ F = ∀ {i} f g → F (f + g) ≈[ i ] F f + F g
Endomorphic-𝟘 F = ∀ {i} → F 𝟘 ≈[ i ] 𝟘
```

# Scalar multiplication

We define the operation that multiplies a series by a scalar from the ring `R`.

```
infixr 7 _·_
_·_ : A → A ⟪ Σ ⟫ i → A ⟪ Σ ⟫ i
ν (c · f) = c *R ν f
δ (c · f) a = c · δ f a
```

## Properties of scalar multiplication

```
·-zero :
    ∀ (f : A ⟪ Σ ⟫) →
    -----------------
    0R · f ≈ 𝟘

ν-≈ (·-zero f) = R-zeroˡ _
δ-≈ (·-zero f) a = ·-zero (δ f a)

·-one :
    ∀ (f : A ⟪ Σ ⟫) →
    -----------------
    1R · f ≈ f

ν-≈ (·-one f) = *R-identityˡ (ν f)
δ-≈ (·-one f) a = ·-one (δ f a)

infix 20 _·≈_
·-cong _·≈_ :
    ∀ {f g : A ⟪ Σ ⟫} {c d : A} →
    c ≈R d →
    f ≈[ i ] g →
    -----------------------------
    c · f ≈[ i ] d · g

ν-≈ (c≈d ·≈ f≈g) = *R-cong c≈d (ν-≈ f≈g)
δ-≈ (c≈d ·≈ f≈g) a = c≈d ·≈ δ-≈ f≈g a

·-cong = _·≈_
```

Distributivity of scalar multiplication over series addition.

```
module Properties where

  ·-+-distrib :
    ∀ (c : A) (f g : A ⟪ Σ ⟫) →
    ---------------------------
    c · (f + g) ≈ c · f + c · g

  ν-≈ (·-+-distrib c f g) = R-distribˡ c (ν f) (ν g)
  δ-≈ (·-+-distrib c f g) a = ·-+-distrib c (δ f a) (δ g a)

  *-·-distrib :
    ∀ (c d : A) (f : A ⟪ Σ ⟫) →
    ---------------------------
    (c *R d) · f ≈ c · (d · f)

  ν-≈ (*-·-distrib c d f) = *R-assoc c d (ν f)
  δ-≈ (*-·-distrib c d f) a = *-·-distrib c d (δ f a)
```

Distributivity of ring addition over scalar multiplication.

```
  +-·-distrib :
    ∀ (f : A ⟪ Σ ⟫) (c d : A) →
    --------------------------------
    (c +R d) · f ≈ c · f + d · f

  ν-≈ (+-·-distrib f c d) = R-distribʳ (ν f) c d
  δ-≈ (+-·-distrib f c d) a = +-·-distrib (δ f a) c d
```

We define what it means for a map of series to respect scalar multiplication.

```
Endomorphic-· : (A ⟪ Σ ⟫ → A ⟪ Σ ⟫) → Set
Endomorphic-· F = ∀ {i} c f → F (c · f) ≈[ i ] c · F f
```

# Additive inverses

We can use scalar multiplication to define additive inverses.

```
infixl 3 -_
-_ : A ⟪ Σ ⟫ → A ⟪ Σ ⟫
- f = (-R 1R) · f
```

In turn, this allows us to define subtraction of series.

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

The unary minus operator allows us to define left and right additive inverses.

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
  ∎ where open EqS; open Properties

-‿inverseˡ : LeftInverse _≈_ 𝟘 (-_) _+_
-‿inverseˡ f = begin
    (- f) + f
        ≈⟨ +-comm _ _ ⟩
    f - f
        ≈⟨ -‿inverseʳ f ⟩
    𝟘
    ∎ where open EqS

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
open Properties

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

# Classic (inductive) approach to series

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
  coeff-δˡ* : ∀ u v f → δˡ* u f ⟨ v ⟩ ≡ f ⟨ u ++ v ⟩
  coeff-δˡ* ε v f = refl
  coeff-δˡ* (a ∷ u) v f = coeff-δˡ* u v (δˡ a f)
```

We can also convert a classical series to a coinductive one,
however we will not need this in the rest of the development.
