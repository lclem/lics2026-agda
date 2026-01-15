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
```

The additional `Size` parameter is used to ensure productivity
of certain more complicated coinductive definitions that occur later.

```
open _⟪_⟫_ public

_⟪_⟫ : Set → Set → Set
A ⟪ Σ ⟫ = A ⟪ Σ ⟫ ∞

private variable
  i : Size
  f g : A ⟪ Σ ⟫

-- constant series
const : A → A ⟪ Σ ⟫
ν (const c) = c
δ (const c) a = const c

-- only constant term
only : A → A ⟪ Σ ⟫
ν (only c) = c
δ (only _) a = const 0R

-- flip the order of the arguments
δˡ : ∀ {i} {j : Size< i} → Σ → A ⟪ Σ ⟫ i → A ⟪ Σ ⟫ j
δˡ {j = j} a f = δ f {j} a

-- map a series to its constant term
hd : A ⟪ Σ ⟫ i → A ⟪ Σ ⟫ i
hd f = only (ν f)
```

# Equality of series

```
infix 4 _≈[_]_
record _≈[_]_ (f : A ⟪ Σ ⟫) (i : Size) (g : A ⟪ Σ ⟫) : Set where
  coinductive
  field
    ν-≈ : ν f ≈R ν g
    δ-≈ : ∀ {j : Size< i} (a : Σ) → δ f a ≈[ j ] (δ g a)
  
open _≈[_]_ public

infix 3 _≈_
_≈_ : A ⟪ Σ ⟫ → A ⟪ Σ ⟫ → Set
f ≈ g = f ≈[ ∞ ] g
```

# Properties of equality

```
≈-refl : {f : A ⟪ Σ ⟫} → f ≈[ i ] f
ν-≈ ≈-refl = R-refl
δ-≈ ≈-refl _ = ≈-refl

≈-sym : {f g : A ⟪ Σ ⟫} → f ≈[ i ] g → g ≈[ i ] f
ν-≈ (≈-sym f≈g) = R-sym (ν-≈ f≈g)
δ-≈ (≈-sym f≈g) a = ≈-sym (δ-≈ f≈g a)

≈-trans : {f g h : A ⟪ Σ ⟫} → f ≈[ i ] g → g ≈[ i ] h → f ≈[ i ] h
ν-≈ (≈-trans f≈g g≈h) = R-trans (ν-≈ f≈g) (ν-≈ g≈h)
δ-≈ (≈-trans f≈g g≈h) a = ≈-trans (δ-≈ f≈g a) (δ-≈ g≈h a)

isEquivalence-≈ : IsEquivalence (_≈[ i ]_)
isEquivalence-≈ = record { refl = ≈-refl; sym = ≈-sym; trans = ≈-trans }

module EqS {i : Size} where
  open import Preliminaries.Equivalence (isEquivalence-≈ {i})
  open Eq public
```

# Extensions

```
-- extension of equality to environments
infix 4 _≈ϱ[_]_
_≈ϱ[_]_ : ∀ {X} (ϱ : X → A ⟪ Σ ⟫) i (ϱ′ : X → A ⟪ Σ ⟫) → Set
ϱ ≈ϱ[ i ] ϱ′ = ∀ x → ϱ x ≈[ i ] ϱ′ x

≡→≈ϱ :
  ∀ {X} {ϱ ϱ′ : X → A ⟪ Σ ⟫} →
  (∀ x → ϱ x ≡ ϱ′ x) →
  ----------------------------
  ϱ ≈ϱ[ i ] ϱ′

≡→≈ϱ ϱ≡ϱ′ x rewrite ϱ≡ϱ′ x = ≈-refl

-- extension of equality to vectors of series
infix 4 _≈s[]_
infixr 5 _∷-≈_ _[]-≈
data _≈s[]_ {i : Size} : ∀ {n} → (fs gs : Vec (A ⟪ Σ ⟫) n) → Set where
    []-≈ : _≈s[]_ {i} [] []
    _∷-≈_ : ∀ {n f g} {fs gs : Vec (A ⟪ Σ ⟫) n} (f≈g : f ≈[ i ] g) (fs≈gs : _≈s[]_ {i} fs gs) → _≈s[]_ {i} (f ∷ fs) (g ∷ gs)

_[]-≈ : ∀ {n f g} {fs gs : Vec (A ⟪ Σ ⟫) n} (f≈g : f ≈[ i ] g) → _≈s[]_ {i} (f ∷ []) (g ∷ [])
f≈g []-≈ = f≈g ∷-≈ []-≈

infix 5 [_,_,_,_]
[_,_,_,_] :
  ∀ {f₀ f₁ f₂ f₃ g₀ g₁ g₂ g₃ : A ⟪ Σ ⟫} →
    (f₀ ≈[ i ] g₀) →
    (f₁ ≈[ i ] g₁) →
    (f₂ ≈[ i ] g₂) →
    (f₃ ≈[ i ] g₃) →
    _≈s[]_ {i} (f₀ ∷ f₁ ∷ f₂ ∷ f₃ ∷ []) (g₀ ∷ g₁ ∷ g₂ ∷ g₃ ∷ [])
[ f₀≈g₀ , f₁≈g₁ , f₂≈g₂ , f₃≈g₃ ] =
    f₀≈g₀ ∷-≈
    f₁≈g₁ ∷-≈
    f₂≈g₂ ∷-≈
    f₃≈g₃ ∷-≈
    []-≈

infix 5 [_,_,_,_,_,_]
[_,_,_,_,_,_] :
  ∀ {f₀ f₁ f₂ f₃ f₄ f₅ g₀ g₁ g₂ g₃ g₄ g₅ : A ⟪ Σ ⟫} →
    (f₀ ≈[ i ] g₀) →
    (f₁ ≈[ i ] g₁) →
    (f₂ ≈[ i ] g₂) →
    (f₃ ≈[ i ] g₃) →
    (f₄ ≈[ i ] g₄) →
    (f₅ ≈[ i ] g₅) →
    _≈s[]_ {i} (f₀ ∷ f₁ ∷ f₂ ∷ f₃ ∷ f₄ ∷ f₅ ∷ []) (g₀ ∷ g₁ ∷ g₂ ∷ g₃ ∷ g₄ ∷ g₅ ∷ [])
[ f₀≈g₀ , f₁≈g₁ , f₂≈g₂ , f₃≈g₃ , f₄≈g₄ , f₅≈g₅ ] =
    f₀≈g₀ ∷-≈
    f₁≈g₁ ∷-≈
    f₂≈g₂ ∷-≈
    f₃≈g₃ ∷-≈
    f₄≈g₄ ∷-≈
    f₅≈g₅ ∷-≈
    []-≈

infix 4 _≈s[_]_
_≈s[_]_ : ∀ {n} (fs : Vec (A ⟪ Σ ⟫) n) i (gs : Vec (A ⟪ Σ ⟫) n) → Set
fs ≈s[ i ] gs = _≈s[]_ {i} fs gs
```

# Properties of the extensions

```
build-≈ϱ :
  ∀ {n} {fs gs : Vec (A ⟪ Σ ⟫) n} →
  fs ≈s[ i ] gs →
  ---------------------------------
  lookup fs ≈ϱ[ i ] lookup gs

build-≈ϱ (f≈g ∷-≈ _) zero = f≈g
build-≈ϱ (_ ∷-≈ h) (suc x) = build-≈ϱ h x

map-cong : ∀ {B : Set} {n} (f g : B → A ⟪ Σ ⟫) (bs : Vec B n) →
    (∀ b → f b ≈[ i ] g b) →
    map f bs ≈s[ i ] map g bs
map-cong f g [] ass = []-≈
map-cong f g (b ∷ bs) ass = ass b ∷-≈ map-cong f g bs ass

≡→≈ : ∀ {f g : A ⟪ Σ ⟫} → f ≡ g → f ≈ g
≡→≈ _≡_.refl = ≈-refl
```

```
infixr 6 _+_
_+_ : ∀ {i} → A ⟪ Σ ⟫ i → A ⟪ Σ ⟫ i → A ⟪ Σ ⟫ i
ν (f + g) = ν f +R ν g
δ (f + g) a = δ f a + δ g a

𝟘 : A ⟪ Σ ⟫
𝟘 = const 0R
```

# Properties

```
-- open import Series.Equality {Σ = Σ} isEquivalence

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

𝟘-+-𝟘 : 𝟘 + 𝟘 ≈ 𝟘
𝟘-+-𝟘 = +-identityˡ 𝟘

+-assoc : (f g h : A ⟪ Σ ⟫) → (f + g) + h ≈ f + g + h
ν-≈ (+-assoc f g h) = +R-assoc (ν f) (ν g) (ν h)
δ-≈ (+-assoc f g h) a = +-assoc (δ f a) (δ g a) (δ h a)

+-cong : Congruent₂ (λ f g → _≈[_]_ f i g) _+_
ν-≈ (+-cong f≈g h≈i) = +R-cong (ν-≈ f≈g) (ν-≈ h≈i)
δ-≈ (+-cong f≈g h≈i) a = +-cong (δ-≈ f≈g a) (δ-≈ h≈i a)

infix 20 _+≈_
_+≈_ = +-cong

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

```
Endomorphic-+ Endomorphic-𝟘 : (A ⟪ Σ ⟫ → A ⟪ Σ ⟫) → Set
Endomorphic-+ F = ∀ {i} x y → F (x + y) ≈[ i ] F x + F y
Endomorphic-𝟘 F = ∀ {i} → F 𝟘 ≈[ i ] 𝟘
```

```
infixr 7 _·_
_·_ : A → A ⟪ Σ ⟫ i → A ⟪ Σ ⟫ i
ν (c · f) = c *R ν f
δ (c · f) a = c · δ f a
```

# Properties

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

```
  Endomorphic-· : (A ⟪ Σ ⟫ → A ⟪ Σ ⟫) → Set
  Endomorphic-· F = ∀ {i} c f → F (c · f) ≈[ i ] c · F f
```

Additive inverse

```
infixl 3 -_
-_ : A ⟪ Σ ⟫ → A ⟪ Σ ⟫
- f = (-R 1R) · f

infixr 6 _-_
_-_ : A ⟪ Σ ⟫ → A ⟪ Σ ⟫ → A ⟪ Σ ⟫
f - g = f + (- g)
```

```
-‿cong : Congruent₁ _≈_ (-_)
-‿cong f≈g = ·-cong R-refl f≈g
```

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

```
module Classic where

  open import Preliminaries.List public

  -- homomorphic extension to all words
  δˡ* : Σ * → A ⟪ Σ ⟫ → A ⟪ Σ ⟫
  δˡ* ε f = f
  δˡ* (a ∷ w) f = δˡ* w (δˡ a f)

  Series : Set → Set → Set
  Series A Σ = Σ * → A

  -- we can convert a classical series to a coinductive one
  -- unravel : Series A Σ → A ⟪ Σ ⟫
  -- ν (unravel f) = f ε
  -- δ (unravel f) a = unravel (Classic-δˡ a f)

  -- we can convert a coinductive series to a classical one
  -- coefficient extraction operation
  infix 12 _⟨_⟩
  _⟨_⟩ : A ⟪ Σ ⟫ → Series A Σ
  f ⟨ w ⟩ = ν (δˡ* w f)

  coeff-δˡ* : ∀ u v f → δˡ* u f ⟨ v ⟩ ≡ f ⟨ u ++ v ⟩
  coeff-δˡ* ε v f = refl
  coeff-δˡ* (a ∷ u) v f = coeff-δˡ* u v (δˡ a f)

  series-ext :
      ∀ (f g : A ⟪ Σ ⟫) →
      (∀ w → f ⟨ w ⟩ ≈R g ⟨ w ⟩) →
      ----------------------------
      f ≈ g

  ν-≈ (series-ext _ _ asmpt) = asmpt ε
  δ-≈ (series-ext f g asmpt) a = series-ext (δ f a) (δ g a) λ w → asmpt (a ∷ w)
```