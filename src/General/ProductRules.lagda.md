---
title: Products rules 🚧
---

In this section we illustrate some examples of product rules of formal series,
motivating a general definition of a product rule.

```
{-# OPTIONS --guardedness --sized-types #-}

open import Preliminaries.Base hiding (_×_)
module General.ProductRules (R : CommutativeRing) where

open import Size
private variable i : Size

open import Preliminaries.Algebra R
open import Preliminaries.Vector
```

# Examples of products of series
```
module Examples (Σ : Set)  where
    open import General.Series R Σ
```

## Cauchy product

The *Cauchy product* `_×_` is obtained by extending concatenation of words to series by linearity.
Perhaps this is the most well-known product of formal series.
In our coinductive framework, it can be defined using the well-known *Brzozowski derivative*.

```
    infixr 7 _×_
    _×_ : A ⟪ Σ ⟫ i → A ⟪ Σ ⟫ i → A ⟪ Σ ⟫ i
    ν (f × g) = ν f *R ν g
    δ (f × g) a = δ f a × g + ν f · δ g a
```

The size parameter `i` is used to allow Agda to verify productivity of the definition.
A similar consideration applies to the other products defined below.

Our notion of product rule will not capture this product.
However, it is included here as a reference point to contrast it
to the products below, which can be captured by our notion of product rule.

## Hadamard product

The *Hadamard product* `_⊙_` is obtained by extending pointwise the multiplication operation of the underlying ring.
In our coinductive framework, it can be defined as follows.

```
    infixr 7 _⊙_
    _⊙_ : A ⟪ Σ ⟫ → A ⟪ Σ ⟫ → A ⟪ Σ ⟫
    ν (f ⊙ g) = ν f *R ν g
    δ (f ⊙ g) a = δ f a ⊙ δ g a
```

## Shuffle product

The *shuffle product* `_⧢_` is best defined coinductively.

```
    infixr 7 _⧢_
    _⧢_ : A ⟪ Σ ⟫ i → A ⟪ Σ ⟫ i → A ⟪ Σ ⟫ i
    ν (f ⧢ g) = ν f *R ν g
    δ (f ⧢ g) a = δ f a ⧢ g + f ⧢ δ g a
```

Sometimes this is called *Hurwitz product* [@Fliess:1974].
It finds applications in enumerative combinatorics [@Lothaire:CUP:1997] and in control theory [@Fliess:1981].

## Infiltration product

The *infiltration product* `_↑_` is a combination of the Hadamard and the shuffle products [@BasoldHansenPinRutten:MSCS:2017].

```
    infixr 7 _↑_
    _↑_ : A ⟪ Σ ⟫ i → A ⟪ Σ ⟫ i → A ⟪ Σ ⟫ i
    ν (f ↑ g) = ν f *R ν g
    δ (f ↑ g) a = δ f a ↑ g + f ↑ δ g a + δ f a ↑ δ g a
```

# Product rules

We are now ready to define the notion of product rule that we will use in the rest of the document.

A *product rule* is a term `P` with four variables `x`, `x′`, `y`, and `y′`.
Intuitively, `x` and `y` represent two series `f` and `g`,
while `x′` and `y′` represent their derivatives `δ f a` and `δ g a`, respectively.
The term `P` then specifies how to compute the derivative of the product of `f` and `g`
in terms of `f`, `δ f a`, `g`, and `δ g a`.

```
open import General.Terms R

ProductRule : Set
ProductRule = Term′ 4
```

## Examples of product rules {#sec:product-rules-examples}

We show simple examples of product rules.
Some rules are trivial, like the one below.

```
ruleZero : ProductRule
ruleZero = 0T
```

The product rule `ruleConst` is also degenerate since it does not refer to derivatives at all.

```
ruleConst : ProductRule
ruleConst = x * y
```

The product rules for the Hadamard, shuffle, and infiltration products are more interesting.

### Hadamard product rule

```
ruleHadamard : ProductRule
ruleHadamard = x′ * y′
```

### Shuffle product rule

```
ruleShuffle : ProductRule
ruleShuffle = x′ * y + x * y′
```

### Infiltration product rule

```
ruleInfiltration : ProductRule
ruleInfiltration = x′ * y + x * y′ + x′ * y′
```

In the [next section](../Products) we will see how to use a product rule
to define a product of formal series.
