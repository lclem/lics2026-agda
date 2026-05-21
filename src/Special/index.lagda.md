---
title: "Main results"
up: /
prev: /General/index
---

In this part we present our main results.
Namely, we characterise the class of product rules `P` for which `P`-products are bilinear, associative, and commutative,
and we show that for such product rules the semantics of `P`-automata are compatible with equivalence of terms.

The rest of this part is organised as follows.

- In !chapterRef(Special)(Polynomials) we introduce equivalence of terms
w.r.t. the axioms of associative commutative algebras and use it to define special product rules.

- In !chapterRef(Special)(Products) we show that special product rules induce associative commutative series algebras.

- In !chapterRef(Special)(Automata) we show that `P`-automata are compatible with equivalence of terms when `P` is a special product rule.

- Finally, in !chapterRef(Special)(Reversal) we show that `P`-finite series are closed under right derivatives for every special product rule.

```
{-# OPTIONS --guardedness --sized-types #-}

module Special.index where

import Special.Polynomials
import Special.Products
import Special.Automata
import Special.Reversal
```
