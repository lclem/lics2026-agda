---
title: 🚧
---

```

module Preliminaries.Integers where

open import Preliminaries.Base

open import Data.Integer
    renaming (_*_ to _*ℤ_; _+_ to _+ℤ_; _-_ to _-ℤ_; _≟_ to _≟ℤ_)
    public

open import Data.Integer.Properties as ℤ
    renaming (+-comm to +ℤ-comm)
    public

weq : WeaklyDecidable {A = ℤ} _≡_
weq x y with x ≟ℤ y
... | yes a = just a
... | no a = nothing

-- examples
2ℤ = 1ℤ +ℤ 1ℤ
3ℤ = 2ℤ +ℤ 1ℤ

Z : CommutativeRing
Z = ℤ.+-*-commutativeRing
```