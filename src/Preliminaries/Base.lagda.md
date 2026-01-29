---
title: Basic common definitions
---

```
module Preliminaries.Base where

open import Agda.Primitive using (Level; lzero) renaming (_⊔_ to _⊔ℓ_) public
open import Agda.Builtin.Sigma using (fst; snd) public
open import Agda.Builtin.Bool using (Bool; true; false) public

open import Relation.Nullary using (Dec; yes; no; ¬_) public
open import Relation.Unary using () renaming (WeaklyDecidable to WeaklyDecidable₁) public
open import Relation.Binary.Core public
open import Relation.Binary.Structures public
open import Relation.Binary.Definitions using (Decidable; WeaklyDecidable) public
open import Function.Base using (id; _∘_; _$_) public

open import Relation.Binary.PropositionalEquality
    using (_≡_; refl; cong; cong₂; sym; trans)
    renaming (isEquivalence to ≡-isEq) public

module ≡-Eq where
    open Relation.Binary.PropositionalEquality.≡-Reasoning public

open import Data.Bool.Base using (T) public
-- (Bool; true; false; T; ⊥; _∧_; _∨_; not) public

open import Data.Empty public

open import Data.Maybe.Base using (Maybe; just; nothing) public

open import Data.Product using (∃; _×_) public
open import Data.Product.Base using (∃-syntax) renaming (_,_ to _,,_) public

infix 4 _iff_
_iff_ : (A B : Set) → Set
A iff B = (A → B) × (B → A)

open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎) public

open import Data.Nat
    using (ℕ; zero; suc; _≤_; _<_; z≤n; s≤s; s<s; s≤s⁻¹; _≤?_; _⊔_)
    renaming (_+_ to _+ℕ_; _*_ to _*ℕ_)
    public

open import Data.Integer as Int
    using ()
    renaming (ℤ to ℤ; suc to sucℤ; _+_ to _+ℤ_; _-_ to _-ℤ_; _*_ to _*ℤ_; 0ℤ to 0ℤ; 1ℤ to 1ℤ; _≟_ to _≟ℤ′_)
    public

_≟ℤ_ : WeaklyDecidable {A = ℤ} _≡_
x ≟ℤ y with x ≟ℤ′ y
... | yes a = just a
... | no a = nothing

import Data.Integer.Properties as IntProp using (+-*-commutativeRing)
-- ringℤ : CommutativeRing
ringℤ = IntProp.+-*-commutativeRing

open import Data.Fin.Base using (Fin; zero; suc; fromℕ; fromℕ<; fromℕ<″; _↑ˡ_; _↑ʳ_; inject≤) public

open import Data.Vec
    using (Vec; []; _∷_; _++_; lookup; map; truncate; tabulate; fromList; concat)
    public

open import Data.Vec.Relation.Unary.Any as Any using (Any; here; there) public
open import Data.Vec.Relation.Unary.All as All using (All; []; _∷_) renaming (lookup to All-lookup; map to All-map) public

open import Data.Vec.Membership.Propositional.Properties
    using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-tabulate⁺; ∈-lookup) public

open import Data.Vec.Membership.Propositional public

open import Algebra renaming (CommutativeRing to CR)
CommutativeRing = CR lzero lzero

infixl 5 _⟨_⟩_
_⟨_⟩_ : 
    -- {A : Set} {B : A → Set} {C : (a : A) → B a → Set} →
    -- (a : A) → ((a : A) → (b : B a) → C a b) → (b : B a) → C a b
    -- ∀ {ℓ} {A B : Set} {C : Set ℓ} →
    ∀ {ℓ} {A B C : Set ℓ} →
    A → (A → B → C) → B → C
    
x ⟨ f ⟩ y = f x y
```
