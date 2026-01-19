---
title: Vectors 🚧
---

In this section we do vectors.

```
-- {-# OPTIONS --allow-unsolved-metas #-}

module Preliminaries.Vector where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import Function.Base using (_∘_)
open import Data.Product.Base using (∃; ∃-syntax; _,_)

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_)

open import Data.Vec
    using (Vec; []; _∷_; _++_; lookup; map; truncate; tabulate; concat)
open import Data.Vec.Relation.Unary.Any using (Any; here; there; index)
open import Data.Vec.Membership.Propositional

private variable
    m n : ℕ
    A B : Set
    a : A
    b : B
    as : Vec A m
    bs : Vec A n
    ass : Vec (Vec A m) n

lookup-map :
    ∀ (f : A → B) (as : Vec A n) (j : Fin n) →
    lookup (map f as) j ≡ f (lookup as j)
lookup-map f (a ∷ _) zero = refl
lookup-map f (_ ∷ as) (suc j) = lookup-map f as j

lookup-tabulate :
    ∀ (f : Fin n → A) (x : Fin n) →
    lookup (tabulate f) x ≡ f x
lookup-tabulate f zero = refl
lookup-tabulate f (suc j) = lookup-tabulate (f ∘ Fin.suc) j

lookup-∈ :
    ∀ {a : A} {as : Vec A n} →
    a ∈ as →
    --------------------------
    ∃[ i ] a ≡ lookup as i
    
lookup-∈ (here a≡x) = zero , a≡x
lookup-∈ (there a∈as) with lookup-∈ a∈as
... | i , eq = suc i , eq

lookup-zero-++ :
    ∀ (as : Vec A (suc m)) (bs : Vec A n) →
    lookup as zero ≡ lookup (as ++ bs) zero

lookup-zero-++ (a ∷ as) bs = refl
```

```
∈ᵥ-++ : a ∈ as ++ bs → a ∈ as ⊎ a ∈ bs
∈ᵥ-++ {as = []} a∈bs = inj₂ a∈bs
∈ᵥ-++ {as = _ ∷ _} (here px) = inj₁ (here px)
∈ᵥ-++ {a = a} {as = _ ∷ as} {bs = bs} (there a∈as++bs)
    with ∈ᵥ-++ {a = a} {as = as} {bs = bs} a∈as++bs
... | inj₁ a∈as = inj₁ (there a∈as)
... | inj₂ a∈bs = inj₂ a∈bs

∈-map⁻ : {f : A → B} → b ∈ map f as → ∃[ a ] a ∈ as × b ≡ f a
∈-map⁻ {as = a ∷ _} (here b≡fa) = a , here refl , b≡fa
∈-map⁻ {as = _ ∷ as} (there b∈) with ∈-map⁻ b∈
... | a , as∈as , b≡fa = a , there as∈as , b≡fa

∈-tabulate⁻ : ∀ {v} {f : Fin n → A} → v ∈ tabulate f → ∃ λ i → v ≡ f i
∈-tabulate⁻ (here px) = zero , px
∈-tabulate⁻ (there v∈f) with ∈-tabulate⁻ v∈f
... | i , eq = suc i , eq

concat-∈⁻ : a ∈ concat ass → ∃ λ as → as ∈ ass × a ∈ as
concat-∈⁻ {a = a} {ass = as ∷ ass} a∈ass with ∈ᵥ-++ {as = as} a∈ass
... | inj₁ a∈as = as ,  here refl , a∈as
... | inj₂ a∈ass with concat-∈⁻ {ass = ass} a∈ass
... | as , as∈ass , a∈as = as , there as∈ass , a∈as
```