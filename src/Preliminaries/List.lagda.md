
---
title: List preliminaries
---

```
{-# OPTIONS --sized-types #-}

module Preliminaries.List where

open import Preliminaries.Base hiding (_++_)
open import Preliminaries.Equivalence

open import Data.List as L renaming (List to _*; [] to ε) hiding (map; concatMap; lookup) public
open import Data.List.Properties public

private
  variable
    A B : Set

∷ʳ-++-++ :
    ∀ (xs : A *) a ys zs →
    ----------------------------------------
    xs ∷ʳ a ++ ys ++ zs ≡ xs ++ a ∷ ys ++ zs

∷ʳ-++-++ {A = A} xs a ys zs =
    begin
        xs ∷ʳ a ++ (ys ++ zs) ≡⟨ ++-assoc (xs ∷ʳ a) ys zs ⟨
        (xs ∷ʳ a ++ ys) ++ zs ≡⟨ cong (λ ts → ts ++ zs) (∷ʳ-++ xs a ys) ⟩
        (xs ++ a ∷ ys) ++ zs ≡⟨ ++-assoc xs _ zs ⟩
        xs ++ (a ∷ ys ++ zs)
    ∎ where open Eq ≡-isEq

∷ʳ-∷ : ∀ xs (x y : A) → (y ∷ xs) ∷ʳ x ≡ y ∷ (xs ∷ʳ x)
∷ʳ-∷ _ _ _ = refl

reverse-∷ʳ : ∀ (x : A) xs → reverse (xs ∷ʳ x) ≡ x ∷ reverse xs
reverse-∷ʳ x ε = refl
reverse-∷ʳ x (y ∷ xs) =
    begin
        reverse ((y ∷ xs) ∷ʳ x) ≡⟨ refl ⟩
        reverse (y ∷ (xs ∷ʳ x)) ≡⟨ unfold-reverse _ (xs ∷ʳ x) ⟩
        reverse (xs ∷ʳ x) ∷ʳ y ≡⟨ cong (_∷ʳ y) (reverse-∷ʳ x xs) ⟩
        (x ∷ reverse xs) ∷ʳ y ≡⟨ refl ⟩
        x ∷ (reverse xs ∷ʳ y) ≡⟨ cong (x ∷_) (unfold-reverse y xs) ⟨
        x ∷ reverse (y ∷ xs)
    ∎ where open Eq ≡-isEq

reverse-∷ʳ-++ :
    ∀ u v (b : A) →
    ---------------------------------------------
    (u ∷ʳ b) ++ reverse v ≡ u ++ reverse (v ∷ʳ b)
    
reverse-∷ʳ-++ u v b =
    begin
        (u ∷ʳ b) ++ reverse v ≡⟨ ∷ʳ-++ _ _ _ ⟩
        u ++ b ∷ reverse v ≡⟨ cong (u ++_) $ reverse-∷ʳ _ v ⟨
        u ++ reverse (v ∷ʳ b)
    ∎ where open Eq ≡-isEq
```
