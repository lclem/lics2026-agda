
{-# OPTIONS --allow-unsolved-metas --sized-types #-}

module Preliminaries.List where

open import Preliminaries.Base hiding (_++_)
open import Preliminaries.Equivalence

open import Data.List as L renaming (List to _*; [] to ε) hiding (map; concatMap; lookup) public
open import Data.List.Properties public

-- -- using (List; _++_; length; reverse; map; foldr; downFrom)
-- open import Data.List.Membership.Propositional using (_∈_)

-- open import Data.List.Relation.Unary.All using (All; []; _∷_)


-- open import Relation.Binary.PropositionalEquality using (_≡_; cong; refl; sym)

private
  variable
    A B : Set

-- _inn_ : ∀ {A : Set} (x : A) (xs : A *) → Set
-- x inn xs = Any (x ≡_) xs

-- ∈-sing : ∀ {A : Set} (a : A) → a ∈ [ a ]
-- ∈-sing a = here refl

-- ∈-sing-inv : ∀ {A : Set} {a b : A} → a ∈ [ b ] → a ≡ b
-- ∈-sing-inv (here px) = px

-- ∈-++ : ∀ {A : Set} (a : A) {as bs} → a ∈ as ++ bs → a ∈ as ⊎ a ∈ bs
-- ∈-++ a = {! x  !}

-- ∈-++ˡ : ∀ {A : Set} {a : A} {as bs} → a ∈ as → a ∈ as ++ bs
-- ∈-++ˡ = {!   !}

-- ∈-++ʳ : ∀ {A : Set} {a : A} {as bs} → a ∈ bs → a ∈ as ++ bs
-- ∈-++ʳ = {!   !}

-- ∈-map : ∀ {A B : Set} {f : A → B} {a} {as : A *} → a ∈ as → f a ∈ mapL f as
-- ∈-map = {!   !}

-- map-∈-inv : ∀ {A B : Set} {as : A *} (f : A → B) {b} → b ∈ mapL f as → ∃ λ a → a ∈ as × b ≡ f a
-- map-∈-inv f b∈map = {!   !}

-- mmap : ∀ {A B : Set} (as : A *) (f : ∀ {a} → a ∈ as → B) → B *
-- mmap ε f = ε 
-- mmap (_ ∷ as) f = f (here refl) ∷ mmap as λ b∈as → f (there b∈as)

-- mmap-∈-inv : ∀ {A B : Set} {as : A *} (f : ∀ {a} → a ∈ as → B) {b} → b ∈ mmap as f → ∃ λ a → ∃ λ (a∈as : a ∈ as) → b ≡ f a∈as
-- mmap-∈-inv f bb = {!   !}

-- mmap-lemma : ∀ {A B : Set} {a} {as : A *} (f : ∀ {a} → a ∈ as → B) (a∈as : a ∈ as) → f a∈as ∈ mmap as f
-- mmap-lemma f (here px) rewrite px = here refl
-- mmap-lemma f (there a∈as) = there (mmap-lemma (λ b∈as → f (there b∈as)) a∈as)

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

-- ∷ʳ-++ : ∀ xs (a : A) ys → xs ∷ʳ a ++ ys ≡ xs ++ a ∷ ys
-- ∷ʳ-++ xs a ys = ++-assoc xs [ a ] ys

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

-- -- homomorphic lifting of a function over a list
-- hom-lift : ∀ {A B : Set} → (A → B → B) → A * → B → B
-- hom-lift _ ε b = b
-- hom-lift f (a ∷ as) b = hom-lift f as (f a b)

-- unpack : ∀ {A : Set} → (A × A) * → A *
-- unpack ε = ε
-- unpack ((a , b) ∷ xs) = a ∷ b ∷ unpack xs

-- singleton : ∀ {A : Set} → A → A *
-- singleton a = a ∷ ε

-- -- list comprehension
-- infixl 1 concatMap map
-- concatMap = L.concatMap
-- map       = L.map

-- infix 4 [_]
-- [_] : ∀ {A : Set} → A * → A *
-- [_] x = x

-- -- Enumerations and binding
-- -- syntax enum k l = k ⋯ l
-- syntax map (λ x → expr) xs       = expr ∣ x ← xs
-- syntax concatMap (λ x → expr) xs = expr , x ← xs

-- _ : List (ℕ × ℕ)
-- _ = [ 2 * x , 3 * x ∣ x ← [[ 1 ]] ]

-- map-comp : ∀ {A B C : Set} {f : A → B} {g : B → C} {as} → map g [ f a ∣ a ← as ] ≡ [ g (f a) ∣ a ← as ]
-- map-comp {f = f} {g} = {! map-∘ {g = g} {f = f}  !}

-- map-comp' : ∀ {A B C : Set} (f : A → B) as → [ f a ∣ a ← as ] ≡ [ b ∣ b ← map f as ]
-- map-comp' f as = {! map-∘ {g = g} {f = f}  !}