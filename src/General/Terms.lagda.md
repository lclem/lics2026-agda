---
title: "Series 🚧"
---

```
{-# OPTIONS --guardedness --sized-types #-}
{-# OPTIONS --backtracking-instance-search --instance-search-depth 1 #-}
-- {-# OPTIONS --allow-unsolved-metas #-}

open import Preliminaries.Base
module General.Terms (R : CommutativeRing) where

open import Preliminaries.Algebra R
open import Preliminaries.PolyExpr R as P
  using (PolyExpr; con; 0P; 1P)
  renaming (mkVar to mkVarP; var to varP; ⟦_⟧_ to ⟦_⟧P_; _+_ to _+P_; _*_ to _*P_; _·_ to _·P_; _≈_ to _≈P_)

private variable
  X Y Z X′ Y′ X₀ X₁ Y₀ Y₁ : Set

module Terms (X : Set) where

  infixr 9 _+_
  infixr 10 _*_ _·_

  data Term : Set where
    0T : Term
    var : (x : X) → Term
    _·_ : (c : A) (u : Term) → Term
    _+_ _*_ : (u v : Term) → Term

open Terms public
```

We can define additive inverses.

```
infix 3 -_
-_ : Term X → Term X
- p = (-R 1R) · p

infixl 9 _-_
_-_ : Term X → Term X → Term X
p - q = p + (- q)
```

```
Subst : Set → Set → Set
Subst X Y = X → Term Y

toPolyExpr : Term X → PolyExpr X
toPolyExpr 0T = 0P
toPolyExpr (var x) = varP x
toPolyExpr (c · p) = c ·P toPolyExpr p
toPolyExpr (p + q) = toPolyExpr p +P toPolyExpr q
toPolyExpr (p * q) = toPolyExpr p *P toPolyExpr q

toPolyExpr-≡ :
  ∀ (ϱ₀ : Subst X Y) (ϱ₁ : Subst X Y) →
  (∀ x → ϱ₀ x ≡ ϱ₁ x) →
  -----------------------------------------------
  ∀ x → toPolyExpr (ϱ₀ x) ≡ toPolyExpr (ϱ₁ x)

toPolyExpr-≡ ϱ₀ ϱ₁ ϱ≡ϱ′ x = cong toPolyExpr (ϱ≡ϱ′ x) 

subst : Subst X Y → Term X → Term Y
subst ϱ 0T = 0T
subst ϱ (var x) = ϱ x
subst ϱ (c · p) = c · subst ϱ p
subst ϱ (p + q) = subst ϱ p + subst ϱ q
subst ϱ (p * q) = subst ϱ p * subst ϱ q

subst-≡ : ∀ p (ϱ₀ : Subst X Y) (ϱ₁ : Subst X Y) →
  (∀ x → ϱ₀ x ≡ ϱ₁ x) →
  -----------------------------------------------
  subst ϱ₀ p ≡ subst ϱ₁ p

subst-≡ 0T ϱ₀ ϱ₁ ϱ≡ϱ′ = refl
subst-≡ (var x) ϱ₀ ϱ₁ ϱ≡ϱ′ = ϱ≡ϱ′ x
subst-≡ (c · q) ϱ₀ ϱ₁ ϱ≡ϱ′
  rewrite subst-≡ q ϱ₀ ϱ₁ ϱ≡ϱ′ = refl
subst-≡ (p + q) ϱ₀ ϱ₁ ϱ≡ϱ′
  rewrite subst-≡ p ϱ₀ ϱ₁ ϱ≡ϱ′ | subst-≡ q ϱ₀ ϱ₁ ϱ≡ϱ′ = refl
subst-≡ (p * q) ϱ₀ ϱ₁ ϱ≡ϱ′
  rewrite subst-≡ p ϱ₀ ϱ₁ ϱ≡ϱ′ | subst-≡ q ϱ₀ ϱ₁ ϱ≡ϱ′ = refl
```

```
subst-PolyExpr : ∀ p (ϱ : Subst X Y) →
  ----------------------------------------------------------------
  P.subst (toPolyExpr ∘ ϱ) (toPolyExpr p) ≡ toPolyExpr (subst ϱ p)

subst-PolyExpr 0T ϱ = refl
subst-PolyExpr (var x) ϱ = refl
subst-PolyExpr (p · q) ϱ = cong₂ P._*_ refl (subst-PolyExpr q ϱ)
subst-PolyExpr (p + q) ϱ = cong₂ P._+_ (subst-PolyExpr p ϱ) (subst-PolyExpr q ϱ)
subst-PolyExpr (p * q) ϱ = cong₂ P._*_ (subst-PolyExpr p ϱ) (subst-PolyExpr q ϱ)

subst-subst :
  ∀ p (ϱ₀ : Subst X Y) (ϱ₁ : Subst Y Z) →
  -----------------------------------------------
  subst ϱ₁ (subst ϱ₀ p) ≡ subst (subst ϱ₁ ∘ ϱ₀) p

subst-subst 0T _ _ = refl
subst-subst (var x) _ _ = refl
subst-subst (c · p) ϱ₀ ϱ₁ = cong (_·_ c) (subst-subst p ϱ₀ ϱ₁)
subst-subst (p + q) ϱ₀ ϱ₁ = cong₂ _+_ (subst-subst p ϱ₀ ϱ₁) (subst-subst q ϱ₀ ϱ₁)
subst-subst (p * q) ϱ₀ ϱ₁ = cong₂ _*_ (subst-subst p ϱ₀ ϱ₁) (subst-subst q ϱ₀ ϱ₁)
```

```
open import Preliminaries.Vector
Var = Fin

private variable m n k : ℕ

TE : (m : ℕ) → Set
TE m = Term (Var m)

VSubst : ℕ → Set → Set
VSubst m X = Vec (Term X) m

substᵥ : VSubst n X → TE n → Term X
substᵥ ϱ p = subst (lookup ϱ) p

[_]ᵥ_ : TE n → VSubst n X → Term X
[ p ]ᵥ ϱ = substᵥ ϱ p

subst-substᵥ :
  ∀ p (ϱ₀ : VSubst m (Var n)) (ϱ₁ : VSubst n X) →
  -------------------------------------------------------
  substᵥ ϱ₁ (substᵥ ϱ₀ p) ≡ substᵥ (map (substᵥ ϱ₁) ϱ₀) p

subst-substᵥ p ϱ₀ ϱ₁ =
    begin
      substᵥ ϱ₁ (substᵥ ϱ₀ p)
        ≡⟨⟩
      subst (lookup ϱ₁) (subst (lookup ϱ₀) p)
        ≡⟨ subst-subst p (lookup ϱ₀) (lookup ϱ₁) ⟩
      subst (subst (lookup ϱ₁) ∘ lookup ϱ₀) p
        ≡⟨ subst-≡ p _ _ (lookup-map (subst (lookup ϱ₁)) ϱ₀) ⟨
      subst (lookup (map (subst (lookup ϱ₁)) ϱ₀)) p ≡⟨⟩
      substᵥ (map (substᵥ ϱ₁) ϱ₀) p
    ∎ where open ≡-Eq

infix 101 [_]⟨_⟩
[_]⟨_⟩ : TE 1 → Term X → Term X
[ p ]⟨ q ⟩ = substᵥ (q ∷ []) p

infix 101 [_]⟨_,_,_,_⟩
[_]⟨_,_,_,_⟩ : TE 4 → Term X → Term X → Term X → Term X → Term X
[ p ]⟨ p0 , p1 , p2 , p3 ⟩ = subst (lookup (p0 ∷ p1 ∷ p2 ∷ p3 ∷ [])) p 

infix 101 [_]⟨_,_,_,_,_⟩
[_]⟨_,_,_,_,_⟩ : TE 5 → Term X → Term X → Term X → Term X → Term X → Term X
[ p ]⟨ p0 , p1 , p2 , p3 , p4 ⟩ = subst (lookup (p0 ∷ p1 ∷ p2 ∷ p3 ∷ p4 ∷ [])) p

infix 101 [_]⟨_,_,_,_,_,_⟩
[_]⟨_,_,_,_,_,_⟩ : TE 6 → Term X → Term X → Term X → Term X → Term X → Term X → Term X
[ p ]⟨ p0 , p1 , p2 , p3 , p4 , p5 ⟩ = subst (lookup (p0 ∷ p1 ∷ p2 ∷ p3 ∷ p4 ∷ p5 ∷ [])) p
```

## Variables

We define a simple facility `mkVar m : PE n` for constructing a variable of type `PE n`.
We use instance arguments to automatically construct a proof that `m < n`.

```
open import Data.Nat.Properties

<-forward : m < n → m < suc n
<-forward m<n = m<n⇒m<1+n m<n

<-sucn : 0 < suc n
<-sucn = s≤s z≤n

<-back : suc m < n → m < n
<-back (s≤s sm≤n) = <-forward sm≤n

instance

  -- <-ste : ⦃ m < n ⦄ → suc m < suc n
  -- <-ste {{m<n}} = s<s m<n

  m<sucm+n : ∀ {m n} → m < suc m +ℕ n
  m<sucm+n {zero} {n} =  <-sucn
  m<sucm+n {suc m} {n} = s≤s m<sucm+n

mkVar : ∀ (m : ℕ) → ⦃ m < n ⦄ → TE n
mkVar _ ⦃ m<n ⦄ = var (fromℕ< m<n)

x : TE (1 +ℕ n)
x  = mkVar 0

x′ : TE (2 +ℕ n)
x′ = mkVar 1

y : TE (3 +ℕ n)
y  = mkVar 2

y′ :  TE (4 +ℕ n)
y′ = mkVar 3

z : TE (5 +ℕ n)
z  = mkVar 4

z′ :  TE (6 +ℕ n)
z′ = mkVar 5

t :  TE (7 +ℕ n)
t = mkVar 6

x₀ : PolyExpr (Fin (1 +ℕ n))
x₀ = mkVarP 0

y₀ : PolyExpr (Fin (2 +ℕ n))
y₀ = mkVarP 1

z₀ : PolyExpr (Fin (3 +ℕ n))
z₀ = mkVarP 2
```

# Semantics

An environment `ϱ : Env X` is a function mapping variables from `X` to coefficients from `A`.

```
module Semantics where

  Env : Set → Set
  Env X = X → A
```

The semantics extends the environment from variables `X` to all terms `Term X`.

```
  infix 200 ⟦_⟧_ ⟦_⟧ᵥ_
  ⟦_⟧_ : Term X → Env X → A
  ⟦ 0T ⟧ _ = 0R
  ⟦ var x ⟧ ϱ = ϱ x
  ⟦ c · p ⟧ ϱ = c *R ⟦ p ⟧ ϱ
  ⟦ p + q ⟧ ϱ = ⟦ p ⟧ ϱ +R ⟦ q ⟧ ϱ
  ⟦ p * q ⟧ ϱ = ⟦ p ⟧ ϱ *R ⟦ q ⟧ ϱ
```

```
  VEnv : ℕ → Set
  VEnv n = Vec A n

  ⟦_⟧ᵥ_ : Term (Var n) → VEnv n → A
  ⟦ p ⟧ᵥ ϱ = ⟦ p ⟧ lookup ϱ

  ⟦_⟧⟨_,_,_,_⟩ : Term (Var 4) → A → A → A → A → A
  ⟦ p ⟧⟨ a₀ , a₁ , a₂ , a₃ ⟩ = ⟦ p ⟧ᵥ (a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ [])

  infix 30 ⟦_⟧≈_
  ⟦_⟧≈_ sem-cong :
    ∀ {ϱ₀ ϱ₁ : Env X} (p : Term X) →
    (∀ x → ϱ₀ x ≈R ϱ₁ x) →
    --------------------------------
    ⟦ p ⟧ ϱ₀ ≈R ⟦ p ⟧ ϱ₁

  ⟦ 0T ⟧≈ _ = R-refl
  ⟦ var x ⟧≈ ϱ₀≈ϱ₁ = ϱ₀≈ϱ₁ x
  ⟦ c · p ⟧≈ ϱ₀≈ϱ₁ = R-refl ⟨ *R-cong ⟩ ⟦ p ⟧≈ ϱ₀≈ϱ₁
  ⟦ p + q ⟧≈ ϱ₀≈ϱ₁ = ⟦ p ⟧≈ ϱ₀≈ϱ₁ ⟨ +R-cong ⟩ ⟦ q ⟧≈ ϱ₀≈ϱ₁
  ⟦ p * q ⟧≈ ϱ₀≈ϱ₁ = ⟦ p ⟧≈ ϱ₀≈ϱ₁ ⟨ *R-cong ⟩ ⟦ q ⟧≈ ϱ₀≈ϱ₁

  sem-cong = ⟦_⟧≈_

  ⟦_⟧≈⟨_,_,_,_⟩ :
    ∀ {a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃} (p : Term (Var 4)) →
    a₀ ≈R b₀ → a₁ ≈R b₁ → a₂ ≈R b₂ → a₃ ≈R b₃ →
    -----------------------------------------------
    ⟦ p ⟧⟨ a₀ , a₁ , a₂ , a₃ ⟩ ≈R ⟦ p ⟧⟨ b₀ , b₁ , b₂ , b₃ ⟩

  ⟦ p ⟧≈⟨ a₀≈b₀ , a₁≈b₁ , a₂≈b₂ , a₃≈b₃ ⟩ = ⟦ p ⟧≈ go where

    go : (x : Var 4) →
      lookup (_ ∷ _ ∷ _ ∷ _ ∷ []) x ≈R
      lookup (_ ∷ _ ∷ _ ∷ _ ∷ []) x
    go zero = a₀≈b₀
    go (suc zero) = a₁≈b₁
    go (suc (suc zero)) = a₂≈b₂
    go (suc (suc (suc zero))) = a₃≈b₃
```