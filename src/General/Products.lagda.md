---
title: Products of power series 🚧
---

```
{-# OPTIONS --guardedness --sized-types #-}
-- {-# OPTIONS --allow-unsolved-metas #-}

open import Preliminaries.Base

module General.Products
    (R : CommutativeRing)
    (Σ : Set)
    where

open import Size
private variable i : Size

open import Preliminaries.Algebra R
open import Preliminaries.Vector
open import Preliminaries.PolyExpr R as P
    using (PolyExpr; con)
    renaming (⟦_⟧_ to ⟦_⟧P_)

open import General.Series R Σ hiding (≡→≈)
open import General.Terms R
    renaming (_+_ to _[+]_; _*_ to _[*]_; _·_ to _[·]_)
open import General.ProductRules R

private variable
    m n : ℕ
    X Y : Set
    f₀ f₁ f₂ f₃ f₄ f₅ : A ⟪ Σ ⟫ i
```

Definition of the product operation.

```
module Product (productRule : ProductRule) where
    open ProductRule productRule

    mutual
        infixr 7 _*_
        _*_ : A ⟪ Σ ⟫ i → A ⟪ Σ ⟫ i → A ⟪ Σ ⟫ i
        ν (f * g) = ν f *R ν g
        δ (f * g) a = ⟦ P ⟧⟨ f , δ f a , g , δ g a ⟩

        infix 200 ⟦_⟧_ ⟦_⟧ᵥ_ ⟦_⟧⟨_⟩ ⟦_⟧⟨_,_,_,_⟩ -- ⟦_⟧⟨_,_,_,_,_,_⟩
        ⟦_⟧_ : Term X → SEnv {i} X → A ⟪ Σ ⟫ i
        ⟦ 0T ⟧ ϱ = 𝟘
        ⟦ c [·] u ⟧ ϱ = c · ⟦ u ⟧ ϱ
        ⟦ var x ⟧ ϱ = ϱ x
        ⟦ p [+] q ⟧ ϱ = ⟦ p ⟧ ϱ + ⟦ q ⟧ ϱ
        ⟦ p [*] q ⟧ ϱ = ⟦ p ⟧ ϱ * ⟦ q ⟧ ϱ

        ⟦_⟧ᵥ_ : ∀ {n} → TE n → SEnvᵥ {i} n → A ⟪ Σ ⟫ i
        ⟦ p ⟧ᵥ fs = ⟦ p ⟧ (lookup fs)

        ⟦_⟧⟨_⟩ : TE 1 → A ⟪ Σ ⟫ i → A ⟪ Σ ⟫ i
        ⟦ p ⟧⟨ f ⟩ = ⟦ p ⟧ᵥ (f ∷ [])

        ⟦_⟧⟨_,_,_,_⟩ : TE 4 → A ⟪ Σ ⟫ i → A ⟪ Σ ⟫ i → A ⟪ Σ ⟫ i → A ⟪ Σ ⟫ i → A ⟪ Σ ⟫ i
        ⟦ p ⟧⟨ f₀ , f₁ , f₂ , f₃ ⟩ = ⟦ p ⟧ᵥ (f₀ ∷ f₁ ∷ f₂ ∷ f₃ ∷ [])

        ⟦_⟧⟨_,_,_,_,_,_⟩ : TE 6 → A ⟪ Σ ⟫ i → A ⟪ Σ ⟫ i → A ⟪ Σ ⟫ i →
            A ⟪ Σ ⟫ i → A ⟪ Σ ⟫ i → A ⟪ Σ ⟫ i → A ⟪ Σ ⟫ i
        ⟦ p ⟧⟨ f₀ , f₁ , f₂ , f₃ , f₄ , f₅ ⟩ = ⟦ p ⟧ᵥ (f₀ ∷ f₁ ∷ f₂ ∷ f₃ ∷ f₄ ∷ f₅ ∷ [])
```

## Properties

```
    mutual
        -- equivalent series enviroments yield equivalent series
        infix 30 ⟦_⟧≈_
        ⟦_⟧≈_ sem-cong :
            ∀ {ϱ₀ ϱ₁ : SEnv X} (p : Term X) →
            ϱ₀ ≈ϱ[ i ] ϱ₁ →
            -----------------------------------
            ⟦ p ⟧ ϱ₀ ≈[ i ] ⟦ p ⟧ ϱ₁

        ⟦ 0T ⟧≈ _ = ≈-refl
        ⟦ var x ⟧≈ ϱ₀≈ϱ₁ = ϱ₀≈ϱ₁ x
        ⟦ c [·] p ⟧≈ ϱ₀≈ϱ₁ = R-refl ·≈ (⟦ p ⟧≈ ϱ₀≈ϱ₁)
        ⟦ p [+] q ⟧≈ ϱ₀≈ϱ₁ = ⟦ p ⟧≈ ϱ₀≈ϱ₁ +≈ ⟦ q ⟧≈ ϱ₀≈ϱ₁
        ⟦ p [*] q ⟧≈ ϱ₀≈ϱ₁ = ⟦ p ⟧≈ ϱ₀≈ϱ₁ *≈ ⟦ q ⟧≈ ϱ₀≈ϱ₁

        sem-cong = ⟦_⟧≈_

        sem-congᵥ :
            ∀ {fs gs : SEnvᵥ n} (p : TE n) →
            fs ≈ᵥ[ i ] gs → ⟦ p ⟧ᵥ fs ≈[ i ] ⟦ p ⟧ᵥ gs
        sem-congᵥ p fs≈gs = sem-cong p (build-≈ϱ fs≈gs)

        infix 20 _*≈_
        _*≈_ *-cong : Congruent₂ (λ f g → f ≈[ i ] g) _*_
        ν-≈ (f≈g *≈ h≈i) = *R-cong (ν-≈ f≈g) (ν-≈ h≈i)
        δ-≈ (f≈g *≈ h≈i) a = sem-congᵥ P [ f≈g , δ-≈ f≈g a , h≈i , δ-≈ h≈i a ]

        *-cong = _*≈_
```

The operation of constant term extraction `ν` is a homomorphism
from the series algebra to the underlying ring `R`.

```
    open Semantics
        renaming (⟦_⟧_ to T⟦_⟧_; ⟦_⟧ᵥ_ to T⟦_⟧ᵥ_; sem-cong to sem-congT)

    eval-ν :
        ∀ (p : Term X) (ϱ : SEnv X) →
        -------------------------------
        ν (⟦ p ⟧ ϱ) ≈R T⟦ p ⟧ (ν ∘ ϱ)
    
    eval-ν 0T ϱ = R-refl
    eval-ν (var x) ϱ = R-refl
    eval-ν (c [·] q) ϱ = R-refl ⟨ *R-cong ⟩ eval-ν q ϱ
    eval-ν (p [+] q) ϱ = eval-ν p ϱ ⟨ +R-cong ⟩ eval-ν q ϱ
    eval-ν (p [*] q) ϱ = eval-ν p ϱ ⟨ *R-cong ⟩ eval-ν q ϱ

    eval-νᵥ :
        ∀ (p : Term (Var n)) (ϱ : SEnvᵥ n) →
        -------------------------------
        ν (⟦ p ⟧ᵥ ϱ) ≈R T⟦ p ⟧ᵥ (map ν ϱ)

    eval-νᵥ p ϱ =
        begin
            ν (⟦ p ⟧ᵥ ϱ)
                ≈⟨ eval-ν p (lookup ϱ) ⟩
            T⟦ p ⟧ (ν ∘ lookup ϱ)
                ≈⟨ sem-congT p (λ x → ≡→≈ $ sym $ lookup-map ν ϱ x) ⟩
            T⟦ p ⟧ (lookup $ map ν ϱ)
                ≈⟨⟩
            T⟦ p ⟧ᵥ (map ν ϱ)
        ∎ where open EqR
```

Substitution and evalation commute.

```
    eval-subst :
        ∀ (p : Term X) {ϱ : Subst X Y} {env : SEnv Y} →
        -------------------------------------------------
        ⟦ subst ϱ p ⟧ env ≈ ⟦ p ⟧ (⟦_⟧ env ∘ ϱ)

    eval-subst 0T = ≈-refl
    eval-subst (var x) = ≈-refl
    eval-subst (c [·] q) = R-refl ·≈ eval-subst q
    eval-subst (p [+] q) = eval-subst p +≈ eval-subst q
    eval-subst (p [*] q) = eval-subst p *≈ eval-subst q

    eval-substᵥ :
        ∀ (p : TE m) {qs : VSubst m X} {fs : SEnv X} →
        ------------------------------------------------
        ⟦ substᵥ qs p ⟧ fs ≈ ⟦ p ⟧ᵥ (map (⟦_⟧ fs) qs)

    eval-substᵥ p {qs} {fs} =
        begin
            ⟦ substᵥ qs p ⟧ fs 
                ≈⟨⟩
            ⟦ subst (lookup qs) p ⟧ fs 
                ≈⟨ eval-subst p {ϱ = lookup qs} {env = fs} ⟩
            ⟦ p ⟧ (λ x → ⟦ lookup qs x ⟧ fs)
                ≈⟨ sem-cong p (≡→≈ϱ (lookup-map _ qs)) ⟨
            ⟦ p ⟧ (lookup (map (⟦_⟧ fs) qs))
                ≈⟨⟩
            ⟦ p ⟧ᵥ (map (λ q → ⟦ q ⟧ fs) qs)
        ∎ where open EqS
```

# Endomorphism lemma

```
    open Properties

    Endomorphic-* Endomorphic-ν : (F : A ⟪ Σ ⟫ → A ⟪ Σ ⟫) {i : Size} → Set
    Endomorphic-* F {i} = ∀ f g → F (f * g) ≈[ i ] F f * F g
    Endomorphic-ν F {i} = ∀ {f} → ν (F f) ≈R ν f

    record IsEndomorphism (F : A ⟪ Σ ⟫ → A ⟪ Σ ⟫) {i : Size} : Set where
        field
            ·-end : Endomorphic-· F
            +-end : Endomorphic-+ F
            𝟘-end : Endomorphic-𝟘 F
            *-end : Endomorphic-* F {i}

    open IsEndomorphism public

    -- endomorphism lemma
    -- an endomorphism of the series ring commutes with the semantics of polynomial expressions
    end :
        ∀ {F : A ⟪ Σ ⟫ → A ⟪ Σ ⟫} (p : Term X) {ϱ : SEnv X} →
        IsEndomorphism F {i} →
        ------------------------------------------------------
        F (⟦ p ⟧ ϱ) ≈[ i ] ⟦ p ⟧ (F ∘ ϱ)

    end 0T endF = endF .𝟘-end
    end (var x) _ = ≈-refl

    end {F = F} (c [·] p) {ϱ} endF =
        begin
            F (⟦ c [·] p ⟧ ϱ)
                ≈⟨⟩
            F (c · ⟦ p ⟧ ϱ)
                ≈⟨ ·-end endF _ _ ⟩
            c · F (⟦ p ⟧ ϱ)
                ≈⟨ R-refl ·≈ end p endF ⟩
            c · ⟦ p ⟧ (F ∘ ϱ)
                ≈⟨⟩
            ⟦ c [·] p ⟧ (F ∘ ϱ)
        ∎ where open EqS

    end {F = F} (p [+] q) {ϱ} endF =
        begin
            F (⟦ p [+] q ⟧ ϱ)
                ≈⟨⟩
            F (⟦ p ⟧ ϱ + ⟦ q ⟧ ϱ)
                ≈⟨ +-end endF _ _ ⟩
            F (⟦ p ⟧ ϱ) + F (⟦ q ⟧ ϱ)
                ≈⟨ end p endF +≈ end q endF ⟩
            (⟦ p ⟧ (F ∘ ϱ)) + (⟦ q ⟧ (F ∘ ϱ))
                ≈⟨⟩
            ⟦ p [+] q ⟧ (F ∘ ϱ)
        ∎ where open EqS

    end {F = F} (p [*] q) {ϱ} endF =
        begin
            F (⟦ p [*] q ⟧ ϱ)
                ≈⟨⟩
            F (⟦ p ⟧ ϱ * ⟦ q ⟧ ϱ)
                ≈⟨ *-end endF _ _ ⟩
            F (⟦ p ⟧ ϱ) * F (⟦ q ⟧ ϱ)
                ≈⟨ end p endF *≈ end q endF ⟩
            (⟦ p ⟧ (F ∘ ϱ)) * (⟦ q ⟧ (F ∘ ϱ))
                ≈⟨⟩
            ⟦ p [*] q ⟧ (F ∘ ϱ)
        ∎ where open EqS


    endᵥ :
        ∀ {F : A ⟪ Σ ⟫ → A ⟪ Σ ⟫} (p : TE n) (ϱ : SEnvᵥ n) →
        IsEndomorphism F {i} →
        ------------------------------------------------------
        F (⟦ p ⟧ᵥ ϱ) ≈[ i ] ⟦ p ⟧ᵥ (map F ϱ)

    endᵥ {F = F} p ϱ endF =
        begin
            F (⟦ p ⟧ᵥ ϱ)
                ≈⟨⟩
            F (⟦ p ⟧ (lookup ϱ))
                ≈⟨ end p endF ⟩
            ⟦ p ⟧ (F ∘ (lookup ϱ))
                ≈⟨ sem-cong p (≡→≈ϱ (lookup-map F ϱ)) ⟨
            ⟦ p ⟧ (lookup (map F ϱ))
                ≈⟨⟩
            ⟦ p ⟧ᵥ (map F ϱ)
        ∎ where open EqS
```

# Examples

```
open Examples Σ
module Hadamard where

    open Product ruleHadamard

    agree : ∀ (f g : A ⟪ Σ ⟫) → f * g ≈[ i ] f ⊙ g
    ν-≈ (agree f g) = R-refl
    δ-≈ (agree f g) a =
        begin
            δ (f * g) a ≈⟨⟩
            δ f a * δ g a ≈⟨ agree _ _ ⟩
            δ f a ⊙ δ g a ≈⟨⟩
            δ (f ⊙ g) a
        ∎ where open EqS            

module Shuffle where

    open Product ruleShuffle

    agree : ∀ (f g : A ⟪ Σ ⟫) → f * g ≈[ i ] f ⧢ g
    ν-≈ (agree f g) = R-refl
    δ-≈ (agree f g) a =
        begin
            δ (f * g) a ≈⟨⟩
            δ f a * g + f * δ g a ≈⟨ agree _ _ ⟨ +-cong ⟩ agree _ _ ⟩
            δ f a ⧢ g + f ⧢ δ g a ≈⟨⟩
            δ (f ⧢ g) a
        ∎ where open EqS   

module Infiltration where

    open Product ruleInfiltration

    agree : ∀ (f g : A ⟪ Σ ⟫) → f * g ≈[ i ] f ↑ g
    ν-≈ (agree f g) = R-refl
    δ-≈ (agree f g) a =
        begin
            δ (f * g) a ≈⟨⟩
            δ f a * g + f * δ g a + δ f a * δ g a ≈⟨ agree _ _ ⟨ +-cong ⟩ (agree _ _ ⟨ +-cong ⟩ agree _ _) ⟩
            δ f a ↑ g + f ↑ δ g a + δ f a ↑ δ g a ≈⟨⟩
            δ (f ↑ g) a
        ∎ where open EqS   
```