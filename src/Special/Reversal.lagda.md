---
title: Reversal of formal series 🚧
---

```
{-# OPTIONS --guardedness --sized-types #-}
-- {-# OPTIONS --allow-unsolved-metas #-}

open import Preliminaries.Base hiding (_++_)
open import General.ProductRules

module Special.Reversal
    (R : CommutativeRing)
    (Σ : Set)
    (P : ProductRule R)
    where

open import Size
open import Preliminaries.List
open import Preliminaries.Algebra R
open import Preliminaries.PolyExpr R
    using (PolyExpr; con)
    renaming (subst to P-subst; ⟦_⟧_ to P⟦_⟧_)

open import General.Series R Σ
open import General.Terms R renaming (_+_ to _[+]_; _*_ to _[*]_; _·_ to _[·]_) hiding (x; y; z; t)
open import General.Products R Σ
open import General.Automata R Σ P
open import General.Reversal R Σ
open import General.ReversalEnd R Σ P

open Product P
-- open Reversal P

open import Special.Polynomials R as P renaming (_≈_ to _P≈_)
open import Special.ProductRules R

private variable
    i : Size
    n : ℕ
```

```
ΔʳΔˡ : Set
ΔʳΔˡ = ∀ a b α → Δʳ b ↑ (Δˡ a ↑ α) P≈ Δˡ a ↑ (Δʳ b ↑ α)
```

```
module Assumptions (a b : Σ) (f g : A ⟪ Σ ⟫) where

    data aXb : *X* → Set where
        y : aXb (ε x[ f ] ε)
        ay : aXb ((a ∷ ε) x[ f ] ε)
        yb : aXb (ε x[ f ] (b ∷ ε))
        ayb : aXb ((a ∷ ε) x[ f ] (b ∷ ε))
        z : aXb (ε x[ g ] ε)
        az : aXb ((a ∷ ε) x[ g ] ε)
        zb : aXb (ε x[ g ] (b ∷ ε))
        azb : aXb ((a ∷ ε) x[ g ] (b ∷ ε))

    data aX : *X* → Set where
        y : aX (ε x[ f ] ε)
        ay : aX ((a ∷ ε) x[ f ] ε)
        z : aX (ε x[ g ] ε)
        az : aX ((a ∷ ε) x[ g ] ε)

    data Xb : *X* → Set where
        y : Xb (ε x[ f ] ε)
        yb : Xb (ε x[ f ] (b ∷ ε))
        z : Xb (ε x[ g ] ε)
        zb : Xb (ε x[ g ] (b ∷ ε))

    data εXε : *X* → Set where
        y : εXε (ε x[ f ] ε)
        z : εXε (ε x[ g ] ε)

    ε→a : Term (∃[ x ] εXε x) → Term (∃[ x ] aX x)
    ε→a 0T = 0T
    ε→a (var (x ,, y)) = var (x ,, y)
    ε→a (var (x ,, z)) = var (x ,, z)
    ε→a (c [·] u) = c [·] ε→a u
    ε→a (u [+] v) = ε→a u [+] ε→a v
    ε→a (u [*] v) = ε→a u [*] ε→a v

    ε→b : Term (∃[ x ] εXε x) → Term (∃[ x ] Xb x)
    ε→b 0T = 0T
    ε→b (var (x ,, y)) = var (x ,, y)
    ε→b (var (x ,, z)) = var (x ,, z)
    ε→b (c [·] u) = c [·] ε→b u
    ε→b (u [+] v) = ε→b u [+] ε→b v
    ε→b (u [*] v) = ε→b u [*] ε→b v

    a→ab : Term (∃[ x ] aX x) → Term (∃[ x ] aXb x)
    a→ab 0T = 0T
    a→ab (var (x ,, y)) = var (x ,, y)
    a→ab (var (x ,, ay)) = var (x ,, ay)
    a→ab (var (x ,, z)) = var (x ,, z)
    a→ab (var (x ,, az)) = var (x ,, az)
    a→ab (c [·] u) = c [·] a→ab u
    a→ab (u [+] v) = a→ab u [+] a→ab v
    a→ab (u [*] v) = a→ab u [*] a→ab v

    b→ab : Term (∃[ x ] Xb x) → Term (∃[ x ] aXb x)
    b→ab 0T = 0T
    b→ab (var (x ,, y)) = var (x ,, y)
    b→ab (var (x ,, yb)) = var (x ,, yb)
    b→ab (var (x ,, z)) = var (x ,, z)
    b→ab (var (x ,, zb)) = var (x ,, zb)
    b→ab (c [·] u) = c [·] b→ab u
    b→ab (u [+] v) = b→ab u [+] b→ab v
    b→ab (u [*] v) = b→ab u [*] b→ab v

    Δˡε : Term (∃[ x ] εXε x) → Term (∃[ x ] aX x)
    Δˡε 0T = 0T
    Δˡε (var (_ ,, y)) = var (_ ,, ay)
    Δˡε (var (_ ,, z)) = var (_ ,, az)
    Δˡε (c [·] γ) = c [·] Δˡε γ
    Δˡε (γ [+] δ) = Δˡε γ [+] Δˡε δ
    Δˡε (γ [*] δ) = [ P ]⟨ ε→a γ , Δˡε γ , ε→a δ , Δˡε δ ⟩

    Δʳε : Term (∃[ x ] εXε x) → Term (∃[ x ] Xb x)
    Δʳε 0T = 0T
    Δʳε (var (_ ,, y)) = var (_ ,, yb)
    Δʳε (var (_ ,, z)) = var (_ ,, zb)
    Δʳε (c [·] γ) = c [·] Δʳε γ
    Δʳε (γ [+] δ) = Δʳε γ [+] Δʳε δ
    Δʳε (γ [*] δ) = [ P ]⟨ ε→b γ , Δʳε γ , ε→b δ , Δʳε δ ⟩

    Δˡb : Term (∃[ x ] Xb x) → Term (∃[ x ] aXb x)
    Δˡb 0T = 0T
    Δˡb (var (_ ,, y)) = var (_ ,, ay)
    Δˡb (var (_ ,, yb)) = var (_ ,, ayb)
    Δˡb (var (_ ,, z)) = var (_ ,, az)
    Δˡb (var (_ ,, zb)) = var (_ ,, azb)
    Δˡb (c [·] γ) = c [·] Δˡb γ
    Δˡb (γ [+] δ) = Δˡb γ [+] Δˡb δ
    Δˡb (γ [*] δ) = [ P ]⟨ b→ab γ , Δˡb γ , b→ab δ , Δˡb δ ⟩

    Δʳa : Term (∃[ x ] aX x) → Term (∃[ x ] aXb x)
    Δʳa 0T = 0T
    Δʳa (var (_ ,, y)) = var (_ ,, yb)
    Δʳa (var (_ ,, ay)) = var (_ ,, ayb)
    Δʳa (var (_ ,, z)) = var (_ ,, zb)
    Δʳa (var (_ ,, az)) = var (_ ,, azb)
    Δʳa (c [·] γ) = c [·] Δʳa γ
    Δʳa (γ [+] δ) = Δʳa γ [+] Δʳa δ
    Δʳa (γ [*] δ) = [ P ]⟨ a→ab γ , Δʳa γ , a→ab δ , Δʳa δ ⟩
    
    t : Term (∃[ x ] εXε x)
    t = var (ε x[ f ] ε ,, y) [*] var (ε x[ g ] ε ,, z)

ΔʳΔˡ-var : Set
ΔʳΔˡ-var =
    ∀ a b f g →
    let open Assumptions a b f g in
    --------------------------
    Δʳa (Δˡε t) P≈ Δˡb (Δʳε t)

-- Δʳ b ↑ (Δˡ a ↑ (var (ε x[ f ] ε) [*] var (ε x[ g ] ε))) P≈ Δˡ a ↑ (Δʳ b ↑ (var (ε x[ f ] ε) [*] var (ε x[ g ] ε)))
```

```
module _ (special : Special P) where

    open import Special.Automata R Σ P special

    ΔʳΔˡ→⟦ΔʳΔˡ⟧ : ΔʳΔˡ → ⟦ΔʳΔˡ⟧
    ΔʳΔˡ→⟦ΔʳΔˡ⟧ ass a b α = semantic-invariance S (ass a b α)

    ΔʳΔˡ-var→ΔʳΔˡ : ΔʳΔˡ-var → ΔʳΔˡ
    ΔʳΔˡ-var→ΔʳΔˡ ass-var a b = go where

        go : ∀ α → Δʳ b ↑ (Δˡ a ↑ α) P≈ Δˡ a ↑ (Δʳ b ↑ α)
        go 0T = P.≈-refl
        go (var (u x[ f ] v)) = P.≈-refl
        go (c [·] α) with go α
        ... | ind = P.·-cong R-refl ind
        go (α [+] β) with go α | go β
        ... | ind₀ | ind₁ = ind₀ ⟨ P.+-cong ⟩ ind₁
        go (α [*] β) with go α | go β
        ... | ind₀ | ind₁ = proof where

            f = 𝟘
            g = 𝟘

            open Assumptions a b f g

            ε→ab : Term (∃[ x ] εXε x) → Term (∃[ x ] aXb x)
            ε→ab 0T = 0T
            ε→ab (var (x ,, y)) = var (x ,, y)
            ε→ab (var (x ,, z)) = var (x ,, z)
            ε→ab (c [·] u) = c [·] ε→ab u
            ε→ab (u [+] v) = ε→ab u [+] ε→ab v
            ε→ab (u [*] v) = ε→ab u [*] ε→ab v

            ρ-ε : Subst (∃[ x ] εXε x) *X*
            ρ-ε (_ ,, y) = α
            ρ-ε (_ ,, z) = β

            ρ-a : Subst (∃[ x ] aX x) *X*
            ρ-a (_ ,, y) = α
            ρ-a (_ ,, ay) = Δˡ a ↑ α
            ρ-a (_ ,, z) = β
            ρ-a (_ ,, az) = Δˡ a ↑ β

            ρ-b : Subst (∃[ x ] Xb x) *X*
            ρ-b (_ ,, y) = α
            ρ-b (_ ,, yb) = Δʳ b ↑ α
            ρ-b (_ ,, z) = β
            ρ-b (_ ,, zb) = Δʳ b ↑ β

            ρ-ab : Subst (∃[ x ] aXb x) *X*
            ρ-ab (_ ,, y) = α
            ρ-ab (_ ,, ay) = Δˡ a ↑ α
            ρ-ab (_ ,, yb) = Δʳ b ↑ α
            ρ-ab (_ ,, ayb) = Δʳ b ↑ (Δˡ a ↑ α)
            ρ-ab (_ ,, z) = β
            ρ-ab (_ ,, az) = Δˡ a ↑ β
            ρ-ab (_ ,, zb) = Δʳ b ↑ β
            ρ-ab (_ ,, azb) = Δʳ b ↑ (Δˡ a ↑ β)

            h-a :
                (γ : Term (∃[ x ] εXε x)) →
                --------------------------------
                subst ρ-ε γ P≈ subst ρ-a (ε→a γ)
                
            h-a 0T = P.≈-refl
            h-a (var (_ ,, y)) = P.≈-refl
            h-a (var (_ ,, z)) = P.≈-refl
            h-a (c [·] γ) = R-refl ⟨ P.·-cong ⟩ h-a γ
            h-a (γ [+] δ) = h-a γ ⟨ P.+-cong ⟩ h-a δ
            h-a (γ [*] δ) = h-a γ ⟨ P.*-cong ⟩ h-a δ

            h-b :
                (γ : Term (∃[ x ] εXε x)) →
                --------------------------------
                subst ρ-ε γ P≈ subst ρ-b (ε→b γ)
                
            h-b 0T = P.≈-refl
            h-b (var (_ ,, y)) = P.≈-refl
            h-b (var (_ ,, z)) = P.≈-refl
            h-b (c [·] γ) = R-refl ⟨ P.·-cong ⟩ h-b γ
            h-b (γ [+] δ) = h-b γ ⟨ P.+-cong ⟩ h-b δ
            h-b (γ [*] δ) = h-b γ ⟨ P.*-cong ⟩ h-b δ

            subst-b→ab :
                (γ : Term (∃[ x ] Xb x)) →
                --------------------------------
                subst ρ-b γ P≈ subst ρ-ab (b→ab γ)
                
            subst-b→ab 0T = P.≈-refl
            subst-b→ab (var (_ ,, y)) = P.≈-refl
            subst-b→ab (var (_ ,, yb)) = P.≈-refl
            subst-b→ab (var (_ ,, z)) = P.≈-refl
            subst-b→ab (var (_ ,, zb)) = P.≈-refl
            subst-b→ab (c [·] γ) = R-refl ⟨ P.·-cong ⟩ subst-b→ab γ
            subst-b→ab (γ [+] δ) = subst-b→ab γ ⟨ P.+-cong ⟩ subst-b→ab δ
            subst-b→ab (γ [*] δ) = subst-b→ab γ ⟨ P.*-cong ⟩ subst-b→ab δ

            subst-a→ab :
                (γ : Term (∃[ x ] aX x)) →
                --------------------------------
                subst ρ-a γ P≈ subst ρ-ab (a→ab γ)
                
            subst-a→ab 0T = P.≈-refl
            subst-a→ab (var (_ ,, y)) = P.≈-refl
            subst-a→ab (var (_ ,, ay)) = P.≈-refl
            subst-a→ab (var (_ ,, z)) = P.≈-refl
            subst-a→ab (var (_ ,, az)) = P.≈-refl
            subst-a→ab (c [·] γ) = R-refl ⟨ P.·-cong ⟩ subst-a→ab γ
            subst-a→ab (γ [+] δ) = subst-a→ab γ ⟨ P.+-cong ⟩ subst-a→ab δ
            subst-a→ab (γ [*] δ) = subst-a→ab γ ⟨ P.*-cong ⟩ subst-a→ab δ

            Δˡε-lem :
                (γ : Term (∃[ x ] εXε x)) →
                ---------------------------------------
                Δˡ a ↑ subst ρ-ε γ P≈ subst ρ-a (Δˡε γ)

            Δˡε-lem 0T = P.≈-refl
            Δˡε-lem (var (_ ,, y)) = P.≈-refl
            Δˡε-lem (var (_ ,, z)) = P.≈-refl
            Δˡε-lem (c [·] γ) = R-refl ⟨ P.·-cong ⟩ Δˡε-lem γ
            Δˡε-lem (γ [+] δ) = Δˡε-lem γ ⟨ P.+-cong ⟩ Δˡε-lem δ
            Δˡε-lem (γ [*] δ) =
                begin
                    Δˡ a ↑ subst ρ-ε (γ [*] δ)
                        ≈⟨⟩
                    [ P ]⟨ subst ρ-ε γ , Δˡ a ↑ subst ρ-ε γ , subst ρ-ε δ , Δˡ a ↑ subst ρ-ε δ ⟩
                        ≈⟨ subst-inv′ᵥ P (h-a γ ∷-≈ Δˡε-lem γ ∷-≈ h-a δ ∷-≈ Δˡε-lem δ ∷-≈ []-≈) ⟩
                    [ P ]⟨ subst ρ-a (ε→a γ) , subst ρ-a (Δˡε γ) , subst ρ-a (ε→a δ) , subst ρ-a (Δˡε δ) ⟩
                        ≡⟨ subst-substᵥ P (_ ∷ _ ∷ _ ∷ _ ∷ []) ρ-a ⟨
                    subst ρ-a [ P ]⟨ ε→a γ , Δˡε γ , ε→a δ , Δˡε δ ⟩
                ∎ where open EqP

            Δʳε-lem :
                ∀ (γ : Term (∃[ x ] εXε x)) →
                ---------------------------------
                Δʳ b ↑ (subst ρ-ε γ) P≈ subst ρ-b (Δʳε γ)

            Δʳε-lem 0T = P.≈-refl
            Δʳε-lem (var (_ ,, y)) = P.≈-refl
            Δʳε-lem (var (_ ,, z)) = P.≈-refl
            Δʳε-lem (c [·] γ) = R-refl ⟨ P.·-cong ⟩ Δʳε-lem γ
            Δʳε-lem (γ [+] δ) = Δʳε-lem γ ⟨ P.+-cong ⟩ Δʳε-lem δ
            Δʳε-lem (γ [*] δ) =
                begin
                    Δʳ b ↑ subst ρ-ε (γ [*] δ)
                        ≈⟨⟩
                    [ P ]⟨ subst ρ-ε γ , Δʳ b ↑ subst ρ-ε γ , subst ρ-ε δ , Δʳ b ↑ subst ρ-ε δ ⟩
                        ≈⟨ subst-inv′ᵥ P (h-b γ ∷-≈ Δʳε-lem γ ∷-≈ h-b δ ∷-≈ Δʳε-lem δ ∷-≈ []-≈) ⟩
                    [ P ]⟨ subst ρ-b (ε→b γ) , subst ρ-b (Δʳε γ) , subst ρ-b (ε→b δ) , subst ρ-b (Δʳε δ) ⟩
                        ≡⟨ subst-substᵥ P (_ ∷ _ ∷ _ ∷ _ ∷ []) ρ-b ⟨
                    subst ρ-b (Δʳε (γ [*] δ))
                ∎ where open EqP

            Δˡb-lem :
                ∀ (γ : Term (∃[ x ] Xb x)) →
                ---------------------------------
                Δˡ a ↑ (subst ρ-b γ) P≈ subst ρ-ab (Δˡb γ)

            Δˡb-lem 0T = P.≈-refl
            Δˡb-lem (var (_ ,, y)) = P.≈-refl
            Δˡb-lem (var (_ ,, yb)) = P.≈-sym ind₀
            Δˡb-lem (var (_ ,, z)) = P.≈-refl
            Δˡb-lem (var (_ ,, zb)) = P.≈-sym ind₁
            Δˡb-lem (c [·] γ) = R-refl ⟨ P.·-cong ⟩ Δˡb-lem γ
            Δˡb-lem (γ [+] δ) = Δˡb-lem γ ⟨ P.+-cong ⟩ Δˡb-lem δ
            Δˡb-lem (γ [*] δ) =
                begin
                    Δˡ a ↑ subst ρ-b (γ [*] δ)
                        ≈⟨⟩
                    [ P ]⟨ subst ρ-b γ , Δˡ a ↑ subst ρ-b γ , subst ρ-b δ , Δˡ a ↑ subst ρ-b δ ⟩
                        ≈⟨ subst-inv′ᵥ P (subst-b→ab γ ∷-≈ Δˡb-lem γ ∷-≈ subst-b→ab δ ∷-≈ Δˡb-lem δ ∷-≈ []-≈) ⟩
                    [ P ]⟨ subst ρ-ab (b→ab γ) , subst ρ-ab (Δˡb γ) , subst ρ-ab (b→ab δ) , subst ρ-ab (Δˡb δ) ⟩
                        ≡⟨ subst-substᵥ P (_ ∷ _ ∷ _ ∷ _ ∷ []) ρ-ab ⟨
                    subst ρ-ab (Δˡb (γ [*] δ))
                ∎ where open EqP

            Δʳa-lem :
                ∀ (γ : Term (∃[ x ] aX x)) →
                ---------------------------------
                Δʳ b ↑ (subst ρ-a γ) P≈ subst ρ-ab (Δʳa γ)

            Δʳa-lem 0T = P.≈-refl
            Δʳa-lem (var (_ ,, y)) = P.≈-refl
            Δʳa-lem (var (_ ,, ay)) = P.≈-refl
            Δʳa-lem (var (_ ,, z)) = P.≈-refl
            Δʳa-lem (var (_ ,, az)) = P.≈-refl
            Δʳa-lem (c [·] γ) = R-refl ⟨ P.·-cong ⟩ Δʳa-lem γ
            Δʳa-lem (γ [+] δ) = Δʳa-lem γ ⟨ P.+-cong ⟩ Δʳa-lem δ
            Δʳa-lem (γ [*] δ) =
                begin
                    Δʳ b ↑ subst ρ-a (γ [*] δ)
                        ≈⟨⟩
                    [ P ]⟨ subst ρ-a γ , Δʳ b ↑ subst ρ-a γ , subst ρ-a δ , Δʳ b ↑ subst ρ-a δ ⟩
                        ≈⟨ subst-inv′ᵥ P (subst-a→ab γ ∷-≈ Δʳa-lem γ ∷-≈ subst-a→ab δ ∷-≈ Δʳa-lem δ ∷-≈ []-≈) ⟩
                    [ P ]⟨ subst ρ-ab (a→ab γ) , subst ρ-ab (Δʳa γ) , subst ρ-ab (a→ab δ) , subst ρ-ab (Δʳa δ) ⟩
                        ≡⟨ subst-substᵥ P (_ ∷ _ ∷ _ ∷ _ ∷ []) ρ-ab ⟨
                    subst ρ-ab (Δʳa (γ [*] δ))
                ∎ where open EqP

            proof : Δʳ b ↑ (Δˡ a ↑ (α [*] β)) P≈ Δˡ a ↑ (Δʳ b ↑ (α [*] β))
            proof =
                begin
                    Δʳ b ↑ (Δˡ a ↑ (α [*] β))
                        ≈⟨⟩
                    Δʳ b ↑ (Δˡ a ↑ (subst ρ-ε t))
                        ≈⟨ invariance (Δʳ b) (Δˡε-lem t) ⟩
                    Δʳ b ↑ (subst ρ-a (Δˡε t))
                        ≈⟨ Δʳa-lem (Δˡε t) ⟩
                    subst ρ-ab (Δʳa (Δˡε t))
                        ≈⟨ subst-inv ρ-ab (ass-var a b f g) ⟩
                    subst ρ-ab (Δˡb (Δʳε t))
                        ≈⟨ Δˡb-lem (Δʳε t) ⟨
                    Δˡ a ↑ (subst ρ-b (Δʳε t))
                        ≈⟨ invariance (Δˡ a) (Δʳε-lem t) ⟨
                    Δˡ a ↑ (Δʳ b ↑ (subst ρ-ε t))
                        ≈⟨⟩
                    Δˡ a ↑ (Δʳ b ↑ (α [*] β))
                ∎ where open EqP

```


