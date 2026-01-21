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
open import General.Terms R renaming (_+_ to _[+]_; _*_ to _[*]_; _·_ to _[·]_) hiding (x; y; z)
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
ΔʳΔˡ-var : Set
ΔʳΔˡ-var = ∀ a b f g → Δʳ b ↑ (Δˡ a ↑ var (ε x[ f ] ε)) P≈ Δˡ a ↑ (Δʳ b ↑ var (ε x[ g ] ε))
```

```
module _ (special : Special P) where

    open import Special.Automata R Σ P special

    ΔʳΔˡ→⟦ΔʳΔˡ⟧ : ΔʳΔˡ → ⟦ΔʳΔˡ⟧
    ΔʳΔˡ→⟦ΔʳΔˡ⟧ ass a b α = semantic-invariance S (ass a b α)

    ΔʳΔˡ-var→ΔʳΔˡ : ΔʳΔˡ-var → ΔʳΔˡ
    ΔʳΔˡ-var→ΔʳΔˡ ass a b = go where

        go : ∀ α → Δʳ b ↑ (Δˡ a ↑ α) P≈ Δˡ a ↑ (Δʳ b ↑ α)
        go 0T = P.≈-refl
        go (var (u x[ f ] v)) = P.≈-refl
        go (c [·] α) with go α
        ... | ind = P.·-cong R-refl ind
        go (α [+] β) with go α | go β
        ... | ind₀ | ind₁ = ind₀ ⟨ P.+-cong ⟩ ind₁
        go (α [*] β) with go α | go β
        ... | ind₀ | ind₁ = {!  !} where

            x = ε x[ 𝟘 ] ε
            -- y = ε x[ 𝟘 ] ε

            data Y : Set where
                y ₐy yb ₐyb z ₐz zb ₐzb : Y

            ρ : Subst Y *X*
            ρ y = α
            ρ ₐy = Δˡ a ↑ α
            ρ yb = Δʳ b ↑ α
            ρ ₐyb = Δʳ b ↑ (Δˡ a ↑ α)
            ρ z = β
            ρ ₐz = Δˡ a ↑ β
            ρ zb = Δʳ b ↑ β
            ρ ₐzb = Δʳ b ↑ (Δˡ a ↑ β)

            lem₀ : ∀ (γ : Term Y) → Δˡ a ↑ (subst ρ γ) P≈ subst ρ (Δˡ a ↑ γ)
            lem₀ γ = ?
```


