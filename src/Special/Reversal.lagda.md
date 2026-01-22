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

            f = 𝟘
            g = 𝟘
            -- x = ε x[ f ] ε
            -- y = ε x[ g ] ε

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

            a→ab : ∀ {x} → aX x → aXb x
            a→ab y = y
            a→ab ay = ay
            a→ab z = z
            a→ab az = az

            b→ab : ∀ {x} → Xb x → aXb x
            b→ab y = y
            b→ab yb = yb
            b→ab z = z
            b→ab zb = zb

            ρ : Subst (∃[ x ] aXb x) *X*
            ρ (_ ,, y) = α
            ρ (_ ,, ay) = Δˡ a ↑ α
            ρ (_ ,, yb) = Δʳ b ↑ α
            ρ (_ ,, ayb) = Δʳ b ↑ (Δˡ a ↑ α)
            ρ (_ ,, z) = β
            ρ (_ ,, az) = Δˡ a ↑ β
            ρ (_ ,, zb) = Δʳ b ↑ β
            ρ (_ ,, azb) = Δʳ b ↑ (Δˡ a ↑ β)

            pr-b : Term (∃[ x ] Xb x) → Term *X*
            pr-b 0T = 0T
            pr-b (var (x ,, _)) = var x
            pr-b (c [·] u) = c [·] pr-b u
            pr-b (u [+] v) = pr-b u [+] pr-b v
            pr-b (u [*] v) = pr-b u [*] pr-b v

            pr-a : Term (∃[ x ] aX x) → Term *X*
            pr-a 0T = 0T
            pr-a (var (x ,, _)) = var x
            pr-a (c [·] u) = c [·] pr-a u
            pr-a (u [+] v) = pr-a u [+] pr-a v
            pr-a (u [*] v) = pr-a u [*] pr-a v

            pr-ab : Term (∃[ x ] aXb x) → Term *X*
            pr-ab 0T = 0T
            pr-ab (var (x ,, _)) = var x
            pr-ab (c [·] u) = c [·] pr-ab u
            pr-ab (u [+] v) = pr-ab u [+] pr-ab v
            pr-ab (u [*] v) = pr-ab u [*] pr-ab v

            data Term-Prop (Var-Prop : *X* → Set) : Term *X* → Set where
                0T : Term-Prop Var-Prop 0T
                var : ∀ {x} (prop : Var-Prop x) → Term-Prop Var-Prop (var x)
                _[·]_ : ∀ {u} c → Term-Prop Var-Prop u → Term-Prop Var-Prop (c [·] u)
                _[+]_ : ∀ {u v} → Term-Prop Var-Prop u → Term-Prop Var-Prop v → Term-Prop Var-Prop (u [+] v)
                _[*]_ : ∀ {u v} → Term-Prop Var-Prop u → Term-Prop Var-Prop v → Term-Prop Var-Prop (u [*] v)

            Δˡa-lem :
                ∀ (γ : Term (∃[ x ] Xb x)) →
                -----------------------------
                Term-Prop aXb (Δˡ a ↑ pr-b γ)

            Δˡa-lem 0T = 0T
            Δˡa-lem (var (_ ,, y)) = var ay
            Δˡa-lem (var (_ ,, yb)) = var ayb
            Δˡa-lem (var (_ ,, z)) = var az
            Δˡa-lem (var (_ ,, zb)) = var azb
            Δˡa-lem (c [·] γ) = c [·] Δˡa-lem γ
            Δˡa-lem (γ [+] δ) = Δˡa-lem γ [+] Δˡa-lem δ
            Δˡa-lem (γ [*] δ) = {! Δˡa-lem γ [*] Δˡa-lem δ !}

            h0 : Term (∃[ x ] Xb x) → Term (∃[ x ] aXb x)
            h0 0T = 0T
            h0 (var (x ,, p)) = var (x ,, b→ab p)
            h0 (c [·] u) = c [·] h0 u
            h0 (u [+] v) = h0 u [+] h0 v
            h0 (u [*] v) = h0 u [*] h0 v

            h1 : ∀ {γ} → Term-Prop aXb γ → Term (∃[ x ] aXb x)
            h1 0T = 0T
            h1 (var y) = var (_ ,, y)
            h1 (var ay) = var (_ ,, ay)
            h1 (var yb) = var (_ ,, yb)
            h1 (var ayb) = var (_ ,, ayb)
            h1 (var z) = var (_ ,, z)
            h1 (var az) = var (_ ,, az)
            h1 (var zb) = var (_ ,, zb)
            h1 (var azb) = var (_ ,, azb)
            h1 (c [·] u) = c [·] h1 u
            h1 (u [+] v) = h1 u [+] h1 v
            h1 (u [*] v) = h1 u [*] h1 v

            Δˡ-ρ :
                ∀ (γ : Term (∃[ x ] Xb x)) →
                ----------------------------------------------------
                Δˡ a ↑ (subst ρ (h0 γ)) P≈ subst ρ (h1 (Δˡa-lem γ))

            Δˡ-ρ 0T = P.≈-refl
            Δˡ-ρ (var (x ,, y)) = P.≈-refl
            Δˡ-ρ (var (x ,, yb)) = 
                begin
                    Δˡ a ↑ subst ρ (var (_ ,, yb))
                        ≈⟨⟩
                    Δˡ a ↑ (Δʳ b ↑ α)
                        ≈⟨ ind₀ ⟨
                    Δʳ b ↑ (Δˡ a ↑ α)
                        ≈⟨⟩
                    subst ρ (var (_ ,, ayb))
                ∎ where open EqP
            Δˡ-ρ (var (x ,, z)) = P.≈-refl
            Δˡ-ρ (var (x ,, zb)) =
                begin
                    Δˡ a ↑ subst ρ (var (_ ,, zb))
                        ≈⟨⟩
                    Δˡ a ↑ (Δʳ b ↑ β)
                        ≈⟨ ind₁ ⟨
                    Δʳ b ↑ (Δˡ a ↑ β)
                        ≈⟨⟩
                    subst ρ (var (_ ,, azb))
                ∎ where open EqP
            Δˡ-ρ (c [·] γ) = R-refl ⟨ P.·-cong ⟩ Δˡ-ρ γ
            Δˡ-ρ (γ [+] δ) = Δˡ-ρ γ ⟨ P.+-cong ⟩ Δˡ-ρ δ
            Δˡ-ρ (γ [*] δ) = {!   !} -- Δˡ-ρ γ ⟨ P.*-cong ⟩ Δˡ-ρ δ
```


