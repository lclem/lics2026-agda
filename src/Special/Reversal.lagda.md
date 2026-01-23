---
title: Reversal of formal series
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
module Assumptions (a b : Σ) where

    data aXb : Set where
        y : aXb
        ay : aXb
        yb : aXb
        ayb : aXb
        z : aXb
        az : aXb
        zb : aXb
        azb : aXb

    data aX : Set where
        y : aX
        ay : aX
        z : aX
        az : aX

    data Xb : Set where
        y : Xb
        yb : Xb
        z : Xb
        zb : Xb

    data εXε : Set where
        y : εXε
        z : εXε

    ε→a : Term εXε → Term aX
    ε→a 0T = 0T
    ε→a (var y) = var y
    ε→a (var z) = var z
    ε→a (c [·] u) = c [·] ε→a u
    ε→a (u [+] v) = ε→a u [+] ε→a v
    ε→a (u [*] v) = ε→a u [*] ε→a v

    ε→b : Term εXε → Term Xb
    ε→b 0T = 0T
    ε→b (var y) = var y
    ε→b (var z) = var z
    ε→b (c [·] u) = c [·] ε→b u
    ε→b (u [+] v) = ε→b u [+] ε→b v
    ε→b (u [*] v) = ε→b u [*] ε→b v

    a→ab : Term aX → Term aXb
    a→ab 0T = 0T
    a→ab (var y) = var y
    a→ab (var ay) = var ay
    a→ab (var z) = var z
    a→ab (var az) = var az
    a→ab (c [·] u) = c [·] a→ab u
    a→ab (u [+] v) = a→ab u [+] a→ab v
    a→ab (u [*] v) = a→ab u [*] a→ab v

    b→ab : Term Xb → Term aXb
    b→ab 0T = 0T
    b→ab (var y) = var y
    b→ab (var yb) = var yb
    b→ab (var z) = var z
    b→ab (var zb) = var zb
    b→ab (c [·] u) = c [·] b→ab u
    b→ab (u [+] v) = b→ab u [+] b→ab v
    b→ab (u [*] v) = b→ab u [*] b→ab v

    Δˡε : Term εXε → Term aX
    Δˡε 0T = 0T
    Δˡε (var y) = var ay
    Δˡε (var z) = var az
    Δˡε (c [·] γ) = c [·] Δˡε γ
    Δˡε (γ [+] δ) = Δˡε γ [+] Δˡε δ
    Δˡε (γ [*] δ) = [ P ]⟨ ε→a γ , Δˡε γ , ε→a δ , Δˡε δ ⟩

    Δʳε : Term εXε → Term Xb
    Δʳε 0T = 0T
    Δʳε (var y) = var yb
    Δʳε (var z) = var zb
    Δʳε (c [·] γ) = c [·] Δʳε γ
    Δʳε (γ [+] δ) = Δʳε γ [+] Δʳε δ
    Δʳε (γ [*] δ) = [ P ]⟨ ε→b γ , Δʳε γ , ε→b δ , Δʳε δ ⟩

    Δˡb : Term Xb → Term aXb
    Δˡb 0T = 0T
    Δˡb (var y) = var ay
    Δˡb (var yb) = var ayb
    Δˡb (var z) = var az
    Δˡb (var zb) = var azb
    Δˡb (c [·] γ) = c [·] Δˡb γ
    Δˡb (γ [+] δ) = Δˡb γ [+] Δˡb δ
    Δˡb (γ [*] δ) = [ P ]⟨ b→ab γ , Δˡb γ , b→ab δ , Δˡb δ ⟩

    Δʳa : Term aX → Term aXb
    Δʳa 0T = 0T
    Δʳa (var y) = var yb
    Δʳa (var ay) = var ayb
    Δʳa (var z) = var zb
    Δʳa (var az) = var azb
    Δʳa (c [·] γ) = c [·] Δʳa γ
    Δʳa (γ [+] δ) = Δʳa γ [+] Δʳa δ
    Δʳa (γ [*] δ) = [ P ]⟨ a→ab γ , Δʳa γ , a→ab δ , Δʳa δ ⟩
```

```
ΔʳΔˡ-var : Set
ΔʳΔˡ-var =
    ∀ a b →
    let open Assumptions a b in
    --------------------------
    Δʳa (Δˡε (var y [*] var z)) P≈ Δˡb (Δʳε (var y [*] var z))
```

```
module _ (special : Special P) where

    open import Special.Automata R Σ P special
```

# Proof of `ΔʳΔˡ → ⟦ΔʳΔˡ⟧` {#sec:proof:1}

```
    ΔʳΔˡ→⟦ΔʳΔˡ⟧ : ΔʳΔˡ → ⟦ΔʳΔˡ⟧
    ΔʳΔˡ→⟦ΔʳΔˡ⟧ ass a b α = semantic-invariance S (ass a b α)
```

# Proof of `ΔʳΔˡ-var → ΔʳΔˡ` {#sec:proof:2}

```
    ΔʳΔˡ-var→ΔʳΔˡ : ΔʳΔˡ-var → ΔʳΔˡ
    ΔʳΔˡ-var→ΔʳΔˡ ass-var a b = go where

        go : ∀ α → Δʳ b ↑ (Δˡ a ↑ α) P≈ Δˡ a ↑ (Δʳ b ↑ α)
        go 0T = P.≈-refl
        go (var (_ x[ _ ] _)) = P.≈-refl
        go (c [·] α) with go α
        ... | ind = P.·-cong R-refl ind
        go (α [+] β) with go α | go β
        ... | ind₀ | ind₁ = ind₀ ⟨ P.+-cong ⟩ ind₁
        go (α [*] β) with go α | go β
        ... | ind₀ | ind₁ = proof where

            open Assumptions a b

            -- ε→ab : Term εXε → Term aXb
            -- ε→ab 0T = 0T
            -- ε→ab (var y) = var y
            -- ε→ab (var z) = var z
            -- ε→ab (c [·] u) = c [·] ε→ab u
            -- ε→ab (u [+] v) = ε→ab u [+] ε→ab v
            -- ε→ab (u [*] v) = ε→ab u [*] ε→ab v

            ρ-ε : Subst εXε *X*
            ρ-ε y = α
            ρ-ε z = β

            ρ-a : Subst aX *X*
            ρ-a y = α
            ρ-a ay = Δˡ a ↑ α
            ρ-a z = β
            ρ-a az = Δˡ a ↑ β

            ρ-b : Subst Xb *X*
            ρ-b y = α
            ρ-b yb = Δʳ b ↑ α
            ρ-b z = β
            ρ-b zb = Δʳ b ↑ β

            ρ-ab : Subst aXb *X*
            ρ-ab y = α
            ρ-ab ay = Δˡ a ↑ α
            ρ-ab yb = Δʳ b ↑ α
            ρ-ab ayb = Δʳ b ↑ (Δˡ a ↑ α)
            ρ-ab z = β
            ρ-ab az = Δˡ a ↑ β
            ρ-ab zb = Δʳ b ↑ β
            ρ-ab azb = Δʳ b ↑ (Δˡ a ↑ β)

            h-a :
                (γ : Term εXε) →
                --------------------------------
                subst ρ-ε γ P≈ subst ρ-a (ε→a γ)
                
            h-a 0T = P.≈-refl
            h-a (var y) = P.≈-refl
            h-a (var z) = P.≈-refl
            h-a (c [·] γ) = R-refl ⟨ P.·-cong ⟩ h-a γ
            h-a (γ [+] δ) = h-a γ ⟨ P.+-cong ⟩ h-a δ
            h-a (γ [*] δ) = h-a γ ⟨ P.*-cong ⟩ h-a δ

            h-b :
                (γ : Term εXε) →
                --------------------------------
                subst ρ-ε γ P≈ subst ρ-b (ε→b γ)
                
            h-b 0T = P.≈-refl
            h-b (var y) = P.≈-refl
            h-b (var z) = P.≈-refl
            h-b (c [·] γ) = R-refl ⟨ P.·-cong ⟩ h-b γ
            h-b (γ [+] δ) = h-b γ ⟨ P.+-cong ⟩ h-b δ
            h-b (γ [*] δ) = h-b γ ⟨ P.*-cong ⟩ h-b δ

            subst-b→ab :
                (γ : Term Xb) →
                --------------------------------
                subst ρ-b γ P≈ subst ρ-ab (b→ab γ)
                
            subst-b→ab 0T = P.≈-refl
            subst-b→ab (var y) = P.≈-refl
            subst-b→ab (var yb) = P.≈-refl
            subst-b→ab (var z) = P.≈-refl
            subst-b→ab (var zb) = P.≈-refl
            subst-b→ab (c [·] γ) = R-refl ⟨ P.·-cong ⟩ subst-b→ab γ
            subst-b→ab (γ [+] δ) = subst-b→ab γ ⟨ P.+-cong ⟩ subst-b→ab δ
            subst-b→ab (γ [*] δ) = subst-b→ab γ ⟨ P.*-cong ⟩ subst-b→ab δ

            subst-a→ab :
                (γ : Term aX) →
                --------------------------------
                subst ρ-a γ P≈ subst ρ-ab (a→ab γ)
                
            subst-a→ab 0T = P.≈-refl
            subst-a→ab (var y) = P.≈-refl
            subst-a→ab (var ay) = P.≈-refl
            subst-a→ab (var z) = P.≈-refl
            subst-a→ab (var az) = P.≈-refl
            subst-a→ab (c [·] γ) = R-refl ⟨ P.·-cong ⟩ subst-a→ab γ
            subst-a→ab (γ [+] δ) = subst-a→ab γ ⟨ P.+-cong ⟩ subst-a→ab δ
            subst-a→ab (γ [*] δ) = subst-a→ab γ ⟨ P.*-cong ⟩ subst-a→ab δ

            Δˡε-lem :
                (γ : Term εXε) →
                ---------------------------------------
                Δˡ a ↑ subst ρ-ε γ P≈ subst ρ-a (Δˡε γ)

            Δˡε-lem 0T = P.≈-refl
            Δˡε-lem (var y) = P.≈-refl
            Δˡε-lem (var z) = P.≈-refl
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
                ∀ (γ : Term εXε) →
                ---------------------------------
                Δʳ b ↑ (subst ρ-ε γ) P≈ subst ρ-b (Δʳε γ)

            Δʳε-lem 0T = P.≈-refl
            Δʳε-lem (var y) = P.≈-refl
            Δʳε-lem (var z) = P.≈-refl
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
                ∀ (γ : Term Xb) →
                ---------------------------------
                Δˡ a ↑ (subst ρ-b γ) P≈ subst ρ-ab (Δˡb γ)

            Δˡb-lem 0T = P.≈-refl
            Δˡb-lem (var y) = P.≈-refl
            Δˡb-lem (var yb) = P.≈-sym ind₀
            Δˡb-lem (var z) = P.≈-refl
            Δˡb-lem (var zb) = P.≈-sym ind₁
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
                ∀ (γ : Term aX) →
                ---------------------------------
                Δʳ b ↑ (subst ρ-a γ) P≈ subst ρ-ab (Δʳa γ)

            Δʳa-lem 0T = P.≈-refl
            Δʳa-lem (var y) = P.≈-refl
            Δʳa-lem (var ay) = P.≈-refl
            Δʳa-lem (var z) = P.≈-refl
            Δʳa-lem (var az) = P.≈-refl
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
                    Δʳ b ↑ (Δˡ a ↑ (subst ρ-ε (var y [*] var z)))
                        ≈⟨ invariance (Δʳ b) (Δˡε-lem (var y [*] var z)) ⟩
                    Δʳ b ↑ (subst ρ-a (Δˡε (var y [*] var z)))
                        ≈⟨ Δʳa-lem (Δˡε (var y [*] var z)) ⟩
                    subst ρ-ab (Δʳa (Δˡε (var y [*] var z)))
                        ≈⟨ subst-inv ρ-ab (ass-var a b) ⟩
                    subst ρ-ab (Δˡb (Δʳε (var y [*] var z)))
                        ≈⟨ Δˡb-lem (Δʳε (var y [*] var z)) ⟨
                    Δˡ a ↑ (subst ρ-b (Δʳε (var y [*] var z)))
                        ≈⟨ invariance (Δˡ a) (Δʳε-lem (var y [*] var z)) ⟨
                    Δˡ a ↑ (Δʳ b ↑ (subst ρ-ε (var y [*] var z)))
                        ≈⟨⟩
                    Δˡ a ↑ (Δʳ b ↑ (α [*] β))
                ∎ where open EqP

```


