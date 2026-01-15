---
title: "Finitely generated classes of series 🚧"
---

```
{-# OPTIONS --guardedness --sized-types #-}
-- --allow-unsolved-metas

open import Preliminaries.Base renaming (_,,_ to _,_)
open import General.ProductRules

module General.FinitelyGenerated-AntiDerivatives
    (R : CommutativeRing)
    (n : ℕ) -- size of the alphabet
    (productRule : ProductRule R)
    where

Σ = Fin n

open import Size

open import Preliminaries.Vector
open import Preliminaries.Algebra R
open import Preliminaries.PolyExpr R using (con)

open import General.Terms R
    renaming (_+_ to _[+]_; _*_ to _[*]_; _·_ to _[·]_) -- ⟦_⟧_ to E⟦_⟧_; ⟦_⟧ᵥ_ to E⟦_⟧ᵥ_)

open import General.Series R Σ
open import General.Products R Σ
open Product productRule
open ProductRule productRule

open import General.FinitelyGenerated R Σ productRule

private variable
    m : ℕ
    f g : A ⟪ Σ ⟫
    fs gs : Vec (A ⟪ Σ ⟫) m
```

```
∷-∈ : g ∈[ fs ] → g ∈[ f ∷ fs ]
∷-∈ 𝟘∈ = 𝟘∈
∷-∈ (gen∈ g∈fs) = gen∈ (there g∈fs)
∷-∈ (c ·∈ g∈[fs]) = c ·∈ ∷-∈ g∈[fs]
∷-∈ (f∈[fs] +∈ g∈[fs]) = ∷-∈ f∈[fs] +∈ ∷-∈ g∈[fs]
∷-∈ (f∈[fs] *∈ g∈[fs]) = ∷-∈ f∈[fs] *∈ ∷-∈ g∈[fs]
∷-∈ (f≈g ≈∈ g∈[fs]) = f≈g ≈∈ ∷-∈ g∈[fs]

concat-∈ : ∀ {n} {F : Vec (Vec (A ⟪ Σ ⟫) m) n} → f ∈[ fs ] → fs ∈ F → f ∈[ concat F ]
concat-∈ f∈[fs] (here px) rewrite px = ++-∈ˡ f∈[fs]
concat-∈ {F = F} f∈[fs] (there fs∈F) with concat-∈ f∈[fs] fs∈F
... | f∈[F] = ++-∈ʳ f∈[F]

*-Fin-δ⁻¹ :
    (∀ a → *-Fin (δ f a) m) →
    --------------------------
    *-Fin f (1 +ℕ n +ℕ n *ℕ m)

*-Fin-δ⁻¹ {f} {m} ass =
    *-Fin[ f ∷ δf ++ concat F , gen∈ (here refl) , lem ]
    where

    δf : Vec (A ⟪ Σ ⟫) n
    δf = tabulate $ δ f

    δfa∈δf : ∀ a → δ f a ∈ δf
    δfa∈δf = ∈-tabulate⁺ (δ f)

    gen′ : Σ → Vec (A ⟪ Σ ⟫) m
    gen′ a = gen $ ass a

    F : Vec (Vec (A ⟪ Σ ⟫) m) n
    F = tabulate gen′

    lem′ : ∀ {g a b} → g ∈[ gen′ b ] → δ g a ∈[ concat F ]
    lem′ {g} {a} {b} g∈[gen] = concat-∈ δga∈[gen] (∈-tabulate⁺ gen′ b)
        where

        δga∈[gen] : δ g a ∈[ gen′ b ]
        δga∈[gen] = δ-closed (ass b) a g∈[gen]

    lem :
        ∀ a {g} →
        g ∈ f ∷ δf ++ concat F →
        -----------------------------
        δ g a ∈[ f ∷ δf ++ concat F ]

    lem a {g} (here g≡f) rewrite g≡f = gen∈ $ there $ ∈-++⁺ˡ (δfa∈δf a)

    lem a {g} (there g∈δf++F)
        with ∈ᵥ-++ {a = g} {as = δf} {bs = concat F} g∈δf++F
    ... | inj₁ g∈δf
        with ∈-tabulate⁻ g∈δf
    lem a {g} (there g∈δf++F) | inj₁ g∈δf | b , g≡δfb
        = ∷-∈ $ ++-∈ʳ $ lem′ g∈[gen]
        where

        g∈[gen] : g ∈[ gen′ b ]
        g∈[gen] rewrite g≡δfb = memb (ass b)

    lem a {g} (there g∈δf++F) | inj₂ g∈concatF
        with concat-∈⁻ {ass = F} g∈concatF
    ... | gs , gs∈F , g∈gs
        with ∈-tabulate⁻ gs∈F
    ... | b , gs≡genb
        = ∷-∈ $ ++-∈ʳ $ lem′ g∈[gen]
        where

        g∈[gen] : g ∈[ gen′ b ]
        g∈[gen] rewrite gs≡genb = gen∈ g∈gs
```