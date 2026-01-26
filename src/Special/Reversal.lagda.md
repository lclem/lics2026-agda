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
open import General.Terms R renaming (_+_ to _[+]_; _*_ to _[*]_; _-_ to _[-]_; _·_ to _[·]_) hiding (x; y; z; t)
open import General.Products R Σ
open import General.Automata R Σ P
open import General.Reversal R Σ
open import General.ReversalEnd R Σ P

open Product P
-- open Reversal P

open import Special.Polynomials R as P renaming (_≈_ to _P≈_) hiding (Term-Prop; transfer)
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

    -- enriched forms
    -- data aXb : *X* → Set where
    --     y : aXb (ε x[ f ] ε)
    --     ay : aXb ((a ∷ ε) x[ f ] ε)
    --     yb : aXb (ε x[ f ] (b ∷ ε))
    --     ayb : aXb ((a ∷ ε) x[ f ] (b ∷ ε))
    --     z : aXb (ε x[ g ] ε)
    --     az : aXb ((a ∷ ε) x[ g ] ε)
    --     zb : aXb (ε x[ g ] (b ∷ ε))
    --     azb : aXb ((a ∷ ε) x[ g ] (b ∷ ε))

    -- data aX : *X* → Set where
    --     y : aX (ε x[ f ] ε)
    --     ay : aX ((a ∷ ε) x[ f ] ε)
    --     z : aX (ε x[ g ] ε)
    --     az : aX ((a ∷ ε) x[ g ] ε)

    -- data Xb : *X* → Set where
    --     y : Xb (ε x[ f ] ε)
    --     yb : Xb (ε x[ f ] (b ∷ ε))
    --     z : Xb (ε x[ g ] ε)
    --     zb : Xb (ε x[ g ] (b ∷ ε))

    -- data εXε : *X* → Set where
    --     y : εXε (ε x[ f ] ε)
    --     z : εXε (ε x[ g ] ε)

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

-- what I assume now
ΔʳΔˡ-var : Set
ΔʳΔˡ-var =
    ∀ a b →
    let open Assumptions a b in
    --------------------------
    Δʳa (Δˡε (var y [*] var z)) P≈ Δˡb (Δʳε (var y [*] var z))

-- what I would like to assume instead
ΔʳΔˡ-var′ : Set
ΔʳΔˡ-var′ =
    ∀ a b f g →
    -----------------------------------------------------------
    Δʳ b ↑ (Δˡ a ↑ (var (ε x[ f ] ε) [*] var (ε x[ g ] ε))) P≈
    Δˡ a ↑ (Δʳ b ↑ (var (ε x[ f ] ε) [*] var (ε x[ g ] ε)))

-- open Inductive
open import Relation.Nullary.Negation using (¬_)

module Test a b f g (special : Special P)
    (≠-ε : ¬ (ε x[ f ] ε ≡ ε x[ g ] ε))
    (≠-a : ¬ ((a ∷ ε) x[ f ] ε ≡ (a ∷ ε) x[ g ] ε))
    (≠-b : ¬ (ε x[ f ] (b ∷ ε) ≡ ε x[ g ] (b ∷ ε)))
    (≠-ab : ¬ ((a ∷ ε) x[ f ] (b ∷ ε) ≡ (a ∷ ε) x[ g ] (b ∷ ε)))
    where

    open import Special.Automata R Σ P special
    open Assumptions a b

    ρε : Term εXε → Term *X*
    ρε 0T = 0T
    ρε (var y) = var (ε x[ f ] ε)
    ρε (var z) = var (ε x[ g ] ε)
    ρε (c [·] γ) = c [·] ρε γ
    ρε (γ [+] δ) = ρε γ [+] ρε δ
    ρε (γ [*] δ) = ρε γ [*] ρε δ

    ρa : Term aX → Term *X*
    ρa 0T = 0T
    ρa (var y) = var (ε x[ f ] ε)
    ρa (var ay) = var ((a ∷ ε) x[ f ] ε)
    ρa (var z) = var (ε x[ g ] ε)
    ρa (var az) = var ((a ∷ ε) x[ g ] ε)
    ρa (c [·] γ) = c [·] ρa γ
    ρa (γ [+] δ) = ρa γ [+] ρa δ
    ρa (γ [*] δ) = ρa γ [*] ρa δ

    ρb : Term Xb → Term *X*
    ρb 0T = 0T
    ρb (var y) = var (ε x[ f ] ε)
    ρb (var yb) = var (ε x[ f ] (b ∷ ε))
    ρb (var z) = var (ε x[ g ] ε)
    ρb (var zb) = var (ε x[ g ] (b ∷ ε))
    ρb (c [·] γ) = c [·] ρb γ
    ρb (γ [+] δ) = ρb γ [+] ρb δ
    ρb (γ [*] δ) = ρb γ [*] ρb δ

    ρab : Term aXb → Term *X*
    ρab 0T = 0T
    ρab (var y) = var (ε x[ f ] ε)
    ρab (var ay) = var ((a ∷ ε) x[ f ] ε)
    ρab (var yb) = var (ε x[ f ] (b ∷ ε))
    ρab (var ayb) = var ((a ∷ ε) x[ f ] (b ∷ ε))
    ρab (var z) = var (ε x[ g ] ε)
    ρab (var az) = var ((a ∷ ε) x[ g ] ε)
    ρab (var zb) = var (ε x[ g ] (b ∷ ε))
    ρab (var azb) = var ((a ∷ ε) x[ g ] (b ∷ ε))
    ρab (c [·] γ) = c [·] ρab γ
    ρab (γ [+] δ) = ρab γ [+] ρab δ
    ρab (γ [*] δ) = ρab γ [*] ρab δ

    data aXb′ : *X* → Set where
        y : aXb′ (ε x[ f ] ε)
        ay : aXb′ ((a ∷ ε) x[ f ] ε)
        yb : aXb′ (ε x[ f ] (b ∷ ε))
        ayb : aXb′ ((a ∷ ε) x[ f ] (b ∷ ε))
        z : aXb′ (ε x[ g ] ε)
        az : aXb′ ((a ∷ ε) x[ g ] ε)
        zb : aXb′ (ε x[ g ] (b ∷ ε))
        azb : aXb′ ((a ∷ ε) x[ g ] (b ∷ ε))

    aXb′-inj : ∀ {x} (p q : aXb′ x) → p ≡ q
    aXb′-inj y y = refl
    aXb′-inj y z = ⊥-elim (≠-ε refl)
    aXb′-inj ay ay = refl
    aXb′-inj ay az = ⊥-elim (≠-a refl)
    aXb′-inj yb yb = refl
    aXb′-inj yb zb = ⊥-elim (≠-b refl)
    aXb′-inj ayb ayb = refl
    aXb′-inj ayb azb = ⊥-elim (≠-ab refl)
    aXb′-inj z y = ⊥-elim (≠-ε refl)
    aXb′-inj z z = refl
    aXb′-inj az ay = ⊥-elim (≠-a refl)
    aXb′-inj az az = refl
    aXb′-inj zb yb = ⊥-elim (≠-b refl)
    aXb′-inj zb zb = refl
    aXb′-inj azb ayb = ⊥-elim (≠-ab refl)
    aXb′-inj azb azb = refl

    -- lift a property of variable to all terms
    data Term-Prop (Var-Prop : *X* → Set) : Term *X* → Set where
        0T : Term-Prop Var-Prop 0T
        var : ∀ {x} → Var-Prop x → Term-Prop Var-Prop (var x)
        _[·]_ : ∀ {u} c → Term-Prop Var-Prop u → Term-Prop Var-Prop (c [·] u)
        _[+]_ : ∀ {u v} → Term-Prop Var-Prop u → Term-Prop Var-Prop v → Term-Prop Var-Prop (u [+] v)
        _[*]_ : ∀ {u v} → Term-Prop Var-Prop u → Term-Prop Var-Prop v → Term-Prop Var-Prop (u [*] v)

    Term-Prop-inj :
        ∀ {α} (p q : Term-Prop aXb′ α) →
        --------------------------------
        p ≡ q

    Term-Prop-inj 0T 0T = refl
    Term-Prop-inj (var px) (var qx) = cong var (aXb′-inj px qx)
    Term-Prop-inj (c [·] p) (.c [·] q)
        rewrite Term-Prop-inj p q = refl
    Term-Prop-inj (p [+] p₁) (q [+] q₁)
        rewrite Term-Prop-inj p q | Term-Prop-inj p₁ q₁ = refl
    Term-Prop-inj (p [*] p₁) (q [*] q₁)
        rewrite Term-Prop-inj p q | Term-Prop-inj p₁ q₁ = refl

    Term-Prop-≈ :
        ∀ {α β} →
        Term-Prop aXb′ α →
        α P≈ β →
        ------------------
        Term-Prop aXb′ β

    Term-Prop-≈′ :
        ∀ {α β} →
        Term-Prop aXb′ β →
        α P≈ β →
        ------------------
        Term-Prop aXb′ α

    Term-Prop-≈ pα ≈-refl = pα
    Term-Prop-≈ pα (≈-sym α≈β) = Term-Prop-≈′ pα α≈β
    Term-Prop-≈ pα (≈-trans α≈β α≈β₁) = Term-Prop-≈ (Term-Prop-≈ pα α≈β) α≈β₁
    Term-Prop-≈ (_ [·] pα) (·-cong x α≈β) = _ [·] Term-Prop-≈ pα α≈β
    Term-Prop-≈ (1R [·] pα) (·-one _) = pα
    Term-Prop-≈ (.c [·] (pα [+] pα₁)) (·-+-distrib c p q) = (c [·] pα ) [+] (c [·] pα₁)
    Term-Prop-≈ (_ [·] pα) (+-·-distrib p c d) = (c [·] pα ) [+] (d [·] pα)
    Term-Prop-≈ ((.c [·] pα) [*] pα₁) (·-*-distrib c p q) = c [·] (pα [*] pα₁)
    Term-Prop-≈ (_ [·] pα) (*-·-distrib c d p) = c [·] (d [·] pα)
    Term-Prop-≈ (pα [+] pα₁) (+-cong α≈β α≈β₁) = Term-Prop-≈ pα α≈β [+] Term-Prop-≈ pα₁ α≈β₁
    Term-Prop-≈ (pα [+] pα₁) (+-zeroʳ _) = pα
    Term-Prop-≈ ((pα [+] pα₂) [+] pα₁) (+-assoc _ _ _) = pα [+] (pα₂ [+] pα₁)
    Term-Prop-≈ (pα [+] pα₁) (+-comm _ _) = pα₁ [+] pα
    Term-Prop-≈ pα (+-invʳ p) = 0T
    Term-Prop-≈ (pα [*] pα₁) (*-cong α≈β α≈β₁) = Term-Prop-≈ pα α≈β [*] Term-Prop-≈ pα₁ α≈β₁
    Term-Prop-≈ ((pα [*] pα₂) [*] pα₁) (*-assoc _ _ _) = pα [*] (pα₂ [*] pα₁)
    Term-Prop-≈ (pα [*] pα₁) (*-comm _ _) = pα₁ [*] pα
    Term-Prop-≈ ((pα [+] pα₂) [*] pα₁) (*-distribʳ _ _ _) = (pα [*] pα₁) [+] (pα₂ [*] pα₁)

    Term-Prop-≈′ pβ ≈-refl = pβ
    Term-Prop-≈′ pβ (≈-sym α≈β) = Term-Prop-≈ pβ α≈β
    Term-Prop-≈′ pβ (≈-trans α≈β α≈β₁) = Term-Prop-≈′ (Term-Prop-≈′ pβ α≈β₁) α≈β
    Term-Prop-≈′ (_ [·] pβ) (·-cong _ α≈β) = _ [·] Term-Prop-≈′ pβ α≈β
    Term-Prop-≈′ pβ (·-one _) = 1R [·] pβ
    Term-Prop-≈′ ((_ [·] pβ) [+] (_ [·] pβ₁)) (·-+-distrib _ _ _) = _ [·] (pβ [+] pβ₁)
    Term-Prop-≈′ ((_ [·] pβ) [+] _) (+-·-distrib _ _ _) = _ [·] pβ
    Term-Prop-≈′ (_ [·] (pβ [*] pβ₁)) (·-*-distrib _ _ _) = (_ [·] pβ) [*] pβ₁
    Term-Prop-≈′ (_ [·] (_ [·] pβ)) (*-·-distrib _ _ _) = _ [·] pβ
    Term-Prop-≈′ (pβ [+] pβ₁) (+-cong α≈β α≈β₁) = Term-Prop-≈′ pβ α≈β [+] Term-Prop-≈′ pβ₁ α≈β₁
    Term-Prop-≈′ pβ (+-zeroʳ _) = pβ [+] 0T
    Term-Prop-≈′ (pβ [+] (pβ₁ [+] pβ₂)) (+-assoc _ _ _) = (pβ [+] pβ₁) [+] pβ₂
    Term-Prop-≈′ (pβ [+] pβ₁) (+-comm _ _) = pβ₁ [+] pβ
    Term-Prop-≈′ 0T (+-invʳ p) = {!   !} -- !!!
    Term-Prop-≈′ (pβ [*] pβ₁) (*-cong α≈β α≈β₁) = Term-Prop-≈′ pβ α≈β [*] Term-Prop-≈′ pβ₁ α≈β₁
    Term-Prop-≈′ (pβ [*] (pβ₁ [*] pβ₂)) (*-assoc _ _ _) = (pβ [*] pβ₁) [*] pβ₂
    Term-Prop-≈′ (pβ [*] pβ₁) (*-comm _ _) = pβ₁ [*] pβ
    Term-Prop-≈′ ((pβ [*] pβ₁) [+] (pβ₂ [*] _)) (*-distribʳ _ _ _) = (pβ [+] pβ₂) [*] pβ₁

    ρab-inv : ∀ {α : Term *X*} → Term-Prop aXb′ α → Term aXb
    ρab-inv 0T = 0T
    ρab-inv (var y) = var y
    ρab-inv (var ay) = var ay
    ρab-inv (var yb) = var yb
    ρab-inv (var ayb) = var ayb
    ρab-inv (var z) = var z
    ρab-inv (var az) = var az
    ρab-inv (var zb) = var zb
    ρab-inv (var azb) = var azb
    ρab-inv (c [·] α) = c [·] ρab-inv α
    ρab-inv (α [+] β) = ρab-inv α [+] ρab-inv β
    ρab-inv (α [*] β) = ρab-inv α [*] ρab-inv β

    -- not used
    -- ρab-inv-lemma :
    --     ∀ {α : Term *X*} →
    --     (pα : Term-Prop aXb′ α) →
    --     -------------------------
    --     ρab (ρab-inv pα) ≡ α
    -- ρab-inv-lemma pα = {!   !}

    ρab-wit : ∀ (α : Term aXb) → Term-Prop aXb′ (ρab α)
    ρab-wit 0T = 0T
    ρab-wit (var y) = var y
    ρab-wit (var ay) = var ay
    ρab-wit (var yb) = var yb
    ρab-wit (var ayb) = var ayb
    ρab-wit (var z) = var z
    ρab-wit (var az) = var az
    ρab-wit (var zb) = var zb
    ρab-wit (var azb) = var azb
    ρab-wit (c [·] α) = c [·] ρab-wit α
    ρab-wit (α [+] β) = ρab-wit α [+] ρab-wit β
    ρab-wit (α [*] β) = ρab-wit α [*] ρab-wit β

    ρab-inv-lemma′ :
        ∀ (α : Term aXb) →
        ------------------------
        ρab-inv (ρab-wit α) ≡ α

    ρab-inv-lemma′ 0T = refl
    ρab-inv-lemma′ (var y) = refl
    ρab-inv-lemma′ (var ay) = refl
    ρab-inv-lemma′ (var yb) = refl
    ρab-inv-lemma′ (var ayb) = refl
    ρab-inv-lemma′ (var z) = refl
    ρab-inv-lemma′ (var az) = refl
    ρab-inv-lemma′ (var zb) = refl
    ρab-inv-lemma′ (var azb) = refl
    ρab-inv-lemma′ (c [·] α)
        rewrite ρab-inv-lemma′ α = refl
    ρab-inv-lemma′ (α [+] β)
        rewrite ρab-inv-lemma′ α | ρab-inv-lemma′ β = refl
    ρab-inv-lemma′ (α [*] β)
        rewrite ρab-inv-lemma′ α | ρab-inv-lemma′ β = refl

    -- if α, β are two terms using only variables satisfying aXb′,
    -- and there is an equivalence proof between them in *X*,
    -- then there is another equivalence proof in aXb

    transfer′ :
        ∀ {α β : Term *X*} →
        (pα : Term-Prop aXb′ α) →
        (pβ : Term-Prop aXb′ β) →
        α P≈ β →
        -------------------------
        ρab-inv pα P≈ ρab-inv pβ

    transfer′ pα pβ ≈-refl
        rewrite Term-Prop-inj pα pβ
        = P.≈-refl

    transfer′ pα pβ (≈-sym β≈α)
        = P.≈-sym (transfer′ pβ pα β≈α)

    transfer′ pα pβ (≈-trans {q = γ} α≈γ γ≈β)
        = P.≈-trans (transfer′ pα (Term-Prop-≈ pα α≈γ) α≈γ) (transfer′ _ pβ γ≈β)

    transfer′ (_ [·] pα) (_ [·] pβ) (·-cong x α≈β) = P.·-cong x (transfer′ pα pβ α≈β)

    transfer′ (_ [·] pα) pβ (·-one _)
        rewrite Term-Prop-inj pα pβ
        = P.·-one _

    transfer′ (_ [·] (pα [+] pα₁)) ((_ [·] pβ) [+] (_ [·] pβ₁)) (·-+-distrib _ _ _) 
        rewrite Term-Prop-inj pα pβ | Term-Prop-inj pα₁ pβ₁
        = P.·-+-distrib _ _ _
    
    transfer′ (_ [·] pα) ((_ [·] pβ) [+] (_ [·] pβ₁)) (+-·-distrib _ _ _) 
        rewrite Term-Prop-inj pα pβ | Term-Prop-inj pβ pβ₁
        = P.+-·-distrib _ _ _
    
    transfer′ ((_ [·] pα) [*] pα₁) (_ [·] (pβ [*] pβ₁)) (·-*-distrib _ _ _)
        rewrite Term-Prop-inj pα pβ | Term-Prop-inj pα₁ pβ₁
        = P.·-*-distrib _ _ _

    transfer′ (_ [·] pα) (_ [·] (_ [·] pβ)) (*-·-distrib _ _ _)
        rewrite Term-Prop-inj pα pβ
        = P.*-·-distrib _ _ _

    transfer′ (pα [+] pα₁) (pβ [+] pβ₁) (+-cong α≈β α≈β₁)
        = P.+-cong (transfer′ pα pβ α≈β) (transfer′ pα₁ pβ₁ α≈β₁)

    transfer′ (pα [+] 0T) pβ (+-zeroʳ _)
        rewrite Term-Prop-inj pα pβ = +-zeroʳ _

    transfer′ ((pα [+] pα₂) [+] pα₁) (pβ [+] (pβ₁ [+] pβ₂)) (+-assoc _ _ _)
        rewrite Term-Prop-inj pα pβ | Term-Prop-inj pα₂ pβ₁ | Term-Prop-inj pα₁ pβ₂
        = P.+-assoc _ _ _

    transfer′ (pα [+] pα₁) (pβ [+] pβ₁) (+-comm _ _)
        rewrite Term-Prop-inj pα pβ₁ | Term-Prop-inj pα₁ pβ
        = P.+-comm _ _

    transfer′ (pα [+] (_ [·] pα₁)) 0T (+-invʳ _)
        rewrite Term-Prop-inj pα pα₁
        = +-invʳ _

    transfer′ (pα [*] pα₁) (pβ [*] pβ₁) (*-cong α≈β α≈β₁)
        = P.*-cong (transfer′ pα pβ α≈β) (transfer′ pα₁ pβ₁ α≈β₁)

    transfer′ ((pα [*] pα₂) [*] pα₁) (pβ [*] (pβ₁ [*] pβ₂)) (*-assoc _ _ _)
        rewrite Term-Prop-inj pα pβ | Term-Prop-inj pα₂ pβ₁ | Term-Prop-inj pα₁ pβ₂
        = P.*-assoc _ _ _

    transfer′ (pα [*] pα₁) (pβ [*] pβ₁) (*-comm _ _)
        rewrite Term-Prop-inj pα pβ₁ | Term-Prop-inj pα₁ pβ
        = P.*-comm _ _

    transfer′ ((pα [+] pα₂) [*] pα₁) ((pβ [*] pβ₁) [+] (pβ₂ [*] pβ₃)) (*-distribʳ _ _ _) 
        rewrite 
                Term-Prop-inj pα pβ |
                Term-Prop-inj pα₁ pβ₃ |
                Term-Prop-inj pα₂ pβ₂ |
                Term-Prop-inj pβ₁ pβ₃
        = P.*-distribʳ _ _ _

    -- if there is an equality proof between two terms over aXb,
    -- then there is one where every intermediate term is also over aXb

    transfer :
        ∀ (γ δ : Term aXb) →
        ρab γ P≈ ρab δ →
        --------------------
        γ P≈ δ

    transfer γ δ eq = 
        begin
            γ
                ≡⟨ ρab-inv-lemma′ γ ⟨
            ρab-inv (ρab-wit γ)
                ≈⟨ transfer′ (ρab-wit γ) (ρab-wit δ) eq ⟩
            ρab-inv (ρab-wit δ)
                ≡⟨ ρab-inv-lemma′ δ ⟩
            δ
        ∎ where open EqP
        
    ρΔˡε-lem : 
        (γ : Term εXε) →
        ---------------------------
        ρa (Δˡε γ) P≈ Δˡ a ↑ (ρε γ)

    ρΔˡε-lem 0T = P.≈-refl
    ρΔˡε-lem (var y) = P.≈-refl
    ρΔˡε-lem (var z) = P.≈-refl
    ρΔˡε-lem (c [·] γ) = P.·-cong R-refl (ρΔˡε-lem γ)
    ρΔˡε-lem (γ [+] δ) = ρΔˡε-lem γ ⟨ P.+-cong ⟩ ρΔˡε-lem δ
    ρΔˡε-lem (γ [*] δ) =
        begin
            ρa (Δˡε (γ [*] δ))
                ≈⟨⟩
            ρa ([ P ]⟨ ε→a γ , Δˡε γ , ε→a δ , Δˡε δ ⟩)
                ≈⟨ {!   !} ⟩
            [ P ]⟨ ρa (ε→a γ) , ρa (Δˡε γ) , ρa (ε→a δ) , ρa (Δˡε δ) ⟩
                ≈⟨ {!   !} ⟩
            [ P ]⟨ ρε γ , Δˡ a ↑ (ρε γ) , ρε δ , Δˡ a ↑ (ρε δ) ⟩
                ≈⟨ {!   !} ⟩
            [ P ]⟨ ρε γ , Δˡ a ↑ (ρε γ) , ρε δ , Δˡ a ↑ (ρε δ) ⟩
                ≈⟨⟩
            Δˡ a ↑ (ρε γ [*] ρε δ)
        ∎ where open EqP

    ρΔʳε-lem : 
        (γ : Term εXε) →
        ---------------------------
        ρb (Δʳε γ) P≈ Δʳ b ↑ (ρε γ)

    ρΔʳε-lem 0T = P.≈-refl
    ρΔʳε-lem (var y) = P.≈-refl
    ρΔʳε-lem (var z) = P.≈-refl
    ρΔʳε-lem (c [·] γ) = {!   !}
    ρΔʳε-lem (γ [+] δ) = {!   !}
    ρΔʳε-lem (γ [*] δ) = {!   !}

    ρΔʳa-lem : 
        ∀ (γ : Term aX) →
        ---------------------------
        ρab (Δʳa γ) P≈ Δʳ b ↑ (ρa γ)

    ρΔʳa-lem 0T = P.≈-refl
    ρΔʳa-lem (var y) = P.≈-refl
    ρΔʳa-lem (var ay) = P.≈-refl
    ρΔʳa-lem (var z) = P.≈-refl
    ρΔʳa-lem (var az) = P.≈-refl
    ρΔʳa-lem (c [·] γ) = {!   !}
    ρΔʳa-lem (γ [+] δ) = {!   !}
    ρΔʳa-lem (γ [*] δ) = {!   !}

    ρΔˡb-lem : 
        ∀ (γ : Term Xb) →
        ----------------------------
        ρab (Δˡb γ) P≈ Δˡ a ↑ (ρb γ)

    ρΔˡb-lem 0T = P.≈-refl
    ρΔˡb-lem (var y) = P.≈-refl
    ρΔˡb-lem (var yb) = P.≈-refl
    ρΔˡb-lem (var z) = P.≈-refl
    ρΔˡb-lem (var zb) = P.≈-refl
    ρΔˡb-lem (c [·] γ) = {!   !}
    ρΔˡb-lem (γ [+] δ) = {!   !}
    ρΔˡb-lem (γ [*] δ) = {!   !}

    have :
        ∀ (γ : Term εXε) →
        Δʳ b ↑ (Δˡ a ↑ (ρε γ)) P≈ Δˡ a ↑ (Δʳ b ↑ (ρε γ)) →
        --------------------------------------------------
        ρab (Δʳa (Δˡε γ)) P≈ ρab (Δˡb (Δʳε γ))

    have γ ass =
        begin
            ρab (Δʳa (Δˡε γ))
                ≈⟨ ρΔʳa-lem (Δˡε γ) ⟩
            Δʳ b ↑ (ρa (Δˡε γ))
                ≈⟨ invariance (Δʳ b) (ρΔˡε-lem γ) ⟩
            Δʳ b ↑ (Δˡ a ↑ (ρε γ))
                ≈⟨ ass ⟩
            Δˡ a ↑ (Δʳ b ↑ (ρε γ))
                ≈⟨ invariance (Δˡ a) (ρΔʳε-lem γ) ⟨
            Δˡ a ↑ (ρb (Δʳε γ))
                ≈⟨ ρΔˡb-lem (Δʳε γ) ⟨
            ρab (Δˡb (Δʳε γ))
        ∎ where open EqP

    thm :
        ∀ (γ : Term εXε) →
        Δʳ b ↑ (Δˡ a ↑ (ρε γ)) P≈ Δˡ a ↑ (Δʳ b ↑ (ρε γ)) →
        --------------------------------------------------
        Δʳa (Δˡε γ) P≈ Δˡb (Δʳε γ)

    thm γ eq = transfer (Δʳa (Δˡε γ)) (Δˡb (Δʳε γ)) (have γ eq)
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
