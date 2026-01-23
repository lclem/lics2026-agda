---
title: "Definition"
---

For special product rules,
the semantics of term automata is invariant under term equivalence.
In other words, term automata are polynomial automatam,
that is, automata whose states are bona-fide polynomials.

```
{-# OPTIONS --guardedness --sized-types #-}
-- {-# OPTIONS --allow-unsolved-metas #-}

open import Preliminaries.Base
open import General.ProductRules
open import Special.ProductRules

module Special.Automata
    (R : CommutativeRing)
    (Σ : Set)
    (P : ProductRule R)
    (special : Special R P)
    where

open import General.Terms R
open import General.Products R Σ
open import General.Automata R Σ P

open import Special.Polynomials R -- renaming (_≈_ to _[≈]_)
open import Special.Products R Σ

open Product P hiding (_*_; *-cong)
open ProductProperties special

private variable X : Set
```

# Syntactic invariance

We show that for every substitution `Δ`,
its extension `Δ ↑` to all terms preserves equivalence of terms.
This is a crucial fact.

```
invariance :
    ∀ (Δ : Subst X X) {α β : Term X} →
    α ≈ β →
    ----------------------------------
    Δ ↑ α ≈ Δ ↑ β

invariance Δ = go where

    go : ∀ {α β} → α ≈ β → Δ ↑ α ≈ Δ ↑ β

    go ≈-refl = ≈-refl
    go (≈-sym α≈β) = ≈-sym (go α≈β)
    go (≈-trans α≈β β≈γ) = ≈-trans (go α≈β) (go β≈γ)
    go (·-cong c≈d α≈β) = ·-cong c≈d (go α≈β)
    go {β = β} (·-one _) = ·-one (Δ ↑ β)
    go (·-+-distrib c p q) = ·-+-distrib c (Δ ↑ p) (Δ ↑ q)
    go (+-·-distrib p c d) = +-·-distrib (Δ ↑ p) c d
    go (·-*-distrib c p q) =
        begin
            Δ ↑ ((c · p) * q)
                ≈⟨⟩
            [ P ]⟨ c · p , c · Δ ↑ p , q , Δ ↑ q ⟩
                ≡⟨ substᵥ-substᵥ P (_ ∷ _ ∷ _ ∷ _ ∷ []) (_ ∷ _ ∷ _ ∷ _ ∷ []) ⟨
            [ [ P ]⟨ c · x , c · x′ , y , y′ ⟩ ]⟨ p , Δ ↑ p , q , Δ ↑ q ⟩
                ≈⟨ subst-invᵥ (_ ∷ _ ∷ _ ∷ _ ∷ []) (P-compat special c) ⟩
            [ c · [ P ]⟨ x , x′ , y , y′ ⟩ ]⟨ p , Δ ↑ p , q , Δ ↑ q ⟩
                ≈⟨⟩
            c · [ [ P ]⟨ x , x′ , y , y′ ⟩ ]⟨ p , Δ ↑ p , q , Δ ↑ q ⟩
                ≡⟨ cong (_·_ c) (substᵥ-substᵥ P (_ ∷ _ ∷ _ ∷ _ ∷ []) (_ ∷ _ ∷ _ ∷ _ ∷ [])) ⟩
            c · [ P ]⟨ p , Δ ↑ p , q , Δ ↑ q ⟩
                ≈⟨⟩
            Δ ↑ (c · p * q)
        ∎ where open EqP
    go (*-·-distrib c d p) = *-·-distrib c d (Δ ↑ p)
    go (+-cong α≈β α≈β₁) = +-cong (go α≈β) (go α≈β₁)
    go {β = β} (+-zeroʳ _) = +-zeroʳ (Δ ↑ β)
    go (+-assoc p q r) = +-assoc (Δ ↑ p) (Δ ↑ q) (Δ ↑ r)
    go (+-comm p q) = +-comm (Δ ↑ p) (Δ ↑ q)
    go (+-invʳ p) = +-invʳ (Δ ↑ p)
    go {α = p₀ * q₀} {β = p₁ * q₁} (*-cong p₀≈p₁ q₀≈q₁) =
        begin
            Δ ↑ (p₀ * q₀)
                ≈⟨⟩
            [ P ]⟨ p₀ , Δ ↑ p₀ , q₀ , Δ ↑ q₀ ⟩
                ≈⟨ subst-inv′ᵥ P (p₀≈p₁ ∷-≈ go p₀≈p₁ ∷-≈ q₀≈q₁ ∷-≈ go q₀≈q₁ ∷-≈ []-≈) ⟩
            [ P ]⟨ p₁ , Δ ↑ p₁ , q₁ , Δ ↑ q₁ ⟩
                ≈⟨⟩
            Δ ↑ (p₁ * q₁)
        ∎ where open EqP

    go (*-assoc p q r) =
        begin
            Δ ↑ ((p * q) * r)
                ≈⟨⟩
            [ P ]⟨ p * q , [ P ]⟨ p , Δ ↑ p , q , Δ ↑ q ⟩ , r , Δ ↑ r ⟩
                ≈⟨ subst-inv′ᵥ P (≈-refl ∷-≈ ≡→≈ (substᵥ-substᵥ P (_ ∷ _ ∷ _ ∷ _ ∷ []) (_ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _ ∷ [])) ∷-≈ ≈-refl ∷-≈ ≈-refl ∷-≈ []-≈) ⟨
            [ P ]⟨ [ x * y ]ᵥ ϱ , [ [ P ]⟨ x , x′ , y , y′ ⟩ ]ᵥ ϱ , [ z ]ᵥ ϱ , [ z′ ]ᵥ ϱ ⟩
                ≡⟨ substᵥ-substᵥ P (_ ∷ _ ∷ _ ∷ _ ∷ []) ϱ ⟨
            [ [ P ]⟨ x * y , [ P ]⟨ x , x′ , y , y′ ⟩ ,  z , z′ ⟩ ]ᵥ ϱ
                ≈⟨ subst-invᵥ (_ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _ ∷ []) (P-assoc special) ⟩
            [ [ P ]⟨ x , x′ , y * z , [ P ]⟨ y , y′ , z , z′ ⟩ ⟩ ]ᵥ ϱ
                ≡⟨ substᵥ-substᵥ P (_ ∷ _ ∷ _ ∷ _ ∷ []) ϱ ⟩
            [ P ]⟨ [ x ]ᵥ ϱ , [ x′ ]ᵥ ϱ , [ y * z ]ᵥ ϱ , [ [ P ]⟨ y , y′ , z , z′ ⟩ ]ᵥ ϱ ⟩
                ≈⟨ subst-inv′ᵥ P (≈-refl ∷-≈ ≈-refl ∷-≈ ≈-refl ∷-≈ ≡→≈ (substᵥ-substᵥ P (_ ∷ _ ∷ _ ∷ _ ∷ []) (_ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _ ∷ [])) ∷-≈ []-≈) ⟩
            [ P ]⟨ p , Δ ↑ p , q * r , [ P ]⟨ q , Δ ↑ q , r , Δ ↑ r ⟩ ⟩
                ≈⟨⟩
            Δ ↑ (p * (q * r))
        ∎ where            
            open EqP
            ϱ = p ∷ Δ ↑ p ∷ q ∷ Δ ↑ q ∷ r ∷ Δ ↑ r ∷ []

    go (*-comm p q) =
        begin
            Δ ↑ (p * q)
                ≈⟨⟩
            [ P ]⟨ p , Δ ↑ p , q , Δ ↑ q ⟩
                ≡⟨ substᵥ-substᵥ P (_ ∷ _ ∷ _ ∷ _ ∷ []) (_ ∷ _ ∷ _ ∷ _ ∷ []) ⟨
            [ [ P ]⟨ x , x′ , y , y′ ⟩ ]⟨ p , Δ ↑ p , q , Δ ↑ q ⟩
                ≈⟨ subst-invᵥ (_ ∷ _ ∷ _ ∷ _ ∷ []) (P-comm special) ⟩
            [ [ P ]⟨ y , y′ , x , x′ ⟩ ]⟨ p , Δ ↑ p , q , Δ ↑ q ⟩
                ≡⟨ substᵥ-substᵥ P (_ ∷ _ ∷ _ ∷ _ ∷ []) (_ ∷ _ ∷ _ ∷ _ ∷ []) ⟩
            [ P ]⟨ q , Δ ↑ q , p , Δ ↑ p ⟩
                ≈⟨⟩
            Δ ↑ (q * p)
        ∎ where open EqP

    go (*-distribʳ r p q) =
        let ϱ = p ∷ Δ ↑ p ∷ q ∷ Δ ↑ q ∷ r ∷ Δ ↑ r ∷ [] in
        begin
            Δ ↑ ((p + q) * r)
                ≈⟨⟩
            [ P ]⟨ p + q , Δ ↑ p + Δ ↑ q , r , Δ ↑ r ⟩
                ≈⟨⟩
            [ P ]⟨ [ x + y ]ᵥ ϱ , [ x′ + y′ ]ᵥ ϱ , [ z ]ᵥ ϱ , [ z′ ]ᵥ ϱ ⟩
                ≡⟨ substᵥ-substᵥ P (_ ∷ _ ∷ _ ∷ _ ∷ []) ϱ ⟨
            [ [ P ]⟨ x + y , x′ + y′ , z , z′ ⟩ ]ᵥ ϱ
                ≈⟨ subst-invᵥ (_ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _ ∷ []) (P-add special) ⟩
            [ [ P ]⟨ x , x′ , z , z′ ⟩ + [ P ]⟨ y , y′ , z , z′ ⟩ ]ᵥ ϱ
                ≈⟨⟩
            [ [ P ]⟨ x , x′ , z , z′ ⟩ ]ᵥ ϱ + [ [ P ]⟨ y , y′ , z , z′ ⟩ ]ᵥ ϱ
                ≡⟨ cong₂ _+_ (substᵥ-substᵥ P (_ ∷ _ ∷ _ ∷ _ ∷ []) ϱ) (substᵥ-substᵥ P (_ ∷ _ ∷ _ ∷ _ ∷ []) ϱ) ⟩
            [ P ]⟨ p , Δ ↑ p , r , Δ ↑ r ⟩ + [ P ]⟨ q , Δ ↑ q , r , Δ ↑ r ⟩
                ≈⟨⟩
            Δ ↑ (p * r + q * r)
        ∎ where open EqP
```

# Semantic invariance

We show that the semantics of term automata is invariant under the equivalence generated by axioms of commutative algebras.
We rely only on !remoteRef(General)(Automata)(sem-hom) and `sem-inv`.

An alternative proof using !ref(invariance) above is also possible.

```
open import General.Series R Σ renaming (_≈_ to _≈S_)
semantic-invariance :
    ∀ (S : TermAut X) {α β : Term X} →
    α ≈ β →
    ----------------------------------
    S ⟦ α ⟧ ≈S S ⟦ β ⟧

semantic-invariance S {α} {β} α≈β = begin
    S ⟦ α ⟧
        ≈⟨ sem-hom _ _ ⟩
    ⟦ α ⟧ (S ⟦X⟧)
        ≈⟨ sem-inv α≈β ⟩
    ⟦ β ⟧ (S ⟦X⟧)
        ≈⟨ sem-hom _ _ ⟨
    S ⟦ β ⟧
    ∎ where open EqS
```
