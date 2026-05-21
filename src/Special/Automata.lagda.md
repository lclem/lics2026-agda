---
title: "Polynomial automata"
prev: /Special/Products/
next: /Special/Reversal/
---

In this section we revisit [`P`-automata](../../General/Automata)
in the case of a special product rule `P`.
The main result is that, for special product rules,
the semantics of automata is invariant under term equivalence.
In other words, term automata are in fact *polynomial* automata,
that is, automata whose states are bona-fide polynomials.

The rest of this chapter is organised as follows.

- In !secRef(the first section)(#sec:syntactic-invariance) we show that
the extension of the transition relation of a `P`-automata to all terms preserves equivalence of terms.

- In !secRef(the second section)(#sec:semantic-invariance) we show that
the semantics of `P`-automata is invariant under term equivalence.

```
{-# OPTIONS --guardedness --sized-types #-}

open import Preliminaries.Base
open import General.ProductRules
open import Special.Polynomials using (Special)

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
open import Special.Products R Σ P special

open Product P hiding (_*_; *-cong)

private variable X : Set
```

# Syntactic invariance {#sec:syntactic-invariance}

We show that for every substitution `Δ`,
its extension `Δ ↑` to all terms preserves equivalence of terms.
This is a crucial fact.

```
invariance :
    ∀ (Δ : Subst X X) {α β : Term X} →
    α ≈ β →
    ----------------------------------
    Δ ↑ α ≈ Δ ↑ β
```

The proof is by induction on the derivation of `α ≈ β`.
Some cases are rather straightforward.

```
invariance Δ = go where

    go : ∀ {α β} → α ≈ β → Δ ↑ α ≈ Δ ↑ β

    go ≈-refl = ≈-refl
    go (≈-sym α≈β) = ≈-sym (go α≈β)
    go (≈-trans α≈β β≈γ) = ≈-trans (go α≈β) (go β≈γ)
    go (·-cong c≈d α≈β) = ·-cong c≈d (go α≈β)
    go {β = β} (·-one _) = ·-one (Δ ↑ β)
    go (·-+-distrib c p q) = ·-+-distrib c (Δ ↑ p) (Δ ↑ q)
    go (+-·-distrib p c d) = +-·-distrib (Δ ↑ p) c d
```

The cases involving the series product rely on the fact that the product satisfies a special product rule.
For example, in the case of compatibility with scalar multiplication, we rely on `P-compat`.

```
    go (·-*-distrib c p q) = begin
        Δ ↑ ((c · p) * q)
            ≈⟨⟩
        [ P ]⟨ c · p , c · Δ ↑ p , q , Δ ↑ q ⟩
            ≡⟨ substᵥ-substᵥ P (_ ∷ _ ∷ _ ∷ _ ∷ []) (_ ∷ _ ∷ _ ∷ _ ∷ []) ⟨
        [ [ P ]⟨ c · x , c · x′ , y , y′ ⟩ ]⟨ p , Δ ↑ p , q , Δ ↑ q ⟩
            ≈⟨ subst-invᵥ (_ ∷ _ ∷ _ ∷ _ ∷ []) (P-compat special c) ⟩
        [ c · [ P ]⟨ x , x′ , y , y′ ⟩ ]⟨ p , Δ ↑ p , q , Δ ↑ q ⟩
            ≈⟨⟩
        c · [ [ P ]⟨ x , x′ , y , y′ ⟩ ]⟨ p , Δ ↑ p , q , Δ ↑ q ⟩
            ≡⟨ cong (_·_ c) aux ⟩
        c · [ P ]⟨ p , Δ ↑ p , q , Δ ↑ q ⟩
            ≈⟨⟩
        Δ ↑ (c · p * q)
        ∎ where        
            open EqP
            aux = substᵥ-substᵥ P (_ ∷ _ ∷ _ ∷ _ ∷ []) (_ ∷ _ ∷ _ ∷ _ ∷ [])
```

The next few cases are simple.

```
    go (*-·-distrib c d p) = *-·-distrib c d (Δ ↑ p)
    go (+-cong α≈β α≈β₁) = +-cong (go α≈β) (go α≈β₁)
    go {β = β} (+-zeroʳ _) = +-zeroʳ (Δ ↑ β)
    go (+-assoc p q r) = +-assoc (Δ ↑ p) (Δ ↑ q) (Δ ↑ r)
    go (+-comm p q) = +-comm (Δ ↑ p) (Δ ↑ q)
    go (+-invʳ p) = +-invʳ (Δ ↑ p)

    go {α = p₀ * q₀} {β = p₁ * q₁} (*-cong p₀≈p₁ q₀≈q₁) = begin
        Δ ↑ (p₀ * q₀)
            ≈⟨⟩
        [ P ]⟨ p₀ , Δ ↑ p₀ , q₀ , Δ ↑ q₀ ⟩
            ≈⟨ subst-inv′ᵥ P (p₀≈p₁ ∷-≈ go p₀≈p₁ ∷-≈ q₀≈q₁ ∷-≈ go q₀≈q₁ ∷-≈ []-≈) ⟩
        [ P ]⟨ p₁ , Δ ↑ p₁ , q₁ , Δ ↑ q₁ ⟩
            ≈⟨⟩
        Δ ↑ (p₁ * q₁)
        ∎ where open EqP
```

The case for associativity relies on `P-assoc`.

```
    go (*-assoc p q r) = begin
        Δ ↑ ((p * q) * r)
            ≈⟨⟩
        [ P ]⟨ p * q , [ P ]⟨ p , Δ ↑ p , q , Δ ↑ q ⟩ , r , Δ ↑ r ⟩
            ≈⟨ subst-inv′ᵥ P aux₀ ⟨
        [ P ]⟨ [ x * y ]ᵥ ϱ , [ [ P ]⟨ x , x′ , y , y′ ⟩ ]ᵥ ϱ , [ z ]ᵥ ϱ , [ z′ ]ᵥ ϱ ⟩
            ≡⟨ substᵥ-substᵥ P (_ ∷ _ ∷ _ ∷ _ ∷ []) ϱ ⟨
        [ [ P ]⟨ x * y , [ P ]⟨ x , x′ , y , y′ ⟩ ,  z , z′ ⟩ ]ᵥ ϱ
            ≈⟨ subst-invᵥ (_ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _ ∷ []) (P-assoc special) ⟩
        [ [ P ]⟨ x , x′ , y * z , [ P ]⟨ y , y′ , z , z′ ⟩ ⟩ ]ᵥ ϱ
            ≡⟨ substᵥ-substᵥ P (_ ∷ _ ∷ _ ∷ _ ∷ []) ϱ ⟩
        [ P ]⟨ [ x ]ᵥ ϱ , [ x′ ]ᵥ ϱ , [ y * z ]ᵥ ϱ , [ [ P ]⟨ y , y′ , z , z′ ⟩ ]ᵥ ϱ ⟩
            ≈⟨ subst-inv′ᵥ P aux₁ ⟩
        [ P ]⟨ p , Δ ↑ p , q * r , [ P ]⟨ q , Δ ↑ q , r , Δ ↑ r ⟩ ⟩
            ≈⟨⟩
        Δ ↑ (p * (q * r))
        ∎ where            
            open EqP

            ϱ = p ∷ Δ ↑ p ∷ q ∷ Δ ↑ q ∷ r ∷ Δ ↑ r ∷ []

            aux₀ = ≈-refl ∷-≈ ≡→≈ (substᵥ-substᵥ P (_ ∷ _ ∷ _ ∷ _ ∷ [])
                (_ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _ ∷ [])) ∷-≈ ≈-refl ∷-≈ ≈-refl ∷-≈ []-≈
            
            aux₁ = ≈-refl ∷-≈ ≈-refl ∷-≈ ≈-refl ∷-≈ ≡→≈ (substᵥ-substᵥ P
                (_ ∷ _ ∷ _ ∷ _ ∷ []) (_ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _ ∷ [])) ∷-≈ []-≈
```

The case for commutativity relies on `P-comm`.

```
    go (*-comm p q) = begin
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
```

The case for distributivity relies on `P-add`.

```
    go (*-distribʳ r p q) = begin
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
            ≡⟨ cong₂ _+_ aux₀ aux₁ ⟩
        [ P ]⟨ p , Δ ↑ p , r , Δ ↑ r ⟩ + [ P ]⟨ q , Δ ↑ q , r , Δ ↑ r ⟩
            ≈⟨⟩
        Δ ↑ (p * r + q * r)
        ∎ where
            open EqP
            ϱ = p ∷ Δ ↑ p ∷ q ∷ Δ ↑ q ∷ r ∷ Δ ↑ r ∷ []
            aux₀ = substᵥ-substᵥ P (_ ∷ _ ∷ _ ∷ _ ∷ []) ϱ
            aux₁ = substᵥ-substᵥ P (_ ∷ _ ∷ _ ∷ _ ∷ []) ϱ
```

This concludes the proof of syntactic invariance.

# Semantic invariance {#sec:semantic-invariance}

We show that the semantics of term automata is invariant under the equivalence generated by axioms of commutative algebras.
We rely only on !remoteRef(General)(Automata)(sem-hom) and !remoteRef(Special)(Products)(sem-inv).

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

An alternative proof using !ref(invariance) above is also possible.
