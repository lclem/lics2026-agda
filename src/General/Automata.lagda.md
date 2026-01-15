---
title: "Definition 🚧"
---

```
{-# OPTIONS --guardedness --sized-types #-}
-- --allow-unsolved-metas

open import Preliminaries.Base
open import General.ProductRules

module General.Automata
    (R : CommutativeRing)
    (Σ : Set)
    (productRule : ProductRule R)
    where

open import Size

open import Preliminaries.Vector
open import Preliminaries.Algebra R
open import Preliminaries.PolyExpr R
    using (PolyExpr; con)
    renaming (subst to P-subst; ⟦_⟧_ to P⟦_⟧_)

open import General.Series R Σ
open import General.Products R Σ
open import General.Terms R
    renaming (_+_ to _[+]_; _*_ to _[*]_; _·_ to _[·]_)

open Product productRule
open ProductRule productRule

private variable
    i : Size
    n : ℕ
```

# Syntax

A polynomial automaton is an automaton whose states are polynomials
(in possibly infinitely many variables).

```
record TermAut (X : Set) : Set where
    field
        -- output function
        F : X → A
        -- transitions
        Δ : (a : Σ) → X → Term X

open TermAut public
private variable X : Set
```

# Semantics

Extension of the transition function to all polynomials.

```
infix 20 _↑_
_↑_ : (Δ : Subst X X) → Term X → Term X
Δ ↑ 0T = 0T
Δ ↑ (var x) = Δ x
Δ ↑ (c [·] q) = c [·] Δ ↑ q
Δ ↑ (p [+] q) = Δ ↑ p [+] Δ ↑ q
Δ ↑ (p [*] q) = [ P ]⟨ p , Δ ↑ p , q , Δ ↑ q ⟩
```

Semantics of a polynomial automaton.

```
open Semantics
    renaming (⟦_⟧_ to T⟦_⟧_)
    hiding (⟦_⟧ᵥ_; ⟦_⟧⟨_,_,_,_⟩; sem-cong)

infix 200 _⟦_⟧
_⟦_⟧ : TermAut X → Term X → A ⟪ Σ ⟫
ν (S ⟦ α ⟧) = T⟦ α ⟧ (F S)
δ (S ⟦ α ⟧) a = S ⟦ Δ S a ↑ α ⟧
```

# Homomorphism lemma

The semantics of a polynomial automaton is a homomorphism from polynomial expressions to series.
These properties do not rely on any assumption on `spec`.

```
mutual

    infix 200 _⟦X⟧
    _⟦X⟧ : TermAut X → X → A ⟪ Σ ⟫ i
    S ⟦X⟧ = λ x → S ⟦ var x ⟧

    sem-𝟘 :
        ∀ (S : TermAut X) →
        -------------------
        S ⟦ 0T ⟧ ≈[ i ] 𝟘

    ν-≈ (sem-𝟘 S) = R-refl
    δ-≈ (sem-𝟘 S) a = sem-𝟘 S

    sem-· :
        ∀ (S : TermAut X) c p →
        -------------------------------
        S ⟦ c [·] p ⟧ ≈[ i ] c · S ⟦ p ⟧

    ν-≈ (sem-· S c p) = R-refl
    δ-≈ (sem-· S c p) a =
        begin
            δ (S ⟦ c [·] p ⟧) a
                ≈⟨⟩
            S ⟦ Δ S a ↑ (c [·] p) ⟧
                ≈⟨⟩
            S ⟦ c [·] Δ S a ↑ p ⟧
                ≈⟨ sem-· S _ _ ⟩
            c · S ⟦ Δ S a ↑ p ⟧
                ≈⟨⟩
            δ (c · S ⟦ p ⟧) a
        ∎ where open EqS

    sem-+ :
        ∀ (S : TermAut X) {α β} →
        ------------------------------------
        S ⟦ α [+] β ⟧ ≈[ i ] S ⟦ α ⟧ + S ⟦ β ⟧

    ν-≈ (sem-+ S) = R-refl
    δ-≈ (sem-+ S) _ = sem-+ S

    sem-* :
        ∀ (S : TermAut X) {α β} →
        ------------------------------------
        S ⟦ α [*] β ⟧ ≈[ i ] S ⟦ α ⟧ * S ⟦ β ⟧

    ν-≈ (sem-* S) = R-refl
    δ-≈ (sem-* S {p} {q}) a =
        begin
            S ⟦ Δ S a ↑ (p [*] q) ⟧
                ≈⟨⟩
            S ⟦ [ P ]⟨ p , Δ S a ↑ p , q , Δ S a ↑ q ⟩ ⟧
                ≈⟨ sem-substᵥ S P (_ ∷ _ ∷ _ ∷ _ ∷ []) ⟩
            ⟦ P ⟧⟨ S ⟦ p ⟧ , S ⟦ Δ S a ↑ p ⟧ , S ⟦ q ⟧ , S ⟦ Δ S a ↑ q ⟧ ⟩
        ∎ where open EqS
```

!lemma(#lemma:automataSemHom)(Homomorphism lemma)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
The semantics of an automaton is a homomorphism from terms to series.
```
    sem-hom :
        ∀ (S : TermAut X) (p : Term X) →
        ------------------------------
        S ⟦ p ⟧ ≈[ i ] ⟦ p ⟧ (S ⟦X⟧)
```
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This will be used elsewhere.
!remoteRef(General)(Terms)(Term)(var)

```
    sem-hom S 0T = sem-𝟘 S
    sem-hom S (var x) = ≈-refl

    sem-hom S (c [·] p) =
        begin
            S ⟦ c [·] p ⟧
                ≈⟨ sem-· S c p ⟩
            c · S ⟦ p ⟧
                ≈⟨ ·-cong R-refl (sem-hom S p) ⟩
            c · ⟦ p ⟧ (S ⟦X⟧)
                ≈⟨⟩
            ⟦ c [·] p ⟧ (S ⟦X⟧)
        ∎ where open EqS

    sem-hom S (p [+] q) = 
        begin
            S ⟦ p [+] q ⟧
                ≈⟨ sem-+ S ⟩
            S ⟦ p ⟧ + S ⟦ q ⟧
                ≈⟨ +-cong (sem-hom S p) (sem-hom S q) ⟩
            ⟦ p ⟧ (S ⟦X⟧) + ⟦ q ⟧ (S ⟦X⟧)
                ≈⟨⟩
            ⟦ p [+] q ⟧ (S ⟦X⟧)
        ∎ where open EqS

    sem-hom S (p [*] q) =
        begin
            S ⟦ p [*] q ⟧
                ≈⟨ sem-* S ⟩
            S ⟦ p ⟧ * S ⟦ q ⟧
                ≈⟨ *-cong (sem-hom S p) (sem-hom S q) ⟩
            ⟦ p ⟧ (S ⟦X⟧) * ⟦ q ⟧ (S ⟦X⟧)
                ≈⟨⟩
            ⟦ p [*] q ⟧ (S ⟦X⟧)
        ∎ where open EqS

    sem-substᵥ :
        ∀ (S : TermAut X) (p : TE n) (qs : VSubst n X) →
        ------------------------------------------------------
        S ⟦ substᵥ qs p ⟧ ≈[ i ] ⟦ p ⟧ᵥ (map (λ q → S ⟦ q ⟧) qs)
    
    sem-substᵥ S p qs =
        begin
            S ⟦ substᵥ qs p ⟧
                ≈⟨ sem-hom S _ ⟩
            ⟦ subst (lookup qs) p ⟧ (S ⟦X⟧)
                ≈⟨ eval-substᵥ p {qs} ⟩
            ⟦ p ⟧ᵥ (map (λ q → ⟦ q ⟧ (S ⟦X⟧)) qs)
                ≈⟨ sem-congᵥ p (map-cong _ _ qs (sem-hom S)) ⟨
            ⟦ p ⟧ᵥ (map (λ q → S ⟦ q ⟧) qs)
        ∎ where open EqS

    sem-subst : ∀ (S : TermAut X) (p : Term X) (ϱ : Subst X X) →
        S ⟦ subst ϱ p ⟧ ≈[ i ] ⟦ p ⟧ (λ x → S ⟦ ϱ x ⟧)
    sem-subst S p ϱ =
        begin
            S ⟦ subst ϱ p ⟧
                ≈⟨ sem-hom S _ ⟩
            ⟦ subst ϱ p ⟧ (S ⟦X⟧)
                ≈⟨ eval-subst p ⟩
            ⟦ p ⟧ (λ x → ⟦ ϱ x ⟧ (S ⟦X⟧))
                ≈⟨ sem-cong p (\ x → sem-hom S (ϱ x)) ⟨
            ⟦ p ⟧ (λ x → S ⟦ ϱ x ⟧)
        ∎ where open EqS
```

# Equivalence with finitely generated series {#sec:coincidence}


We show that the class of series recognized by term automata
coincides with the class of finitely generated series.

```
open import General.FinitelyGenerated R Σ productRule
```

## From automata to *-finite series

We show that a polynomial automaton with `n` variables recognises only *-finite series.

```
module PolyAut→*Fin (n : ℕ) where

    TA = TermAut (Fin n)
    ST = TE n

    rec→*-Fin : ∀ (S : TA) (α : ST) → *-Fin (S ⟦ α ⟧) n
    rec→*-Fin S α = *-Fin[ gs , S⟦α⟧∈[gs] α , cl ] where

        -- recall that S ⟦X⟧ = λ x → S ⟦ var x ⟧ is the valuation that maps each variable to its semantics
        gs : Vec (A ⟪ Σ ⟫) n
        gs = tabulate (S ⟦X⟧)

        -- the semantics of variables trivially belongs to the algebra they generate
        S⟦var⟧∈gs : ∀ (i : Fin n) → S ⟦ var i ⟧ ∈[ gs ]
        S⟦var⟧∈gs i = gen∈ (∈-tabulate⁺ _ i)

        -- the value of polynomial expression whose variables evaluate to the generators belong to the algebra they generate
        ⟦α⟧∈[gs] : ∀ α → ⟦ α ⟧ (S ⟦X⟧) ∈[ gs ]
        ⟦α⟧∈[gs] α = subalgebra α S⟦var⟧∈gs

        -- the semantics is a homomorphism
        S⟦α⟧≈⟦α⟧ : ∀ α → S ⟦ α ⟧ ≈ ⟦ α ⟧ (S ⟦X⟧)
        S⟦α⟧≈⟦α⟧ = sem-hom S

        -- the semantics of every polynomial expression belongs to the algebra generated by the semantics of variables
        S⟦α⟧∈[gs] : ∀ α → S ⟦ α ⟧ ∈[ gs ]
        S⟦α⟧∈[gs] α = S⟦α⟧≈⟦α⟧ α ≈∈ (⟦α⟧∈[gs] α)

        cl : ∀ (a : Σ) {g} → g ∈ gs → δ g a ∈[ gs ]
        cl a {g} g∈gs = δga∈[gs] where

            j : Fin n
            j with ∈-tabulate⁻ g∈gs
            ... | i ,, _ = i

            -- g is of the form S ⟦ var i ⟧ for some i : Fin n        
            g≡S⟦var⟧ : g ≡ S ⟦ var j ⟧
            g≡S⟦var⟧ with ∈-tabulate⁻ g∈gs
            ... | _ ,, x = x

            δga≡δS⟦var⟧ : δ g a ≡ δ (S ⟦ var j ⟧) a
            δga≡δS⟦var⟧ = cong (λ g → δ g a) g≡S⟦var⟧

            δga∈[gs] : δ g a ∈[ gs ]
            δga∈[gs] rewrite δga≡δS⟦var⟧ = S⟦α⟧∈[gs] _
```

## From *-finite series to automata

We show that *-finite series are recognisable by polynomial automata.

```
module *-Fin→PolyAut {f} (Fin-f : *-Fin f n) where

    -- there are m variables
    V = Var n

    -- generators
    gs : Vec (A ⟪ Σ ⟫) n
    gs = gen Fin-f

    -- the i-th generator
    g : V → A ⟪ Σ ⟫
    g i = lookup gs i

    -- the i-th generator is indeed a generator
    g∈gs : ∀ i → g i ∈ gs
    g∈gs i = ∈-lookup i gs

    xt : ∀ {f} → f ∈[ gs ] → ∃[ α ] f ≈ ⟦ α ⟧ (lookup gs)
    xt f∈[gs] = extract _ _ f∈[gs]

    -- given a series in the algebra, get the generating term
    xt-α : ∀ {f} → f ∈[ gs ] → TE n
    xt-α f∈[gs] = fst (xt f∈[gs])

    xt-f≈⟦α⟧ : ∀ {f} → (f∈[gs] : f ∈[ gs ]) → f ≈ ⟦ xt-α f∈[gs] ⟧ (lookup gs)
    xt-f≈⟦α⟧ f∈[gs] = snd (xt f∈[gs])

    δga∈[gs] : ∀ i a → δ (g i) a ∈[ gs ]
    δga∈[gs] i a = closed Fin-f a (g∈gs i)

    α : ∀ i a → TE n
    α i a = xt-α (δga∈[gs] i a)

    δga≈⟦α⟧ : ∀ i a → δ (g i) a ≈ ⟦ α i a ⟧ (lookup gs)
    δga≈⟦α⟧ i a = xt-f≈⟦α⟧ (δga∈[gs] i a)

    -- construct the automaton
    S : TermAut V
    S = record {
            F = λ i → ν (g i);
            Δ = λ a i → α i a
        }

    S⟦α⟧≈⟦α⟧ : ∀ α → S ⟦ α ⟧ ≈ ⟦ α ⟧ (S ⟦X⟧)
    S⟦α⟧≈⟦α⟧ α = sem-hom S α

    mutual
        
        sound-var : ∀ x → S ⟦ var x ⟧ ≈[ i ] g x
        ν-≈ (sound-var x) = R-refl
        δ-≈ (sound-var x) a =
            let β = α x a in
            begin
                S ⟦ β ⟧
                    ≈⟨ sound _ ⟩
                ⟦ β ⟧ g
                    ≈⟨ δga≈⟦α⟧ x a ⟨
                δ (g x) a
            ∎ where open EqS

        sound : ∀ α → S ⟦ α ⟧ ≈[ i ] ⟦ α ⟧ g
        sound α = 
            begin
                S ⟦ α ⟧
                    ≈⟨ S⟦α⟧≈⟦α⟧ _ ⟩
                ⟦ α ⟧ (S ⟦X⟧)
                    ≈⟨ sem-cong α sound-var ⟩
                ⟦ α ⟧ g
            ∎ where open EqS

    f∈[gs] : f ∈[ gs ]
    f∈[gs] = memb Fin-f

    β : TE n
    β = xt-α f∈[gs]

    f≈⟦β⟧ : f ≈ ⟦ β ⟧ g
    f≈⟦β⟧ = snd (xt f∈[gs])

    -- in particular, the automaton recognises f from configuration β
    theorem : f ≈ S ⟦ β ⟧
    theorem =
        begin
            f
                ≈⟨ f≈⟦β⟧ ⟩
            ⟦ β ⟧ g
                ≈⟨ sound _ ⟨
            S ⟦ β ⟧
        ∎ where open EqS
```