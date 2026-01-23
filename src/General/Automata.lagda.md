---
title: "Automata"
---

```
{-# OPTIONS --guardedness --sized-types #-}
```

Let `P` be a product rule.
In this section we define `P`-automata.
The main result is that the class of `P`-finite series coincides with
the series recognised by `P`-automata over finitely many variables.

```
open import Preliminaries.Base
open import General.ProductRules

module General.Automata
    (R : CommutativeRing)
    (Σ : Set)
    (P : ProductRule R)
    where
```

```
open import Size

open import Preliminaries.Vector
open import Preliminaries.Algebra R

open import General.Series R Σ
open import General.Products R Σ
open import General.Terms R
    renaming (_+_ to _[+]_; _*_ to _[*]_; _·_ to _[·]_)

open Product P

private variable
    i : Size
    n : ℕ
```

# Syntax of `P`-automata

A *`P`-automaton* (or *term automaton*) is an automaton whose states are terms
(in possibly infinitely many variables).
It is defined by specifying

- an output function `F` that maps each variable to an output in `A`, and
- a transition function `Δ` that maps each input symbol and variable to a term.

Formally, term automata are defined as follows.

```
record TermAut (X : Set) : Set where
    field
        F : X → A                -- output function
        Δ : (a : Σ) → X → Term X -- transitions

open TermAut public
private variable X : Set
```

# Semantics of `P`-automata

## `P`-extensions

We extend the transition function from variables to all terms.
To this end, for any function `Δ : Subst X X` (mapping variables to terms),
let `Δ ↑` be the function mapping terms to terms defined as follows.

```
infix 20 _↑_
_↑_ : (Δ : Subst X X) → Term X → Term X
Δ ↑ 0T = 0T
Δ ↑ (var x) = Δ x
Δ ↑ (c [·] q) = c [·] Δ ↑ q
Δ ↑ (p [+] q) = Δ ↑ p [+] Δ ↑ q
Δ ↑ (p [*] q) = [ P ]⟨ p , Δ ↑ p , q , Δ ↑ q ⟩
```

Note that in the rule for the product of two terms we use the product rule `P`.
For this reason, we call `Δ ↑` the *`P`-extension* of `Δ`.

## Semantics

```
open Semantics
    renaming (⟦_⟧_ to T⟦_⟧_)
    hiding (⟦_⟧ᵥ_; ⟦_⟧⟨_,_,_,_⟩; ⟦_⟧≈_)
```

Thanks to the `P`-extension function `_↑_`,
we can now define the *semantics* of a term automaton `S : TermAut X`,
which is the function `S ⟦_⟧` mapping terms to series.

Let `α : Term X` be a term.
We define `S ⟦ α ⟧` coinductively.

- In the base case, we output the value of `F` at `α` (computed by its homomorphic extension).
- In the coinductive case, given an input symbol `a : Σ`,
  we transition to the term obtained by applying the `P`-extension of `Δ S a` to `α`.

Formally, we obtain the following definition.

```
infix 200 _⟦_⟧
_⟦_⟧ : TermAut X → Term X → A ⟪ Σ ⟫                                                                
ν (S ⟦ α ⟧) = T⟦ α ⟧ (F S)
δ (S ⟦ α ⟧) a = S ⟦ Δ S a ↑ α ⟧
```

## Homomorphism lemma

We show that the semantics of a `P`-automaton is a homomorphism from terms to series.
This does not rely on any assumption on the product rule `P`.

We write `S ⟦X⟧ x` to denote the series recognised by automaton `S` starting from variable `x : X`.

```
infix 200 _⟦X⟧
_⟦X⟧ : TermAut X → X → A ⟪ Σ ⟫ i
S ⟦X⟧ = λ x → S ⟦ var x ⟧
```

### Zero

```
sem-𝟘 :
    ∀ (S : TermAut X) →
    -------------------
    S ⟦ 0T ⟧ ≈[ i ] 𝟘

ν-≈ (sem-𝟘 S) = R-refl
δ-≈ (sem-𝟘 S) a = sem-𝟘 S
```

### Scalar multiplication

```
sem-· :
    ∀ (S : TermAut X) c p →
    -------------------------------
    S ⟦ c [·] p ⟧ ≈[ i ] c · S ⟦ p ⟧

ν-≈ (sem-· S c p) = R-refl
δ-≈ (sem-· S c p) a = sem-· S _ _
```

### Sum

```
sem-+ :
    ∀ (S : TermAut X) {α β} →
    ------------------------------------
    S ⟦ α [+] β ⟧ ≈[ i ] S ⟦ α ⟧ + S ⟦ β ⟧

ν-≈ (sem-+ S) = R-refl
δ-≈ (sem-+ S) _ = sem-+ S
```

### Products and the homomorphism lemma

We need to treat the case of products and the homomorphism lemma simultaneously.

```
mutual
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

The proof relies on `sem-substᵥ` (shown below)
stating the required relationship between the semantics and term substitution.

We finally state the homomorphism lemma.

```
    sem-hom :
        ∀ (S : TermAut X) (p : Term X) →
        --------------------------------
        S ⟦ p ⟧ ≈[ i ] ⟦ p ⟧ (S ⟦X⟧)
```

Its proof proceeds by structural induction on the structure of terms,
relying on the cases we have just proved.

```
    sem-hom S 0T = sem-𝟘 S

    sem-hom S (var x) = ≈-refl

    sem-hom S (c [·] p) =
        begin
            S ⟦ c [·] p ⟧
                ≈⟨ sem-· S c p ⟩
            c · S ⟦ p ⟧
                ≈⟨ R-refl ⟨ ·-cong ⟩ sem-hom S p ⟩
            c · ⟦ p ⟧ (S ⟦X⟧)
                ≈⟨⟩
            ⟦ c [·] p ⟧ (S ⟦X⟧)
        ∎ where open EqS

    sem-hom S (p [+] q) = 
        begin
            S ⟦ p [+] q ⟧
                ≈⟨ sem-+ S ⟩
            S ⟦ p ⟧ + S ⟦ q ⟧
                ≈⟨ sem-hom S p ⟨ +-cong ⟩ sem-hom S q ⟩
            ⟦ p ⟧ (S ⟦X⟧) + ⟦ q ⟧ (S ⟦X⟧)
                ≈⟨⟩
            ⟦ p [+] q ⟧ (S ⟦X⟧)
        ∎ where open EqS

    sem-hom S (p [*] q) =
        begin
            S ⟦ p [*] q ⟧
                ≈⟨ sem-* S ⟩
            S ⟦ p ⟧ * S ⟦ q ⟧
                ≈⟨ sem-hom S p ⟨ *-cong ⟩ sem-hom S q ⟩
            ⟦ p ⟧ (S ⟦X⟧) * ⟦ q ⟧ (S ⟦X⟧)
                ≈⟨⟩
            ⟦ p [*] q ⟧ (S ⟦X⟧)
        ∎ where open EqS
```

As a direct application of the homomorphism lemma,
we show how the semantics interacts with substitutions.

We are interested in the case of finitely many variables.

```
    sem-substᵥ :
        ∀ (S : TermAut X) (p : Term′ n) (qs : Substᵥ n X) →
        ---------------------------------------------------
        S ⟦ substᵥ qs p ⟧ ≈[ i ] ⟦ p ⟧ᵥ (map (S ⟦_⟧) qs)
    
    sem-substᵥ S p qs =
        begin
            S ⟦ substᵥ qs p ⟧
                ≈⟨ sem-hom S _ ⟩
            ⟦ subst (lookup qs) p ⟧ (S ⟦X⟧)
                ≈⟨ eval-substᵥ p {qs} ⟩
            ⟦ p ⟧ᵥ (map (λ q → ⟦ q ⟧ (S ⟦X⟧)) qs)
                ≈⟨ ⟦ p ⟧≈ᵥ map-cong _ _ qs (sem-hom S) ⟨
            ⟦ p ⟧ᵥ (map (λ q → S ⟦ q ⟧) qs)
        ∎ where open EqS
```

For completeness, we also consider the case of term automata
over an arbitrary set of variables `X`.

```
    sem-subst :
        ∀ (S : TermAut X) (p : Term X) (ϱ : Subst X X) →
        ------------------------------------------------
        S ⟦ subst ϱ p ⟧ ≈[ i ] ⟦ p ⟧ (S ⟦_⟧ ∘ ϱ)

    sem-subst S p ϱ =
        begin
            S ⟦ subst ϱ p ⟧
                ≈⟨ sem-hom S _ ⟩
            ⟦ subst ϱ p ⟧ (S ⟦X⟧)
                ≈⟨ eval-subst p ⟩
            ⟦ p ⟧ (λ x → ⟦ ϱ x ⟧ (S ⟦X⟧))
                ≈⟨ sem-cong p (sem-hom S ∘ ϱ) ⟨
            ⟦ p ⟧ (λ x → S ⟦ ϱ x ⟧)
        ∎ where open EqS
```

We immediately apply `sem-hom` in the next secion
to show equivalence between `P`-finite series and series recognised by `P`-automata over finitely many variables.

# Equivalence with finitely generated series {#sec:coincidence}

We show that the class of series recognized by term automata
coincides with the class of finitely generated series.

We remark that this holds for every product rule `P`.

```
open import General.FinitelyGenerated R Σ P
```

## From automata to series

We show that a `P`-automaton with `n` variables recognises only `P`-finite series (with `n` generators).

```
P-aut→P-fin :
    ∀ n (S : TermAut (Fin n)) α →
    -----------------------------------------
    P-fin (S ⟦ α ⟧) n
```

The proof proceeds to construct the required generators (from `S ⟦X⟧`).
The homomorphism lemma `sem-hom`is crucial for correctness.

```
P-aut→P-fin n S α = P-fin[ gs , S⟦α⟧∈[gs] α , cl ] where
```

Recall that `S ⟦X⟧ = λ x → S ⟦ var x ⟧` is the valuation
that maps each variable to its semantics.

```
    gs : Vec (A ⟪ Σ ⟫) n
    gs = tabulate (S ⟦X⟧)
```

The semantics of variables trivially belongs to the algebra they generate.

```
    S⟦var⟧∈gs : ∀ (i : Fin n) → S ⟦ var i ⟧ ∈[ gs ]
    S⟦var⟧∈gs i = gen∈ (∈-tabulate⁺ _ i)
```

The value of a term whose variables evaluate to the generators belong to the algebra they generate

```
    ⟦α⟧∈[gs] : ∀ α → ⟦ α ⟧ (S ⟦X⟧) ∈[ gs ]
    ⟦α⟧∈[gs] α = subalgebra α S⟦var⟧∈gs
```

We recall that the semantics is a homomorphism.

```
    S⟦α⟧≈⟦α⟧ : ∀ α → S ⟦ α ⟧ ≈ ⟦ α ⟧ (S ⟦X⟧)
    S⟦α⟧≈⟦α⟧ = sem-hom S
```

The semantics of every term belongs to the algebra generated by the semantics of variables.

```
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

## From series to automata

Conversely, we show that a `P`-finite series `f` (with `n` generators)
is recognised by a `P`-automaton (over `n` variables).
Correctness of the construction again relies on the homomorphism lemma `sem-hom`.

```
module P-fin→PolyAut {f} (Fin-f : P-fin f n) where
```

The automaton is over `n` variables,

```
    V = Var n
```

Let `gs` be the vector of generators witnessing that `f` is `P`-finite. 

```
    gs : Vec (A ⟪ Σ ⟫) n
    gs = gen Fin-f
```

Let `g i` be the `i`-th generator.

```
    -- the i-th generator
    g : V → A ⟪ Σ ⟫
    g i = lookup gs i
```

We need some additional definitions.

```
    -- the i-th generator is indeed a generator
    g∈gs : ∀ i → g i ∈ gs
    g∈gs i = ∈-lookup i gs

    xt : ∀ {f} → f ∈[ gs ] → ∃[ α ] f ≈ ⟦ α ⟧ (lookup gs)
    xt f∈[gs] = extract _ _ f∈[gs]

    -- given a series in the algebra, get the generating term
    xt-α : ∀ {f} → f ∈[ gs ] → Term′ n
    xt-α f∈[gs] = fst (xt f∈[gs])

    xt-f≈⟦α⟧ : ∀ {f} → (f∈[gs] : f ∈[ gs ]) → f ≈ ⟦ xt-α f∈[gs] ⟧ (lookup gs)
    xt-f≈⟦α⟧ f∈[gs] = snd (xt f∈[gs])

    δga∈[gs] : ∀ i a → δ (g i) a ∈[ gs ]
    δga∈[gs] i a = closed Fin-f a (g∈gs i)
```

For every generator index `i` and input symbol `a`,
let `α i a` be the term witnessing that the left derivative `δ (g i) a`
belongs to the algebra generated by `gs`.

```
    α : ∀ i a → Term′ n
    α i a = xt-α (δga∈[gs] i a)
```

```
    δga≈⟦α⟧ : ∀ i a → δ (g i) a ≈ ⟦ α i a ⟧ g
    δga≈⟦α⟧ i a = xt-f≈⟦α⟧ (δga∈[gs] i a)
```

We are now ready to construct the automaton.

The output function `F` simply maps each variable `i`
to the constant term of the corresponding generator `g i`.

The transition `Δ` function maps each variable `i` and input symbol `a`
to the term `α i a` defined above.

```
    S : TermAut V
    S = record {
            F = λ i → ν (g i);
            Δ = λ a i → α i a
        }
```

It remains to show that the construction is correct,
in the sense that the automaton recognises `f`.

It is necessary to show a more general property first.
First, we claim that from configuration `α`
the automaton recognises the series `⟦ α ⟧ g`.

```
    sound : ∀ α → S ⟦ α ⟧ ≈[ i ] ⟦ α ⟧ g
```

In order to establish this fact,
we need to show that from variable `x : V`,
the automaton recognises the corresponding generator `g x`.

```
    sound-var : ∀ x → S ⟦ var x ⟧ ≈[ i ] g x
```

We are now ready to show both properties.

```
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

    sound α = 
        begin
            S ⟦ α ⟧
                ≈⟨ sem-hom S _ ⟩
            ⟦ α ⟧ (S ⟦X⟧)
                ≈⟨ ⟦ α ⟧≈ sound-var ⟩
            ⟦ α ⟧ g
        ∎ where open EqS
```

```
    f∈[gs] : f ∈[ gs ]
    f∈[gs] = memb Fin-f
```

Let `β` be the term witnessing that `f` belongs to the algebra generated by `gs`.

```
    β : Term′ n
    β = xt-α f∈[gs]

    f≈⟦β⟧ : f ≈ ⟦ β ⟧ g
    f≈⟦β⟧ = snd (xt f∈[gs])
```

The proof of correctness is concluded by applying soundness to `β`.

```
    correctness : f ≈ S ⟦ β ⟧
    correctness =
        begin
            f
                ≈⟨ f≈⟦β⟧ ⟩
            ⟦ β ⟧ g
                ≈⟨ sound _ ⟨
            S ⟦ β ⟧
        ∎ where open EqS
```
