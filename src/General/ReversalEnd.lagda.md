---
title: Reversal endomorphisms
prev: /General/Reversal/
ignore: this extra field will help with the Make script ;p
---

Fix a product rule `P`.
In this section we provide a characterisation of when reversal is an endomorphism of the series algebra.
When this is the case, [we show](#sec:rev-end-right-derivatives-P-fin)
that `P`-finite series are closed under right derivatives.
We then discuss an [automata-based characterisation](#sec:automata).

The rest of the section is organised as follows.

- In !refSection(#sec:rev-product_rule) we show that reversal is an endomorphism
if and only if right derivatives satisfy the same product rule `P` as left derivatives do.

- In !refSection(#sec:unary-operators-product-rules) we show that if a unary operator `G` satisfies a product rule `Q`,
then we can extend the product rule to arbitrary terms.

- In !refSection(#sec:closure-under-right-derivatives) we show that if right derivatives satisfy *any* product rule (not necessarily `P`),
then `P`-finite series are closed under right derivatives.

- Finally, in !refSection(#sec:automata) we provide an automata-based characterisation of when reversal is an endomorphism.

```
{-# OPTIONS --guardedness --sized-types #-}

open import Preliminaries.Base renaming (_++_ to _++ᵥ_)
open import General.ProductRules

module General.ReversalEnd
    (R : CommutativeRing)
    (Σ : Set)
    (P : ProductRule R)
    where

open import Preliminaries.Algebra R
open import Preliminaries.Vector 

open import General.Terms R
    renaming (_+_ to _[+]_; _*_ to _[*]_; _·_ to _[·]_)
    
open import General.Series R Σ
open import General.Products R Σ
open import General.Reversal R Σ

open Product P
open Extensions P

private variable
    i : Size
    m n k ℓ : ℕ
    f g : A ⟪ Σ ⟫ i
    ϱ : Vec (A ⟪ Σ ⟫) k
    Q : ProductRule R
    G : A ⟪ Σ ⟫ → A ⟪ Σ ⟫
```

# Right derivatives, reversal, and product rules {#sec:rev-product_rule}

In this section we study the connection between

- reversal preserving the product operation, and
- right derivatives satisfying a product rule.

We introduce an abbreviation for the property that right derivatives satisfy an arbitrary product rule.

```
δʳ-satisfies_ : ProductRule R → Set
δʳ-satisfies Q = ∀ a → (δʳ a) satisfies Q
```

## Characterisation {#sec:rev-product_rule-characterisation}

The main result of this section is the following characterisation

```
rev-end↔δʳP : IsEndomorphism rev iff δʳ-satisfies P
```

We prove the two directions separately.

## From reversal to a product rule {#sec:rev-to-product_rule}

We show that if reversal is an endomorphism,
then the right derivatives satisfy the same product rule `P` as left derivatives do.

```
rev-end→δʳP : IsEndomorphism rev → δʳ-satisfies P
rev-end→δʳP end a f g =
    begin
        δʳ a (f * g)
            ≈⟨ δʳ-rev-rev _ _ ⟩
        rev (δˡ a (rev (f * g)))
            ≈⟨ rev-cong (δ-≈ (*-end end f g) a) ⟩
        rev (δˡ a (rev f * rev g))
            ≈⟨⟩
        rev ⟦ P ⟧⟨ rev f , δˡ a (rev f) , rev g , δˡ a (rev g) ⟩
            ≈⟨⟩
        rev ⟦ P ⟧⟨ rev f , rev (δʳ a f) , rev g , rev (δʳ a g) ⟩
            ≈⟨ endᵥ P (_ ∷ _ ∷ _ ∷ _ ∷ []) end ⟩
        ⟦ P ⟧⟨ rev (rev f) , rev (rev (δʳ a f)) , rev (rev g) , rev (rev (δʳ a g)) ⟩
            ≈⟨ ⟦ P ⟧≈ᵥ [ rev-rev _ , rev-rev _ , rev-rev _ , rev-rev _ ] ⟩
        ⟦ P ⟧⟨ f , δʳ a f , g , δʳ a g ⟩
    ∎ where open EqS
```

## From product rule to reversal {#sec:product_rule-to-rev}

Viceversa, if right derivatives satisfy the same product rule `P` as left derivatives do,
then reversal is an endomorphism.

```
δʳP→rev-end : δʳ-satisfies P → IsEndomorphism rev {i}
δʳP→rev-end p-rev = record {
    𝟘-end = rev-end-𝟘;
    ·-end = rev-end-·;
    +-end = rev-end-+;
    *-end = rev-end-*
    } where
```

The additional size parameter `i` is used to enable Agda to witness productivity.
Preservation of the vector space structure (`rev-end-𝟘`, `rev-end-·`, and `rev-end-+`) has been proved already.
It remains to show preservation of the product operation.
The proof proceeds by coinduction.

- The base case `ν (rev (f * g)) ≈R ν (rev f * rev g)` is immediate.

- The coinductive case `δˡ a (rev (f * g)) ≈ δˡ a (rev f * rev g)`
relies on the endomorphism lemma applied to the coinductive hypothesis.

```
    rev-end-* : Endomorphic-* rev
    ν-≈ (rev-end-* f g) = R-refl
    δ-≈ (rev-end-* f g) a =
        begin
            δˡ a (rev (f * g))
                ≈⟨⟩
            rev (δʳ a (f * g))
                ≈⟨ rev-cong (p-rev a f g) ⟩
            rev ⟦ P ⟧⟨ f , δʳ a f , g , δʳ a g ⟩
                ≈⟨ endᵥ P (_ ∷ _ ∷ _ ∷ _ ∷ []) (δʳP→rev-end p-rev)⟩
            ⟦ P ⟧⟨ rev f , rev (δʳ a f) , rev g , rev (δʳ a g) ⟩
                ≈⟨⟩
            ⟦ P ⟧⟨ rev f , δˡ a (rev f) , rev g , δˡ a (rev g) ⟩
                ≈⟨⟩
            δˡ a (rev f * rev g)
        ∎ where open EqS
```

The proof of `rev-end↔δʳP` is concluded by putting together the two directions above.

```
rev-end↔δʳP = rev-end→δʳP ,, δʳP→rev-end
```

# Unary operators satisfying a product rule {#sec:unary-operators-product-rules}

In this section we consider a general unary operator `G` on series
and we show that if `G` satisfies a product rule `Q`
(which does not need to be the same as `P`, the product rule satisfies by left derivatives),
then we can extend the product rule to arbitrary terms.

```
ext-lem :
    ∀ ϱ →
    G IsExt Q →
    (u : Term′ k) →
    -------------------------------------------
    ∃[ v ] G (⟦ u ⟧ᵥ ϱ) ≈ ⟦ v ⟧ᵥ (ϱ ++ᵥ map G ϱ)
```

In order to prove the lemma,
we will need to introduce some auxiliary notions.

## Primed variables

We begin by defining a facility to extend variables and terms.
If `x` is a variable belonging to a set of `k` variables,
then `x ′` is a (right) copy of `x` in a set of `ℓ + k` variables.

```
infix 10 _′
_′ : Var k → Var (ℓ +ℕ k)
_′ {ℓ = ℓ} x =  ℓ ↑ʳ x
```

The fundamental property of primed variables is the following.

```
prime-lemma₀ :
    ∀ (x : Var k) (ϱ : Vec (A ⟪ Σ ⟫) ℓ) η →
    ---------------------------------------
    ⟦ var x ⟧ᵥ η ≈ ⟦ var (x ′) ⟧ᵥ (ϱ ++ᵥ η)

prime-lemma₀ x [] η = ≈-refl
prime-lemma₀ x (_ ∷ ϱ) η = prime-lemma₀ x ϱ η
```

We will use the following specialisation of !ref(prime-lemma₀).

```
prime-lemma :
    ∀ (x : Var k) G ϱ →
    ------------------------------------------------
    G (⟦ var x ⟧ᵥ ϱ) ≈ ⟦ var (x ′) ⟧ᵥ (ϱ ++ᵥ map G ϱ)

prime-lemma x G ϱ =
    begin
        G (⟦ var x ⟧ᵥ ϱ)
            ≈⟨⟩
        G (lookup ϱ x)
            ≡⟨ lookup-map G ϱ x ⟨
        lookup (map G ϱ) x
            ≈⟨⟩
        ⟦ var x ⟧ᵥ map G ϱ
            ≈⟨ prime-lemma₀ x ϱ (map G ϱ) ⟩
        ⟦ var (x ′) ⟧ᵥ (ϱ ++ᵥ map G ϱ)
    ∎ where open EqS
```

## Extended terms

We allow variables to appear in larger sets of variables,
by keeping the same index but in a larger finite set.
Thus if `x` is a variable in a set of `k` variables,
then `′-var x` is the same variable in a set of `k + ℓ` variables. 

```
′-var : Var k → Var (k +ℕ ℓ)
′-var {ℓ = ℓ} x = x ↑ˡ ℓ
```

The following is the crucial property of !ref(′-var x).

```
′-var-lem :
    ∀ (x : Var k) ϱ (η : Vec (A ⟪ Σ ⟫) ℓ) →
    ------------------------------------------
    ⟦ var x ⟧ᵥ ϱ ≈ ⟦ var (′-var x) ⟧ᵥ (ϱ ++ᵥ η)

′-var-lem zero ϱ η =
    begin
        lookup ϱ zero
            ≡⟨ lookup-zero-++ ϱ η ⟩
        lookup (ϱ ++ᵥ η) zero
    ∎ where open EqS
    
′-var-lem (suc x) (_ ∷ ϱ) η = ′-var-lem x ϱ η
```

We extend the priming operation to all terms.

```
infix 30 ′_
′_ : Term′ k → Term′ (k +ℕ k)
′ 0T = 0T
′ (var x) = var (′-var x)
′ (c [·] u) = c [·] ′ u
′ (u [+] v) = ′ u [+] ′ v
′ (u [*] v) = ′ u [*] ′ v
```

The crucial property of the priming operation
is that the semantics of the extended term (in any environment extension)
equals the semantics of the original one.
The proof is by structural induction on terms, where the case for variables relies on !ref(′-var-lem).

```
′-lem :
    ∀ (u : Term′ k) ϱ η →
    ----------------------------
    ⟦ u ⟧ᵥ ϱ ≈ ⟦ ′ u ⟧ᵥ (ϱ ++ᵥ η)

′-lem 0T ϱ η = ≈-refl

′-lem (var x) ϱ η = ′-var-lem x ϱ η

′-lem (c [·] u) ϱ η
    with ′-lem u ϱ η
... | ass = R-refl ·≈ ass

′-lem (u [+] v) ϱ η
    with ′-lem u ϱ η | ′-lem v ϱ η
... | ass-u | ass-v = ass-u +≈ ass-v

′-lem (u [*] v) ϱ η
    with ′-lem u ϱ η | ′-lem v ϱ η
... | ass-u | ass-v = ass-u *≈ ass-v
```

## `Q`-extensions

We are finally ready to prove !ref(ext-lem).

```   
ext-lem ϱ isExt 0T = 0T ,, isExt .𝟘-ext

ext-lem ϱ isExt (var x) = var (x ′) ,, prime-lemma x _ ϱ

ext-lem {G = G} ϱ isExt (c [·] u)
    with ext-lem ϱ isExt u
... | u′ ,, ass = c [·] u′ ,, it where
    it =
        begin
            G (⟦ c [·] u ⟧ᵥ ϱ)
                ≈⟨⟩
            G (c · (⟦ u ⟧ᵥ ϱ))
                ≈⟨ isExt .·-ext _ _ ⟩
                c · G (⟦ u ⟧ᵥ ϱ)
                ≈⟨ R-refl ·≈ ass ⟩
            c · ⟦ u′ ⟧ᵥ (ϱ ++ᵥ map G ϱ)
                ≈⟨⟩
            ⟦ c [·] u′ ⟧ᵥ (ϱ ++ᵥ map G ϱ)
        ∎ where open EqS

ext-lem {G = G} ϱ isExt (u [+] v)
    with ext-lem ϱ isExt u | ext-lem ϱ isExt v
... | u′ ,, ass-u | v′ ,, ass-v = (u′ [+] v′) ,, it where

        it = begin
            G (⟦ u [+] v ⟧ᵥ ϱ)
                ≈⟨⟩
            G (⟦ u ⟧ᵥ ϱ + ⟦ v ⟧ᵥ ϱ)
                ≈⟨ isExt .+-ext _ _ ⟩
            G (⟦ u ⟧ᵥ ϱ) + G (⟦ v ⟧ᵥ ϱ)
                ≈⟨ ass-u +≈ ass-v ⟩
            ⟦ u′ ⟧ᵥ (ϱ ++ᵥ map G ϱ) + ⟦ v′ ⟧ᵥ (ϱ ++ᵥ map G ϱ)
                ≈⟨⟩
            ⟦ u′ [+] v′ ⟧ᵥ (ϱ ++ᵥ map G ϱ)
            ∎ where open EqS

ext-lem {G = G} {Q} ϱ isExt (u [*] v)
    with ext-lem ϱ isExt u | ext-lem ϱ isExt v
... | u′ ,, ass-u | v′ ,, ass-v
    = [ Q ]⟨ ′ u , u′ , ′ v , v′ ⟩ ,, it where

    η = ϱ ++ᵥ map G ϱ

    ext-u = ′-lem u ϱ (map G ϱ)
    ext-v = ′-lem v ϱ (map G ϱ)

    it = begin
        G (⟦ u [*] v ⟧ᵥ ϱ)
            ≈⟨⟩
        G (⟦ u ⟧ᵥ ϱ * ⟦ v ⟧ᵥ ϱ)
            ≈⟨ isExt .*-ext _ _ ⟩
        ⟦ Q ⟧⟨ ⟦ u ⟧ᵥ ϱ , G (⟦ u ⟧ᵥ ϱ) , ⟦ v ⟧ᵥ ϱ , G (⟦ v ⟧ᵥ ϱ) ⟩
            ≈⟨ ⟦ Q ⟧≈ᵥ [ ext-u , ass-u , ext-v , ass-v ] ⟩
        ⟦ Q ⟧⟨ ⟦ ′ u ⟧ᵥ η , ⟦ u′ ⟧ᵥ η , ⟦ ′ v ⟧ᵥ η , ⟦ v′ ⟧ᵥ η ⟩
            ≈⟨ eval-substᵥ Q {_ ∷ _ ∷ _ ∷ _ ∷ []} ⟨
        ⟦ [ Q ]⟨ ′ u , u′ , ′ v , v′ ⟩ ⟧ᵥ η
        ∎ where open EqS
```

# Closure under right derivatives {#sec:closure-under-right-derivatives}

We show that if right derivatives satisfy *any* product rule (not necessarily `P`),
then `P`-finite series are closed under right derivatives.

In particular, by !ref(rev-end↔δʳP) in the [previous section](#sec:rev-to-product_rule)
this is the case when reversal is an endomorphism.

```
open import Data.Product.Base using (∃; ∃-syntax; _,_)
open import Data.Product using (_×_)
open import Preliminaries.Vector
open import General.FinitelyGenerated R Σ P
```

## General case

We begin with a general lemma, showing that if `G` is a `Q`-extension
and `f` is generated by `ϱ`,
then `G f` is generated by the same set together with their images under `G `.

```
G-closed :
    G IsExt Q →
    f ∈[ ϱ ] →
    ----------------------
    G f ∈[ ϱ ++ᵥ map G ϱ ]
```

The proof uses !ref(ext-lem) from the [previous section](#sec:unary-operators-product-rules).

```
G-closed {G = G} {Q = Q} {f = f} {ϱ = ϱ} isExt f∈[ϱ] = step₁ where

    ϱ′ = map G ϱ
    ϱ′′ = ϱ ++ᵥ ϱ′

    -- witnessing term of f ∈[ ϱ ]
    α-all = extract _ _ f∈[ϱ]

    α : Term′ _
    α = fst α-all

    α-sound : f ≈ ⟦ α ⟧ᵥ ϱ
    α-sound = snd α-all

    β-all = ext-lem ϱ isExt α

    β : Term′ _
    β = fst β-all

    β-sound : G (⟦ α ⟧ᵥ ϱ) ≈ ⟦ β ⟧ᵥ ϱ′′
    β-sound = snd β-all

    αβ-sound : G f ≈ ⟦ β ⟧ᵥ ϱ′′
    αβ-sound =
        begin
            G f
                ≈⟨ isExt .≈-ext α-sound ⟩
            G (⟦ α ⟧ᵥ ϱ)
                ≈⟨ β-sound ⟩
            ⟦ β ⟧ᵥ ϱ′′
        ∎ where open EqS

    step₀ : ⟦ β ⟧ᵥ ϱ′′ ∈[ ϱ′′ ]
    step₀ = subalgebraᵥ β

    step₁ :  G f ∈[ ϱ′′ ]
    step₁ = αβ-sound ≈∈ step₀
```

## Right derivatives {#sec:closure-right-derivatives}

We apply !ref(G-closed) to show closure under right derivatives,
whenever they satisfy *any* product rule `Q` (not necessarily `P`).

```
δʳ-closed :
    ∀ Q b →
    δʳ-satisfies Q →
    f ∈[ ϱ ] →
    ------------------------------
    δʳ b f ∈[ ϱ ++ᵥ map (δʳ b) ϱ ]
```

The proof is just an application of !ref(G-closed) with `G = δʳ b`.

```
δʳ-closed Q b δʳ-sat f∈[ϱ] = G-closed xt f∈[ϱ] where

    xt : (δʳ b) IsExt Q
    xt = record {
        ≈-ext = δʳ-inv b ;
        𝟘-ext = δʳ-end-𝟘 b ; 
        ·-ext = δʳ-end-· b ; 
        +-ext = δʳ-end-+ b ; 
        *-ext = δʳ-sat b }
```

## `P`-finiteness {#sec:right-derivatives-P-fin}

Consequently, `P`-finite series are closed under right derivatives,
whenever the latter satisfy any product rule `Q`.
For instance, this is the case when reversal is an endomorphism.
This relies on the fact that left and right derivatives commute.

```
P-fin-δʳ :
    ∀ Q →
    δʳ-satisfies Q →
    P-fin f k →
    ∀ b →
    -----------------------
    P-fin (δʳ b f) (k +ℕ k)
```

The proof proceeds as follows.
Let `fs` be the generators for `f`, and let `gs` be their right derivative.
Then the right derivative of `f` is generated by `fs ++ᵥ gs`.

```
P-fin-δʳ {f = f} {k = k} Q p-δʳ G b =
    P-fin[ fs ++ᵥ gs , lem1 , lem2 ]
    where

    fs gs : Vec (A ⟪ Σ ⟫) k
    fs = gen G
    gs = map (δʳ b) fs

    lem1 : δʳ b f ∈[ fs ++ᵥ gs ]
    lem1 = δʳ-closed Q b p-δʳ (memb G)

    -- g ∈ gs means that g is of the form δʳ b h for some h ∈ fs
    wit : g ∈ gs → ∃[ h ] h ∈ fs × g ≡ δʳ b h
    wit g∈gs = ∈-map⁻ g∈gs

    -- closure under left derivatives of generators
    lem2 : ∀ a {g} → g ∈ fs ++ᵥ gs → δ g a ∈[ fs ++ᵥ gs ]
    lem2 a {g} g∈ with ∈ᵥ-++ {as = fs} g∈
    ... | inj₁ g∈fs = ++-∈ˡ (closed G a g∈fs)
    ... | inj₂ g∈gs = δga∈[fs++gs] where

        h : A ⟪ Σ ⟫
        h = fst (wit g∈gs)

        h∈fs : h ∈ fs
        h∈fs = fst (snd (wit g∈gs))

        g≡δʳbh : g ≡ δʳ b h
        g≡δʳbh = snd (snd (wit g∈gs))

        -- left and right derivatives commute
        δˡg≈δʳδˡh : δ g a ≈ δʳ b (δ h a)
        δˡg≈δʳδˡh =
            begin
                δ g a
                    ≡⟨ cong (\ f → δ f a) g≡δʳbh ⟩
                δ (δʳ b h) a
                    ≈⟨⟩
                δʳ b (δ h a)
            ∎ where open EqS

        δˡh∈[fs] : δ h a ∈[ fs ]
        δˡh∈[fs] = closed G a h∈fs

        δʳδˡh∈[fs++gs] : δʳ b (δ h a) ∈[ fs ++ᵥ gs ]
        δʳδˡh∈[fs++gs] = δʳ-closed Q b p-δʳ δˡh∈[fs]

        δga∈[fs++gs] : δ g a ∈[ fs ++ᵥ gs ]
        δga∈[fs++gs] = δˡg≈δʳδˡh ≈∈ δʳδˡh∈[fs++gs]
```

## Putting it all together {#sec:rev-end-right-derivatives-P-fin}

By combining all the results above,
we have that if reversal is an endomorphism,
then `P`-finite series are closed under right derivatives.

Formally, we have the following

```
rev-end→P-fin :
    IsEndomorphism rev →
    P-fin f k →
    ∀ b →
    -----------------------
    P-fin (δʳ b f) (k +ℕ k)

rev-end→P-fin rev-end f-P-fin b =
    P-fin-δʳ P (rev-end→δʳP rev-end) f-P-fin b
```

# Automaton-based characterisation {#sec:automata}

In this section we characterise when reversal is an endomorphism with `P`-automata.
This syntactic characterisation will be used [later](../../Special/Reversal)
to show that reversal is an endomorphism for every special product rule.

```
open Inductive renaming (_++ℓ_ to _++_)
open import General.Automata R Σ P
```

## Automaton for left and right derivatives

```
infix 8 _x[_]_
data *X* : Set where
    _x[_]_ : (u : Σ *) (f : A ⟪ Σ ⟫) (v : Σ *) → *X*


Δˡ Δʳ : (a : Σ) → *X* → Term *X*
Δˡ a (u x[ f ] v) = var ((u ∷ʳ a) x[ f ] v)
Δʳ b (u x[ f ] v) = var (u x[ f ] (v ∷ʳ b))

S : TermAut *X*
F S (u x[ f ] v) = f ⟨ u ++ reverse v ⟩
Δ S = Δˡ
```

## Properties of the automaton {#sec:automaton:properties}

```
var-lemma-coeff :
    ∀ u f v w →
    --------------------------------------------------------
    S ⟦ var (u x[ f ] v) ⟧ ⟨ w ⟩ ≡ f ⟨ u ++ w ++ reverse v ⟩

var-lemma-coeff u f v ε = refl
var-lemma-coeff u f v (a ∷ w) =
    begin
        S ⟦ var (u x[ f ] v) ⟧ ⟨ a ∷ w ⟩
            ≡⟨⟩            
        δ (S ⟦ var (u x[ f ] v) ⟧) a ⟨ w ⟩
            ≡⟨⟩
        S ⟦ var ((u ∷ʳ a) x[ f ] v) ⟧ ⟨ w ⟩
            ≡⟨ var-lemma-coeff _ _ _ w ⟩
        f ⟨ (u ∷ʳ a) ++ w ++ reverse v ⟩
            ≡⟨ cong (λ w → f ⟨ w ⟩) (∷ʳ-++-++ u a w (reverse v)) ⟩
        f ⟨ u ++ a ∷ w ++ reverse v ⟩
    ∎ where open ≡-Eq
```

The construction of the automaton `S` is meant to satisfy the following property.

```
var-lemma : ∀ u f v →
    ----------------------------------------
    S ⟦ var (u x[ f ] v) ⟧ ≈ δˡ* u (δʳ* v f)

var-lemma u f v = series-ext λ w → EqR.≡→≈ (helper w) where

    helper : ∀ w → S ⟦ var (u x[ f ] v) ⟧ ⟨ w ⟩ ≡ δˡ* u (δʳ* v f) ⟨ w ⟩
    helper w =
        begin
            S ⟦ var (u x[ f ] v) ⟧ ⟨ w ⟩ ≡⟨ var-lemma-coeff u f v w ⟩
            f ⟨ u ++ w ++ reverse v ⟩ ≡⟨ coeff-δˡ*-δʳ* u v f w ⟨
            δˡ* u (δʳ* v f) ⟨ w ⟩
        ∎ where open ≡-Eq
```

We will use the following special case of !ref(var-lemma).

```
var-lemma-simple : ∀ f → S ⟦ var (ε x[ f ] ε) ⟧ ≈ f
var-lemma-simple f = var-lemma ε f ε
```        

## Equivalent conditions

We introduce two additional conditions and we show their equivalence to !ref(δʳ-satisfies P).

The first condition relates right derivatives and `Δʳ`.
The additional size parameter is used to enable Agda to witness productivity.

```
δʳΔʳ : Set
δʳΔʳ = ∀ {i} b α → δʳ b (S ⟦ α ⟧) ≈[ i ] S ⟦ Δʳ b ↑ α ⟧
```

The second condition states that the semantics of the automaton
is invariant under swapping `Δʳ` and `Δˡ`.

```
⟦ΔʳΔˡ⟧ : Set
⟦ΔʳΔˡ⟧ = ∀ a b α → S ⟦ Δʳ b ↑ (Δˡ a ↑ α) ⟧ ≈ S ⟦ Δˡ a ↑ (Δʳ b ↑ α) ⟧
```

We now show the following equivalences.

```
automata-char-lemma : IsEndomorphism rev iff δʳΔʳ × δʳΔʳ iff ⟦ΔʳΔˡ⟧
```

### First equivalence {#sec:product_rule-equivalence-1}

We begin with the first half of !ref(automata-char-lemma).
We show that !ref(δʳΔʳ) is equivalent to !ref(δʳ-satisfies P),
and then use  !ref(rev-end↔δʳP) to conclude.

We prove two implications.

```
δʳP→δʳΔʳ : δʳ-satisfies P → δʳΔʳ

δʳP→δʳΔʳ ass b 0T =
    begin
        δʳ b (S ⟦ 0T ⟧)
            ≈⟨ δʳ-cong b (sem-𝟘 S) ⟩
        δʳ b 𝟘
            ≈⟨ δʳ-end-𝟘 b ⟩
        𝟘
            ≈⟨ sem-𝟘 S ⟨
        S ⟦ 0T ⟧
    ∎ where open EqS
    
δʳP→δʳΔʳ ass b (c [·] p) =
    begin
        δʳ b (S ⟦ c [·] p ⟧)
            ≈⟨ δʳ-cong b (sem-· S c p) ⟩
        δʳ b (c · S ⟦ p ⟧)
            ≈⟨ δʳ-end-· _ _ _ ⟩
        c · δʳ b (S ⟦ p ⟧)
            ≈⟨ R-refl ⟨ ·-cong ⟩ δʳP→δʳΔʳ ass b p ⟩
        c · S ⟦ Δʳ b ↑ p ⟧
            ≈⟨ sem-· S _ _ ⟨
        S ⟦ c [·] Δʳ b ↑ p ⟧
            ≈⟨⟩
        S ⟦ Δʳ b ↑ (c [·] p) ⟧
    ∎ where open EqS

δʳP→δʳΔʳ ass b (var (u x[ f ] v)) =
    begin
        δʳ b (S ⟦ var (u x[ f ] v) ⟧)
            ≈⟨ δʳ-cong b (var-lemma u f v) ⟩
        δʳ b (δˡ* u (δʳ* v f))
            ≈⟨ δʳ-δˡ* _ b u ⟩
        δˡ* u (δʳ b (δʳ* v f))
            ≡⟨ cong (δˡ* u) (δʳ-δʳ* b v f) ⟩
        δˡ* u (δʳ* (v ∷ʳ b) f)
            ≈⟨ ≈-sym (var-lemma _ _ _) ⟩
        S ⟦ var (u x[ f ] (v ∷ʳ b)) ⟧
            ≈⟨⟩
        S ⟦ Δʳ b ↑ var (u x[ f ] v) ⟧
    ∎ where open EqS

δʳP→δʳΔʳ ass b (α [+] β) =
    begin
        δʳ b (S ⟦ α [+] β ⟧)
            ≈⟨ δʳ-cong b (sem-+ S) ⟩
        δʳ b (S ⟦ α ⟧ + S ⟦ β ⟧)
            ≈⟨ δʳ-end-+ _ _ _ ⟩
        δʳ b (S ⟦ α ⟧) + δʳ b (S ⟦ β ⟧)
            ≈⟨ δʳP→δʳΔʳ ass _ _ ⟨ +-cong ⟩ δʳP→δʳΔʳ ass _ _ ⟩
        S ⟦ Δʳ b ↑ α ⟧ + S ⟦ Δʳ b ↑ β ⟧
            ≈⟨ sem-+ S ⟨
        S ⟦ Δʳ b ↑ (α [+] β) ⟧
    ∎ where open EqS

δʳP→δʳΔʳ ass b (α [*] β) with δʳP→δʳΔʳ ass b α | δʳP→δʳΔʳ ass b β
... | ass-α | ass-β =
    begin
        δʳ b (S ⟦ α [*] β ⟧)
            ≈⟨ δʳ-cong b (sem-* S) ⟩
        δʳ b (S ⟦ α ⟧ * S ⟦ β ⟧)
            ≈⟨ ass _ _ _ ⟩
        ⟦ P ⟧⟨ S ⟦ α ⟧ , δʳ b (S ⟦ α ⟧) , S ⟦ β ⟧ , δʳ b (S ⟦ β ⟧) ⟩
            ≈⟨ ⟦ P ⟧≈ᵥ [_,_,_,_] ≈-refl ass-α ≈-refl ass-β ⟩ 
        ⟦ P ⟧⟨ S ⟦ α ⟧ , S ⟦ Δʳ b ↑ α ⟧ , S ⟦ β ⟧ , S ⟦ Δʳ b ↑ β ⟧ ⟩
            ≈⟨ sem-substᵥ S P (_ ∷ _ ∷ _ ∷ _ ∷ []) ⟨
        S ⟦ [ P ]⟨ α , Δʳ b ↑ α , β , Δʳ b ↑ β ⟩ ⟧
            ≈⟨⟩
        S ⟦ Δʳ b ↑ (α [*] β) ⟧
    ∎ where open EqS
```

We now prove the other direction.

```
δʳΔʳ→δʳP : δʳΔʳ → δʳ-satisfies P
δʳΔʳ→δʳP ass b f g =
    let x = var (ε x[ f ] ε); y = var (ε x[ g ] ε) in
    begin
        δʳ b (f * g)
            ≈⟨ δʳ-cong b (var-lemma-simple f ⟨ *-cong ⟩ var-lemma-simple g) ⟨
        δʳ b (S ⟦ x ⟧ * S ⟦ y ⟧)
            ≈⟨ δʳ-cong b (sem-hom S _) ⟨
        δʳ b (S ⟦ x [*] y ⟧)
            ≈⟨ ass _ _ ⟩
        S ⟦ Δʳ b ↑ (x [*] y) ⟧
            ≈⟨⟩
        S ⟦ [ P ]⟨ x , Δʳ b ↑ x , y , Δʳ b ↑ y ⟩ ⟧
            ≈⟨ sem-substᵥ S P (_ ∷ _ ∷ _ ∷ _ ∷ []) ⟩
        ⟦ P ⟧⟨ S ⟦ x ⟧ , S ⟦ Δʳ b ↑ x ⟧ , S ⟦ y ⟧ , S ⟦ Δʳ b ↑ y ⟧ ⟩
            ≈⟨ ⟦ P ⟧≈ᵥ [_,_,_,_] (≈-refl) (ass _ _) (≈-refl) (ass _ _) ⟨
        ⟦ P ⟧⟨ S ⟦ x ⟧ , δʳ b (S ⟦ x ⟧) , S ⟦ y ⟧ , δʳ b (S ⟦ y ⟧) ⟩
            ≈⟨ ⟦ P ⟧≈ᵥ [_,_,_,_]
                (var-lemma-simple _) (δʳ-cong b ((var-lemma-simple _)))
                (var-lemma-simple _) (δʳ-cong b ((var-lemma-simple _))) ⟩
        ⟦ P ⟧⟨ f , δʳ b f , g , δʳ b g ⟩
    ∎ where open EqS 
```

### Second equivalence {#sec:product_rule-equivalence-2}

We show that condition !ref(δʳΔʳ) implies !ref(⟦ΔʳΔˡ⟧).
This is very easy, since left and right derivatives commute.

```
δʳΔʳ→⟦ΔʳΔˡ⟧ : δʳΔʳ → ⟦ΔʳΔˡ⟧
δʳΔʳ→⟦ΔʳΔˡ⟧ ass a b α =
    begin
        S ⟦ Δʳ b ↑ (Δˡ a ↑ α) ⟧ ≈⟨ ass _ _ ⟨
        δʳ b (S ⟦ Δˡ a ↑ α ⟧) ≈⟨⟩
        δʳ b (δˡ a (S ⟦ α ⟧)) ≈⟨⟩
        δˡ a (δʳ b (S ⟦ α ⟧)) ≈⟨ δ-≈ (ass _ α) a ⟩
        δˡ a (S ⟦ Δʳ b ↑ α ⟧) ≈⟨⟩
        S ⟦ Δˡ a ↑ (Δʳ b ↑ α) ⟧
    ∎ where open EqS
```

### Third equivalence {#sec:product_rule-equivalence-3}

We show the converse to !ref(δʳΔʳ→⟦ΔʳΔˡ⟧) above.

```
open Semantics renaming (⟦_⟧_ to T⟦_⟧_; ⟦_⟧⟨_,_,_,_⟩ to T⟦_⟧⟨_,_,_,_⟩)

δʳΔʳ-ν-var :
    ∀ b u f v →
    --------------------------------------------------------------------
    ν (δʳ b (S ⟦ var (u x[ f ] v) ⟧)) ≡ ν (S ⟦ Δʳ b ↑ var (u x[ f ] v) ⟧)

δʳΔʳ-ν-var b u f v =
    begin
        ν (δʳ b (S ⟦ var (u x[ f ] v) ⟧)) ≡⟨⟩
        ν (δˡ b (S ⟦ var (u x[ f ] v) ⟧)) ≡⟨⟩
        ν (S ⟦ Δˡ b ↑ var (u x[ f ] v) ⟧) ≡⟨⟩
        ν (S ⟦ var ((u ∷ʳ b) x[ f ] v) ⟧) ≡⟨⟩
        f ⟨ (u ∷ʳ b) ++ reverse v ⟩ ≡⟨ (cong (λ x → f ⟨ x ⟩) $ reverse-∷ʳ-++ u v b) ⟩
        f ⟨ u ++ reverse (v ∷ʳ b) ⟩ ≡⟨⟩
        ν (S ⟦ var (u x[ f ] (v ∷ʳ b)) ⟧) ≡⟨⟩
        ν (S ⟦ Δʳ b ↑ var (u x[ f ] v) ⟧)
    ∎ where open ≡-Eq
```

```
δʳΔʳ-ν :
    ∀ b α →
    ---------------------------------------
    ν (δʳ b (S ⟦ α ⟧)) ≈R ν (S ⟦ Δʳ b ↑ α ⟧)

δʳΔʳ-ν b 0T = R-refl

δʳΔʳ-ν b (var (u x[ f ] v)) = EqR.≡→≈ (δʳΔʳ-ν-var b u f v)

δʳΔʳ-ν b (c [·] α) =
    begin
        ν (δʳ b (S ⟦ c [·] α ⟧))
            ≈⟨⟩
        ν (δˡ b (S ⟦ c [·] α ⟧))
            ≈⟨⟩
        ν (S ⟦ Δˡ b ↑ (c [·] α) ⟧)
            ≈⟨⟩
        ν (S ⟦ c [·] Δˡ b ↑ α ⟧)
            ≈⟨ (ν-≈ $ sem-· S c (Δˡ b ↑ α)) ⟩
        ν (c · S ⟦ Δˡ b ↑ α ⟧)
            ≈⟨⟩
        ν (c · δˡ b (S ⟦ α ⟧))
            ≈⟨⟩
        c *R ν (δˡ b (S ⟦ α ⟧))
            ≈⟨⟩
        c *R ν (δʳ b (S ⟦ α ⟧))
            ≈⟨ R-refl ⟨ *R-cong ⟩ δʳΔʳ-ν b α ⟩
        c *R ν (S ⟦ Δʳ b ↑ α ⟧)
            ≈⟨⟩
        ν (c · S ⟦ Δʳ b ↑ α ⟧)
            ≈⟨⟩
        ν (S ⟦ c [·] Δʳ b ↑ α ⟧)
            ≈⟨⟩
        ν (S ⟦ Δʳ b ↑ (c [·] α) ⟧)
    ∎ where open EqR

δʳΔʳ-ν b (α [+] β) =
    begin
        ν (δʳ b (S ⟦ α [+] β ⟧)) ≈⟨ ν-≈ (δʳ-cong b (sem-+ S {α} {β})) ⟩ 
        ν (δʳ b (S ⟦ α ⟧ + S ⟦ β ⟧)) ≈⟨⟩ 
        ν (δʳ b (S ⟦ α ⟧) + δʳ b (S ⟦ β ⟧)) ≈⟨⟩ 
        ν (δʳ b (S ⟦ α ⟧)) +R ν (δʳ b (S ⟦ β ⟧)) ≈⟨ δʳΔʳ-ν b α ⟨ +R-cong ⟩ δʳΔʳ-ν b β ⟩
        ν (S ⟦ Δʳ b ↑ α ⟧) +R ν (S ⟦ Δʳ b ↑ β ⟧) ≈⟨⟩ 
        ν (S ⟦ Δʳ b ↑ α ⟧ + S ⟦ Δʳ b ↑ β ⟧) ≈⟨ ν-≈ (sem-+ S {Δʳ b ↑ α} {Δʳ b ↑ β}) ⟩
        ν (S ⟦ Δʳ b ↑ α [+] Δʳ b ↑ β ⟧) ≈⟨⟩ 
        ν (S ⟦ Δʳ b ↑ (α [+] β) ⟧)
    ∎ where open EqR

δʳΔʳ-ν b (α [*] β) =
    let ϱˡ = α ∷ Δˡ b ↑ α ∷ β ∷ Δˡ b ↑ β ∷ []
        ϱʳ = α ∷ Δʳ b ↑ α ∷ β ∷ Δʳ b ↑ β ∷ [] in
    begin
        ν (δʳ b (S ⟦ α [*] β ⟧)) ≈⟨⟩
        ν (δˡ b (S ⟦ α [*] β ⟧)) ≈⟨⟩  -- !
        ν (S ⟦ Δˡ b ↑ (α [*] β) ⟧) ≈⟨⟩
        ν (S ⟦ [ P ]⟨ α , Δˡ b ↑ α , β , Δˡ b ↑ β ⟩ ⟧) ≈⟨ ν-≈ (sem-substᵥ S P ϱˡ) ⟩
        ν (⟦ P ⟧⟨ S ⟦ α ⟧ , S ⟦ Δˡ b ↑ α ⟧ , S ⟦ β ⟧ , S ⟦ Δˡ b ↑ β ⟧ ⟩)
            ≈⟨ ν-homᵥ P (_ ∷ _ ∷ _ ∷ _) ⟩
        T⟦ P ⟧⟨ ν (S ⟦ α ⟧) , ν (S ⟦ Δˡ b ↑ α ⟧) , ν (S ⟦ β ⟧) , ν (S ⟦ Δˡ b ↑ β ⟧) ⟩
            ≈⟨⟩
        T⟦ P ⟧⟨ ν (S ⟦ α ⟧) , ν (δˡ b (S ⟦ α ⟧)) , ν (S ⟦ β ⟧) , ν (δˡ b (S ⟦ β ⟧)) ⟩
            ≈⟨⟩
        T⟦ P ⟧⟨ ν (S ⟦ α ⟧) , ν (δʳ b (S ⟦ α ⟧)) , ν (S ⟦ β ⟧) , ν (δʳ b (S ⟦ β ⟧)) ⟩
            ≈⟨ ⟦ P ⟧≈⟨ R-refl , δʳΔʳ-ν b α , R-refl , δʳΔʳ-ν b β ⟩ ⟩ -- induction
        T⟦ P ⟧⟨ ν (S ⟦ α ⟧) , ν (S ⟦ Δʳ b ↑ α ⟧) , ν (S ⟦ β ⟧) , ν (S ⟦ Δʳ b ↑ β ⟧) ⟩
            ≈⟨ ν-homᵥ P (_ ∷ _ ∷ _ ∷ _) ⟨
        ν (⟦ P ⟧⟨ S ⟦ α ⟧ , S ⟦ Δʳ b ↑ α ⟧ , S ⟦ β ⟧ , S ⟦ Δʳ b ↑ β ⟧ ⟩) ≈⟨ ν-≈ (sem-substᵥ S P ϱʳ) ⟨
        ν (S ⟦ [ P ]⟨ α , Δʳ b ↑ α , β , Δʳ b ↑ β ⟩ ⟧) ≈⟨⟩
        ν (S ⟦ Δʳ b ↑ (α [*] β) ⟧)
    ∎ where open EqR
```

We can finally show that `⟦ΔʳΔˡ⟧` implies `δʳΔʳ`.

```
⟦ΔʳΔˡ⟧→δʳΔʳ : ⟦ΔʳΔˡ⟧ → δʳΔʳ
ν-≈ (⟦ΔʳΔˡ⟧→δʳΔʳ _ b α) = δʳΔʳ-ν b α
δ-≈ (⟦ΔʳΔˡ⟧→δʳΔʳ ass b α) a =
    begin
        δˡ a (δʳ b (S ⟦ α ⟧)) ≈⟨⟩
        δʳ b (δˡ a (S ⟦ α ⟧)) ≈⟨⟩
        δʳ b (S ⟦ Δˡ a ↑ α ⟧) ≈⟨ ⟦ΔʳΔˡ⟧→δʳΔʳ ass b (Δˡ a ↑ α) ⟩
        S ⟦ Δʳ b ↑ (Δˡ a ↑ α) ⟧ ≈⟨ ass a b α ⟩
        S ⟦ Δˡ a ↑ (Δʳ b ↑ α) ⟧ ≈⟨⟩
        δˡ a (S ⟦ Δʳ b ↑ α ⟧)
    ∎ where open EqS
```

We can finally prove !ref(automata-char-lemma).

```
automata-char-lemma = (δʳP→δʳΔʳ ∘ rev-end→δʳP , δʳP→rev-end ∘ δʳΔʳ→δʳP) , (δʳΔʳ→⟦ΔʳΔˡ⟧ , ⟦ΔʳΔˡ⟧→δʳΔʳ)
```

For later reference, we extract the following corollary.

```
⟦ΔʳΔˡ⟧→rev-end : ⟦ΔʳΔˡ⟧ → IsEndomorphism rev
⟦ΔʳΔˡ⟧→rev-end = δʳP→rev-end ∘ δʳΔʳ→δʳP ∘ ⟦ΔʳΔˡ⟧→δʳΔʳ
```
