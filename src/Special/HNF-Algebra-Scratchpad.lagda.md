---
title: Completeness of equivalence algorithm
---

```
{-# OPTIONS --guardedness --sized-types #-}
{-# OPTIONS --allow-unsolved-metas #-}

open import Preliminaries.Base
import Preliminaries.Algebra

module Special.HNF-Algebra-Scratchpad
    (R : CommutativeRing)
    (1≉0 : let open Preliminaries.Algebra R in ¬ (1R ≈R 0R))
    (no-zero-divisors : let open Preliminaries.Algebra R in
        ∀ {a b} → a *R b ≈R 0R → a ≈R 0R ⊎ b ≈R 0R)
    (_≟R_ : let open Preliminaries.Algebra R in Decidable _≈R_)
    where

open Preliminaries.Algebra R
open import General.Terms R hiding (x)
open import Special.Polynomials R
open import Special.HNF R
open import Special.DecidableEquivalence R _≟R_
open import Special.AuxiliaryLemmas R
open import Special.HNF-Normalised R 1≉0 _≟R_

open import Special.HNF-Algebra R 1≉0 no-zero-divisors _≟R_

private variable
    k : ℕ
```

```

*H-zeroʳ :
    (p : HNF (suc k)) →
    -------------------
    p *H 0H ≈H 0H

*H-zeroʳ ∅ = ≈H-refl
*H-zeroʳ (_ *x+ _ ·x+ _) = ∅

_*x+H_ : HNF (suc k) → HNF (suc k) → HNF (suc k)
∅ *x+H q = q
p *x+H ∅ = p *x+ 0R ·x+HN 0N
p *x+H (q *x+ c ·x+ m) = {!   !}

-- *x+·x+HN-*H :
--     (p : HNF (suc k)) →
--     (c : A) →
--     (m : Normal k) →
--     (q : HNF (suc k)) →
--     ----------------------------------------------------------
--     (p *x+ c ·x+HN m) *H q ≈H (p *H q +H c ·H q) *x+H (m *NH q)

-- *x+·x+HN-*H p c m q = {!   !}

+H-*x+H-+H :
    (p q r s : HNF (suc k)) →
    --------------------------------------------------
    (p +H q) *x+H (r +H s) ≈H (p *x+H r) +H (q *x+H s)

+H-*x+H-+H p q r s = {!   !}

*H-*x+·x+-distribˡ :
    (p q : HNF (suc k)) →
    (c : A) →
    (m : Normal k) →
    ---------------------------------------------------------
    p *H (q *x+ c ·x+ m) ≈H (p *H q +H c ·H p) *x+H (p *HN m)

*H-*x+·x+-distribˡ p q c m = {!   !}   

mutual

    HN-distribʳ :
        (p q : HNF (suc k)) →
        (m : Normal k) →
        ------------------------------------
        (p +H q) *HN m ≈H p *HN m +H q *HN m

    HN-distribʳ p q m = {!   !}

    H-distribʳ :
        (p q r : HNF (suc k)) →
        -------------------------------------
        (p +H q) *H r ≈H (p *H r) +H (q *H r)

    H-distribʳ p q ∅ =
        begin
            (p +H q) *H 0H ≈⟨ *H-zeroʳ (p +H q) ⟩
            0H ≈⟨ ∅ ⟨
            0H +H 0H ≈⟨ (*H-zeroʳ p ⟨ +H-cong ⟩ *H-zeroʳ q) ⟨
            (p *H 0H) +H (q *H 0H)
        ∎ where open EqH

    H-distribʳ p q (r *x+ c ·x+ m) =
        begin
            (p +H q) *H (r *x+ c ·x+ m)
                ≈⟨ {!   !} ⟩
            ((p +H q) *H r +H c ·H (p +H q)) *x+H ((p +H q) *HN m)
                ≈⟨ {!   !} ⟩
            ((p *H r +H q *H r) +H (c ·H p +H c ·H q)) *x+H (p *HN m +H q *HN m)
                ≈⟨ {!   !} ⟩
            ((p *H r +H c ·H p) +H (q *H r +H c ·H q)) *x+H (p *HN m +H q *HN m)
                ≈⟨ {!   !} ⟩
            ((p *H r +H c ·H p) *x+H (p *HN m)) +H ((q *H r +H c ·H q) *x+H (q *HN m))
                ≈⟨ {!   !} ⟩
            p *H (r *x+ c ·x+ m) +H q *H (r *x+ c ·x+ m)
        ∎ where open EqH

    N-distribʳ :
        (m n o : Normal k) →
        -------------------------------------
        (m +N n) *N o ≈N (m *N o) +N (n *N o)

    N-distribʳ zero zero zero = zero
    N-distribʳ (poly p) (poly q) (poly r) = poly (H-distribʳ p q r)

-- mutual

--     *-HNH :
--         (p : HNF (suc k)) →
--         (n : Normal k) →
--         (q : HNF (suc k)) →
--         -------------------------------
--         (p *HN n) *H q ≈H p *H (n *NH q)

--     *-HNH p n q = {!   !}
    
--     *H-*x+·x+ :
--         (p : HNF (suc k)) →
--         (q : HNF (suc k)) →
--         (c : A) →
--         (n : Normal k) →
--         ----------------------------------------------------------
--         p *H (q *x+ c ·x+ n) ≈H ((p *H q +H c ·H p) *x+H (p *HN n))

--     *H-*x+·x+ = {!   !}

--     *H-assoc :
--         {p q r : HNF (suc k)} →
--         Normalised-HNF p →
--         Normalised-HNF q →
--         Normalised-HNF r →
--         ------------------------------
--         (p *H q) *H r ≈H p *H (q *H r)

--     *H-assoc ∅ q r = ∅
--     *H-assoc (_ *x+ _ ·x+ _ by _) ∅ r = ∅
--     *H-assoc {p = p} {q = q} (_ *x+ _ ·x+ _ by _) (_ *x+ _ ·x+ _ by _) ∅ =
--         begin
--             (p *H q) *H ∅
--                 ≈⟨ *H-zeroʳ (p *H q) ⟩
--             ∅
--                 ≈⟨ ≈H-refl ⟩
--             p *H (q *H ∅)
--         ∎ where open EqH
--     *H-assoc
--         {p = p′@(p *x+ c ·x+ m)} {q′@(q *x+ d ·x+ n)} {r′@(r *x+ e ·x+ o)}
--         np′@(np *x+ .c ·x+ nℓ by x) nq′@(nq *x+ .d ·x+ nm by y) nr′@(nr *x+ .e ·x+ nn by z) =
--             begin
--                 (p′ *H q′) *H r′
--                     ≈⟨⟩
--                 (p′ *H (q *x+ d ·x+ n)) *H r′
--                     ≈⟨ {!   !} ⟩
--                 ((p′ *H q +H d ·H p′) *x+H (p′ *HN n)) *H r′
--                     ≈⟨ {!   !} ⟩
--                 ((p′ *H q +H d ·H p′) *H r′) *x+H ((p′ *HN n) *H r′)
--                     ≈⟨ {!   !} ⟩
--                 ((p′ *H q) *H r′ +H (d ·H p′) *H r′) *x+H ((p′ *HN n) *H r′)
--                     ≈⟨ {!   !} ⟩
--                 (p′ *H (q *H r′) +H p′ *H (d ·H r′)) *x+H (p′ *H (n *NH r′))
--                     ≈⟨ {!   !} ⟩
--                 (p′ *H (q *H r′ +H d ·H r′)) *x+H (p′ *H (n *NH r′))
--                     ≈⟨ {!   !} ⟩
--                 p′ *H ((q *H r′ +H d ·H r′) *x+H (n *NH r′))
--                     ≈⟨ {!   !} ⟩
--                 p′ *H ((q *x+ d ·x+ n) *H r′)
--                     ≈⟨⟩
--                 p′ *H (q′ *H r′)
--                 -- ((p *x+ c ·x+ m) *H (q *x+ d ·x+ n))
--                 --     *H (r *x+ e ·x+ o)
--                 --     ≈⟨⟩
--                 -- ((pq+dp+cq *x+ cd ·x+HN cn+dm +H pn +H mq) *x+HN mn)
--                 --     *H r′
--                 --     ≈⟨ {!   !} ⟩
--                 -- (((pq+dp+cq *x+ cd ·x+HN cn+dm) +H pn +H mq) *H r′) *x+H mnr′
--                 --     ≈⟨ {!   !} ⟩
--                 -- ((pq+dp+cq *x+ cd ·x+HN cn+dm) *H r′ +H pnr′ +H mqr′) *x+H mnr′
--                 --     ≈⟨ {!   !} ⟩
--                 -- (((pq+dp+cq *H r′ +H cd ·H r′) *x+H (cn+dm *NH r′)) +H pnr′ +H mqr′) *x+H mnr′
--                 --     ≈⟨ {!   !} ⟩
--                 -- ((((pqr′ +H dpr′ +H cqr′) +H cdr′) *x+H (cnr′ +H dmr′)) +H pnr′ +H mqr′) *x+H mnr′
--                 --     ≈⟨ {!   !} ⟩
--                 -- (p *x+ c ·x+ m) *H ((q *x+ d ·x+ n) *H (r *x+ e ·x+ o))
--                 --     ≈⟨⟩
--                 -- p′ *H (q′ *H r′)
--             ∎ where
            
--                 open EqH

--                 -- pq = p *H q
--                 -- dp = d ·H p
--                 -- cq = c ·H q
--                 -- cd = c *R d
--                 -- cn = c ·N n
--                 -- dm = d ·N m
--                 -- cn+dm = cn +N dm
--                 -- pn = p *HN n
--                 -- mq = m *NH q
--                 -- mn = m *N n
--                 -- pq+dp+cq = pq +H dp +H cq
--                 -- mnr′ = mn *NH r′
--                 -- pnr′ = pn *H r′
--                 -- mqr′ = mq *H r′
--                 -- pqr′ = pq *H r′
--                 -- dpr′ = dp *H r′
--                 -- cqr′ = cq *H r′
--                 -- cdr′ = cd ·H r′
--                 -- cnr′ = cn *NH r′
--                 -- dmr′ = dm *NH r′
--     --     begin
--     --         (0H +H q) +H r ≈⟨ +H-zeroˡ q ⟨ +H-cong ⟩ ≈H-refl ⟩
--     --         q +H r ≈⟨ +H-zeroˡ _ ⟨
--     --         0H +H (q +H r)
--     --     ∎ where open EqH

--     -- +H-assoc {p = p} {∅} {r} _ _ _ =
--     --     begin
--     --         (p +H 0H) +H r ≈⟨ +H-zeroʳ p ⟨ +H-cong ⟩ ≈H-refl ⟩
--     --         p +H r ≈⟨ ≈H-refl {p = p} ⟨ +H-cong ⟩ +H-zeroˡ _ ⟨
--     --         p +H (0H +H r)
--     --     ∎ where open EqH

--     -- +H-assoc {p = p} {q} {∅} _ _ _ =
--     --     begin
--     --         (p +H q) +H ∅ ≈⟨ +H-zeroʳ _ ⟩
--     --         p +H q ≈⟨ ≈H-refl {p = p} ⟨ +H-cong ⟩ +H-zeroʳ _ ⟨
--     --         p +H (q +H ∅)
--     --     ∎ where open EqH

--     -- +H-assoc
--     --     {p = p′@(p *x+ c ·x+ m)} {q′@(q *x+ d ·x+ n)} {r′@(r *x+ e ·x+ o)}
--     --     np′@(np *x+ c ·x+ nℓ by x) nq′@(nq *x+ d ·x+ nm by y) nr′@(nr *x+ e ·x+ nn by z) =
--     --     begin
--     --     (p′ +H q′) +H r′
--     --         ≈⟨⟩
--     --     ((p +H q) *x+ c +R d ·x+HN (m +N n)) +H (r *x+ e ·x+ o)
--     --         ≈⟨ *x+·x+HN-add₀ (p +H q) _ _ _ _ _ nr′ ⟩
--     --     ((p +H q) +H r) *x+ ((c +R d) +R e) ·x+HN ((m +N n) +N o)
--     --         ≈⟨ *x+·x+HN-cong (+H-assoc np nq nr) (+R-assoc _ _ _) (+N-assoc nℓ nm nn) ⟩
--     --     (p +H (q +H r)) *x+ (c +R (d +R e)) ·x+HN (m +N (n +N o))
--     --         ≈⟨ *x+·x+HN-add₁ p _ _ _ _ _ np′ ⟨
--     --     (p *x+ c ·x+ m) +H ((q +H r) *x+ d +R e ·x+HN (n +N o))
--     --         ≈⟨⟩
--     --     p′ +H (q′ +H r′)
--     --     ∎ where open EqH

--     *N-assoc :
--         {m n o : Normal k} →
--         Normalised m →
--         Normalised n →
--         Normalised o →
--         -----------------------------
--         (m *N n) *N o ≈N m *N (n *N o)

--     *N-assoc zero zero zero = zero
--     *N-assoc (poly p) (poly q) (poly r) = poly (*H-assoc p q r)
```
