---
title:
---

```
-- {-# OPTIONS --allow-unsolved-metas #-}

open import Preliminaries.Base

module Preliminaries.Homomorphism
    (R : CommutativeRing)
    (S : CommutativeRing)
    where

open import Preliminaries.Algebra S using (+-inv-unique)
open import Algebra

open import Preliminaries.PolyExpr R as PR renaming
    (PolyExpr to PolyExprR;
    _≈_ to _[≈]R_;
    _+_ to _[+]R_;
    -_ to [-]R_;
    _*_ to _[*]R_;
    PE to PER
    )

open import Preliminaries.PolyExpr S as PS renaming
    (PolyExpr to PolyExprS;
    _≈_ to _[≈]S_;
    _+_ to _[+]S_;
    -_ to [-]S_;
    _*_ to _[*]S_
    )

open CommutativeRing R renaming
    (Carrier to CarrierR;
    0# to 0R;
    1# to 1R;
    _+_ to _+R_;
    -_ to -R_;
    _*_ to _*R_;
    _≈_ to _≈R_;
    -‿inverseʳ to -R‿inverseʳ
    ) 

open CommutativeRing S renaming
    (Carrier to CarrierS;
    0# to 0S;
    1# to 1S;
    _+_ to _+S_;
    -_ to -S_;
    _*_ to _*S_;
    _≈_ to _≈S_;
    -‿cong to -S‿cong;
    sym to S-sym;
    trans to S-trans;
    isEquivalence to isEquivalenceS
    )

private variable X Y : Set

record IsRingHom (φ : CarrierR → CarrierS) : Set where
    field
        ≈-hom : ∀ {a b} → a ≈R b → φ a ≈S φ b
        0-hom : φ 0R ≈S 0S
        1-hom : φ 1R ≈S 1S
        +-hom : ∀ a b → φ (a +R b) ≈S φ a +S φ b
        *-hom : ∀ a b → φ (a *R b) ≈S φ a *S φ b

ext : (CarrierR → CarrierS) → PolyExprR X → PolyExprS X
ext φ (con c) = PS.con (φ c)
ext φ (var x) = PS.var x
ext φ (p [+]R q) = ext φ p [+]S ext φ q
ext φ (p [*]R q) = ext φ p [*]S ext φ q

open import Preliminaries.Vector

module _
    {φ : CarrierR → CarrierS}
    (isRingHom : IsRingHom φ)
    where

    open IsRingHom isRingHom
    open import Preliminaries.AuxiliaryLemmas S
    open import Preliminaries.Equivalence isEquivalenceS

    -‿hom : ∀ a → φ (-R a) ≈S (-S (φ a))
    -‿hom a = +-inv-unique _ _ aux where
        aux : φ a +S φ (-R a) ≈S 0S
        aux =
            begin
                φ a +S φ (-R a)
                    ≈⟨ +-hom _ _ ⟨
                φ (a +R -R a)
                    ≈⟨ ≈-hom (-R‿inverseʳ _) ⟩
                φ 0R
                    ≈⟨ 0-hom ⟩
                0S
            ∎ where open Eq

    -‿one-hom :  φ (-R 1R) ≈S -S 1S
    -‿one-hom = S-trans (-‿hom _) (-S‿cong 1-hom)

    -‿hom-ext : ∀ (p : PolyExprR X) → ext φ (PR.- p) [≈]S (PS.- (ext φ p))
    -‿hom-ext p = 
        begin
            PS.con (φ (-R 1R)) [*]S (ext φ p)
                ≈⟨ PS.*-cong (PS.≈-con -‿one-hom) PS.≈-refl ⟩
            PS.con ((-S 1S)) [*]S (ext φ p)
                ≈⟨⟩
            ([-]S ext φ p)
        ∎ where open PS.EqP

    one-ext : ext φ (PR.1P {X}) [≈]S PS.1P
    one-ext =
        begin
            PS.con (φ 1R)
                ≈⟨ PS.≈-con 1-hom ⟩
            PS.con 1S
                ≈⟨⟩
            PS.1P
        ∎ where open PS.EqP

    -- homomorphism lemma
    -- homomorphisms respect equivalent polynomials
    private
        lem :
            ∀ {a b : PolyExprR X} →
            a [≈]R b →
            -----------------------
            ext φ a [≈]S ext φ b
        
    lem ≈-refl = PS.≈-refl
    lem (≈-sym b≈a) = PS.≈-sym (lem b≈a)
    lem (≈-trans a≈b b≈c) = PS.≈-trans (lem a≈b) (lem b≈c)
    lem (≈-con c≈Rd) = PS.≈-con (≈-hom c≈Rd)
    lem (+-cong p≈q r≈s) = PS.+-cong (lem p≈q) (lem r≈s)
    lem (+-con c d) =
        begin
            PS.con (φ (c +R d))
                ≈⟨ PS.≈-con $ +-hom _ _ ⟩
            PS.con ( φ c +S φ d )
                ≈⟨ PS.+-con _ _ ⟩
            PS.con (φ c) [+]S PS.con (φ d)
        ∎ where open PS.EqP
    lem (+-zeroʳ p) =
        begin
            ext φ p [+]S PS.con (φ 0R)
                ≈⟨ PS.+-cong PS.≈-refl (PS.≈-con 0-hom) ⟩
            ext φ p [+]S PS.con 0S
                ≈⟨ PS.+-zeroʳ _ ⟩
            ext φ p
        ∎ where open PS.EqP
    lem (+-assoc p q r) = PS.+-assoc _ _ _
    lem (+-comm p q) = PS.+-comm _ _
    lem (+-invʳ p) =
        begin
            ext φ p [+]S ext φ (PR.- p)
                ≈⟨ PS.+-cong PS.≈-refl (-‿hom-ext _) ⟩
            ext φ p [+]S (PS.- (ext φ p))
                ≈⟨ PS.+-invʳ _ ⟩
            PS.con 0S
                ≈⟨ PS.≈-con 0-hom ⟨
            PS.con (φ 0R)
        ∎ where open PS.EqP
    lem (*-cong a≈b c≈d) = PS.*-cong (lem a≈b) (lem c≈d)
    lem (*-con c d) =
        begin
            PS.con (φ (c *R d))
                ≈⟨ PS.≈-con $ *-hom _ _ ⟩
            PS.con ( φ c *S φ d )
                ≈⟨ PS.*-con _ _ ⟩
            PS.con (φ c) [*]S PS.con (φ d)
        ∎ where open PS.EqP
    lem (*-oneʳ p) =
        begin
            ext φ p [*]S PS.con (φ 1R)
                ≈⟨ PS.*-cong PS.≈-refl (PS.≈-con 1-hom) ⟩
            ext φ p [*]S PS.con 1S
                ≈⟨ PS.*-oneʳ _ ⟩
            ext φ p
        ∎ where open PS.EqP
    lem (*-assoc p q r) = PS.*-assoc _ _ _
    lem (*-comm p q) = PS.*-comm _ _
    lem (*-distrʳ p q r) = PS.*-distrʳ _ _ _

    hom-lemma = lem
```