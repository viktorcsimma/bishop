-- Definitions and properties regarding multiplicative inverses.
-- Inverses require a number of results that rightfully belong in RealProperties.agda,
-- hence this new file.

-- {-# OPTIONS --without-K --safe #-}

module Inverse where

{-# FOREIGN AGDA2HS {-# LANGUAGE TypeOperators #-} #-}

open import Algebra
open import Data.Bool.Base using (Bool; if_then_else_)
open import Function.Base using (_∘_)
open import Data.Integer.Base as ℤ using (ℤ; +_; +0; +[1+_]; -[1+_])
import Data.Integer.Properties as ℤP
open import Data.Integer.DivMod as ℤD
open import Data.Nat as ℕ using (ℕ; zero; suc)
open import Data.Nat.Properties as ℕP using (≤-step)
import Data.Nat.DivMod as ℕD
open import Level using (0ℓ)
open import Data.Product
open import Relation.Nullary
open import Relation.Nullary.Negation using (contraposition)
open import Relation.Nullary.Decidable
open import Relation.Unary using (Pred)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; _≢_; refl; cong; sym; subst; trans; ≢-sym)
open import Relation.Binary
open import Data.Rational.Unnormalised as ℚ using (ℚᵘ; mkℚᵘ; _≢0; _/_; 0ℚᵘ; 1ℚᵘ; ↥_; ↧_; ↧ₙ_)
import Data.Rational.Unnormalised.Properties as ℚP
open import Algebra.Bundles
open import Algebra.Structures
open import Data.Empty
open import Data.Sum
open import Data.Maybe.Base
import NonReflectiveQ as ℚ-Solver
import NonReflectiveZ as ℤ-Solver
open import Data.List

open import Agda.Builtin.Unit
open import Haskell.Prim.Num
import Haskell.Prim.Either as Either

open import ErasureProduct
open import ExtraProperties
open import Real
open import RealProperties

-- We have to substitute some functions from the standard library with erasure-compatible versions.
-- In RewriteRules.yaml, this is rewritten to recip from Prelude.
infix  8 erased-1/_
erased-1/_ : (p : ℚᵘ) → @0 .{ℤ.∣ ↥ p ∣ ≢0} → ℚᵘ
erased-1/_ (mkℚᵘ +[1+ n ] d) = mkℚᵘ +[1+ d ] n
erased-1/_ (mkℚᵘ -[1+ n ] d) = mkℚᵘ -[1+ d ] n

open import Data.Nat.Solver renaming (module +-*-Solver to ℕ-solver)
open import Relation.Binary.PropositionalEquality

@0 e-*-inverseˡ : ∀ p {p≢0 : ℤ.∣ ↥ p ∣ ≢0} → erased-1/_ p {p≢0} ℚ.* p ℚ.≃ 1ℚᵘ
e-*-inverseˡ p@(mkℚᵘ -[1+ n ] d) = e-*-inverseˡ (mkℚᵘ +[1+ n ] d)
e-*-inverseˡ p@(mkℚᵘ +[1+ n ] d) = ℚ.*≡* (cong +[1+_] (begin
  (n ℕ.+ d ℕ.* suc n) ℕ.* 1 ≡⟨ ℕP.*-identityʳ _ ⟩
  (n ℕ.+ d ℕ.* suc n)       ≡⟨ cong (n ℕ.+_) (ℕP.*-suc d n) ⟩
  (n ℕ.+ (d ℕ.+ d ℕ.* n))   ≡⟨ solve 2 (λ n d → n :+ (d :+ d :* n) := d :+ (n :+ n :* d)) refl n d ⟩
  (d ℕ.+ (n ℕ.+ n ℕ.* d))   ≡⟨ cong (d ℕ.+_) (sym (ℕP.*-suc n d)) ⟩
  d ℕ.+ n ℕ.* suc d         ≡˘⟨ ℕP.+-identityʳ _ ⟩
  d ℕ.+ n ℕ.* suc d ℕ.+ 0   ∎))
  where open ≡-Reasoning; open ℕ-solver

@0 e-*-inverseʳ : ∀ p {p≢0 : ℤ.∣ ↥ p ∣ ≢0} → p ℚ.* erased-1/_ p {p≢0} ℚ.≃ 1ℚᵘ
e-*-inverseʳ p {p≢0} = ℚP.≃-trans (ℚP.*-comm p (erased-1/ p)) (e-*-inverseˡ p {p≢0})

-- Helper results for defining inverses

na : (x : ℝ) -> x ≄ zeroℝ -> ℕ
na x xNeq0 = suc (proj₁ (fastLemma281If (abs x) (xNonZeroThenPosAbsx x xNeq0)))
{-# COMPILE AGDA2HS na #-}

abstract
  @0 not0-helper : ∀ (x : ℝ) -> (x≄0 : x ≄0) -> ∀ (n : ℕ) ->
                ℤ.∣ ↥ (seq x ((n ℕ.+ (na x x≄0)) ℕ.* ((na x x≄0) ℕ.* (na x x≄0)))) ∣ ≢0
  not0-helper x x≄0 n = ℚP.p≄0⇒∣↥p∣≢0 xₛ (ℚ≠-helper xₛ ([ left , right ]′ (ℚP.∣p∣≡p∨∣p∣≡-p xₛ)))
    where
      open ℚP.≤-Reasoning

      N : ℕ
      N = na x x≄0

      xₛ : ℚᵘ
      xₛ = seq x ((n ℕ.+ N) ℕ.* (N ℕ.* N))

      @0 0<∣xₛ∣ : 0ℚᵘ ℚ.< ℚ.∣ xₛ ∣
      0<∣xₛ∣ = begin-strict
        0ℚᵘ     <⟨ ℚP.positive⁻¹ _ ⟩
        + 1 / N ≤⟨ (ErasureProduct.proj₂ (fastLemma281If (abs x) (xNonZeroThenPosAbsx x x≄0))) ((n ℕ.+ N) ℕ.* (N ℕ.* N))
                 (ℕP.≤-trans (ℕP.m≤n*m N {N} ℕP.0<1+n) (ℕP.m≤n*m (N ℕ.* N) {n ℕ.+ N} (subst (0 ℕ.<_) (ℕP.+-comm N n) ℕP.0<1+n))) ⟩
        ℚ.∣ xₛ ∣  ∎

      @0 left : ℚ.∣ xₛ ∣ ≡ xₛ -> xₛ ℚ.> 0ℚᵘ ⊎ xₛ ℚ.< 0ℚᵘ
      left hyp = inj₁ (begin-strict
        0ℚᵘ      <⟨ 0<∣xₛ∣ ⟩
        ℚ.∣ xₛ ∣ ≡⟨ hyp ⟩
        xₛ        ∎)

      @0 right : ℚ.∣ xₛ ∣ ≡ ℚ.- xₛ -> xₛ ℚ.> 0ℚᵘ ⊎ xₛ ℚ.< 0ℚᵘ
      right hyp = inj₂ (begin-strict
        xₛ            ≈⟨ ℚP.≃-sym (ℚP.neg-involutive xₛ) ⟩
        ℚ.- (ℚ.- xₛ)  ≡⟨ cong ℚ.-_ (sym hyp) ⟩
        ℚ.- ℚ.∣ xₛ ∣  <⟨ ℚP.neg-mono-< 0<∣xₛ∣ ⟩
        0ℚᵘ            ∎)

--Had to declare separately as abstract in order to typecheck fast enough.
--TODO: see whether it could be hidden from global scope.
abstract
  @0 lesser-helper-2 : ∀ (x : ℝ) -> (x≄0 : x ≄0) -> ∀ (n : ℕ) -> (+ 1 / (na x x≄0)) ℚ.≤ ℚ.∣ seq x ((n ℕ.+ (na x x≄0)) ℕ.* ((na x x≄0) ℕ.* (na x x≄0))) ∣
  lesser-helper-2 x x≄0 n = proj₂ (fastLemma281If (abs x) (xNonZeroThenPosAbsx x x≄0)) ((n ℕ.+ N) ℕ.* (N ℕ.* N)) lesser-helper
    where
    N : ℕ
    N = na x x≄0
    lesser-helper : (na x x≄0) ℕ.≤ (n ℕ.+ (na x x≄0)) ℕ.* ((na x x≄0) ℕ.* (na x x≄0))
    lesser-helper = ℕP.≤-trans (ℕP.m≤n+m N n) (ℕP.m≤m*n (n ℕ.+ N) {N ℕ.* N} ℕP.0<1+n)


abstract
  @0 inverse-helper : ∀ (x : ℝ) -> (x≄0 : x ≄0) -> ∀ (n : ℕ) ->
                   ℚ.∣ (erased-1/ seq x ((n ℕ.+ (na x x≄0)) ℕ.* (na x x≄0 ℕ.* na x x≄0))) {not0-helper x x≄0 n} ∣ ℚ.≤ + (na x x≄0) / 1
  inverse-helper x x≄0 n = begin
    ℚ.∣ xₛ⁻¹ ∣                             ≈⟨ ℚP.≃-sym (ℚP.*-identityʳ ℚ.∣ xₛ⁻¹ ∣) ⟩
    ℚ.∣ xₛ⁻¹ ∣ ℚ.* 1ℚᵘ                     ≈⟨ ℚP.*-congˡ {ℚ.∣ xₛ⁻¹ ∣} (ℚP.≃-sym (ℚP.*-inverseˡ (+ N / 1))) ⟩
    ℚ.∣ xₛ⁻¹ ∣ ℚ.* (+ 1 / N ℚ.* (+ N / 1)) ≈⟨ ℚP.≃-sym (ℚP.*-assoc ℚ.∣ xₛ⁻¹ ∣ (+ 1 / N) (+ N / 1)) ⟩
    ℚ.∣ xₛ⁻¹ ∣ ℚ.* (+ 1 / N) ℚ.* (+ N / 1) ≤⟨ ℚP.*-monoˡ-≤-nonNeg {+ N / 1} _ (ℚP.*-monoʳ-≤-nonNeg {ℚ.∣ xₛ⁻¹ ∣} (ℚ.nonNegative (ℚP.0≤∣p∣ (xₛ⁻¹))) (lesser-helper-2 x x≄0 n)) ⟩
    ℚ.∣ xₛ⁻¹ ∣ ℚ.* ℚ.∣ xₛ ∣ ℚ.* (+ N / 1)  ≈⟨ ℚP.*-congʳ {+ N / 1} helper ⟩
    1ℚᵘ ℚ.* (+ N / 1)                     ≈⟨ ℚP.*-identityˡ (+ N / 1) ⟩
    + N / 1                                 ∎
    where
      open ℚP.≤-Reasoning

      N : ℕ
      N = na x x≄0

      xₛ : ℚᵘ
      xₛ = seq x ((n ℕ.+ N) ℕ.* (N ℕ.* N))

      xₛ≢0 : ℤ.∣ ↥ xₛ ∣ ≢0
      xₛ≢0 = not0-helper x x≄0 n
  
      
      xₛ⁻¹ : ℚᵘ
      xₛ⁻¹ = (erased-1/ xₛ) {xₛ≢0}
      

      helper : ℚ.∣ xₛ⁻¹ ∣ ℚ.* ℚ.∣ xₛ ∣ ℚ.≃ ℚ.1ℚᵘ
      helper = begin-equality
        ℚ.∣ xₛ⁻¹ ∣ ℚ.* ℚ.∣ xₛ ∣ ≈⟨ ℚP.≃-sym (ℚP.∣p*q∣≃∣p∣*∣q∣ xₛ⁻¹ xₛ) ⟩
        ℚ.∣ xₛ⁻¹ ℚ.* xₛ ∣       ≈⟨ ℚP.∣-∣-cong (e-*-inverseˡ xₛ {xₛ≢0}) ⟩
        ℚ.1ℚᵘ                    ∎
{-
      lesser-helper : N ℕ.≤ (n ℕ.+ N) ℕ.* (N ℕ.* N)
      lesser-helper = ℕP.≤-trans (ℕP.m≤n+m N n) (ℕP.m≤m*n (n ℕ.+ N) {N ℕ.* N} ℕP.0<1+n)

      lesser-helper-2 : (+ 1 / N) ℚ.≤ ℚ.∣ xₛ ∣
      lesser-helper-2 = proj₂ (fastLemma281If {∣ x ∣} (xNonZeroThenPosAbsx {x} x≄0)) ((n ℕ.+ N) ℕ.* (N ℕ.* N)) lesser-helper
-}

-- Definition of the multiplicative inverse function _⁻¹
-- Here x ≄ zeroℝ cannot be erased; since the natural in it is used for the computation.
-- And therefore, sadly, we cannot really define a Fractional instance.
-- And no copatterns;)
_\<_ : (x : ℝ) -> x ≄ zeroℝ -> ℝ
(x \< xNeq0) = Mkℝ sequence proofForSequence
  where
    open ℚP.≤-Reasoning

    l = na x xNeq0  -- this is where it needs the existence proof from x≄0; that's why it cannot be erased

    sequence : ℕ → ℚᵘ
    sequence n = (erased-1/ xₛ) {not0-helper x xNeq0 n}
      where
        xₛ = seq x ((n ℕ.+ l) ℕ.* (l ℕ.* l))

    @0 proofForSequence : (m n : ℕ) {@0 m≢0 : m ≢0} {@0 n≢0 : n ≢0} →
          ℚ.∣ sequence m ℚ.- sequence n ∣ ℚ.≤
          (+ 1 / m) {m≢0} ℚ.+ (+ 1 / n) {n≢0}
    proofForSequence (suc k₁) (suc k₂) = begin
     ℚ.∣ yₘ ℚ.- yₙ ∣                                 ≈⟨ ℚP.∣-∣-cong (ℚP.+-cong
                                                          ((ℚP.≃-trans (ℚP.≃-sym (ℚP.*-identityʳ yₘ)) (ℚP.*-congˡ {yₘ} (ℚP.≃-sym (e-*-inverseˡ xₙ {xₖ≢0 n})))))
                                                          ((ℚP.-‿cong (ℚP.≃-trans (ℚP.≃-sym (ℚP.*-identityʳ yₙ)) (ℚP.*-congˡ {yₙ} (ℚP.≃-sym (e-*-inverseˡ xₘ {xₖ≢0 m}))))))) ⟩
       ℚ.∣ yₘ ℚ.* (yₙ ℚ.* xₙ) ℚ.- yₙ ℚ.* (yₘ ℚ.* xₘ) ∣ ≈⟨ ℚP.∣-∣-cong (solve 4 (λ xₘ xₙ yₘ yₙ ->
                                                          (yₘ ⊗ (yₙ ⊗ xₙ) ⊖ yₙ ⊗ (yₘ ⊗ xₘ)) ⊜ (yₘ ⊗ yₙ ⊗ (xₙ ⊖ xₘ)))
                                                          ℚP.≃-refl xₘ xₙ yₘ yₙ) ⟩
       ℚ.∣ yₘ ℚ.* yₙ ℚ.* (xₙ ℚ.- xₘ) ∣                 ≈⟨ ℚP.∣p*q∣≃∣p∣*∣q∣ (yₘ ℚ.* yₙ) (xₙ ℚ.- xₘ) ⟩
       ℚ.∣ yₘ ℚ.* yₙ ∣ ℚ.* ℚ.∣ xₙ ℚ.- xₘ ∣             ≤⟨ ℚP.≤-trans
                                                          (ℚP.*-monoʳ-≤-nonNeg {ℚ.∣ yₘ ℚ.* yₙ ∣} _ (reg x ((n ℕ.+ l) ℕ.* (l ℕ.* l)) ((m ℕ.+ l) ℕ.* (l ℕ.* l))))
                                                          (ℚP.*-monoˡ-≤-nonNeg {+ 1 / ((n ℕ.+ l) ℕ.* (l ℕ.* l)) ℚ.+ + 1 / ((m ℕ.+ l) ℕ.* (l ℕ.* l))} _ ∣yₘ*yₙ∣≤l²) ⟩
       (+ l / 1) ℚ.* (+ l / 1) ℚ.*
       ((+ 1 / ((n ℕ.+ l) ℕ.* (l ℕ.* l))) ℚ.+
        (+ 1 / ((m ℕ.+ l) ℕ.* (l ℕ.* l))))             ≈⟨ ℚ.*≡* (ℤsolve 3 (λ m n l ->
                                                          ((l :* l) :* ((κ (+ 1) :* ((m :+ l) :* (l :* l))) :+
                                                          (κ (+ 1) :* ((n :+ l) :* (l :* l))))) :* ((m :+ l) :* (n :+ l)) :=
                                                          (κ (+ 1) :* (n :+ l) :+ κ (+ 1) :* (m :+ l)) :* (κ (+ 1) :* κ (+ 1) :*
                                                          (((n :+ l) :* (l :* l)) :* ((m :+ l) :* (l :* l)))))
                                                          refl (+ m) (+ n) (+ l)) ⟩

       (+ 1 / (m ℕ.+ l)) ℚ.+ (+ 1 / (n ℕ.+ l))         ≤⟨ ℚP.+-mono-≤
                                                          (q≤r⇒+p/r≤+p/q 1 m (m ℕ.+ l) (ℕP.m≤m+n m l))
                                                          (q≤r⇒+p/r≤+p/q 1 n (n ℕ.+ l) (ℕP.m≤m+n n l)) ⟩
       (+ 1 / m) ℚ.+ (+ 1 / n)                          ∎
      where
        open ℚP.≤-Reasoning
        open ℚ-Solver
        open ℤ-Solver using ()
          renaming
            ( solve to ℤsolve
            ; _⊕_   to _:+_
            ; _⊗_   to _:*_
            ; _⊜_   to _:=_
            ; Κ     to κ
            )
        
        m = suc k₁
        n = suc k₂

        xₘ = seq x ((m ℕ.+ l) ℕ.* (l ℕ.* l))
        xₙ = seq x ((n ℕ.+ l) ℕ.* (l ℕ.* l))

        xₖ≢0 : ∀ (k : ℕ) -> ℤ.∣ ↥ seq x ((k ℕ.+ l) ℕ.* (l ℕ.* l)) ∣ ≢0
        xₖ≢0 k = not0-helper x xNeq0 k

        yₘ = (erased-1/ xₘ) {xₖ≢0 m}
        yₙ = (erased-1/ xₙ) {xₖ≢0 n}

        ∣yₘ*yₙ∣≤l² : ℚ.∣ yₘ ℚ.* yₙ ∣ ℚ.≤ (+ l / 1) ℚ.* (+ l / 1)
        ∣yₘ*yₙ∣≤l² = begin
          ℚ.∣ yₘ ℚ.* yₙ ∣          ≈⟨ ℚP.∣p*q∣≃∣p∣*∣q∣ yₘ yₙ ⟩
          ℚ.∣ yₘ ∣ ℚ.* ℚ.∣ yₙ ∣    ≤⟨ ℚ-*-mono-≤ {ℚ.∣ yₘ ∣} {+ l / 1} {ℚ.∣ yₙ ∣} {+ l / 1} _ _
                                     (inverse-helper x xNeq0 m) (inverse-helper x xNeq0 n) ⟩
          (+ l / 1) ℚ.* (+ l / 1)   ∎
{-# COMPILE AGDA2HS _\<_ #-}

-- The old name as an erased alias.
@0 _⁻¹ : (x : ℝ) → x ≄ zeroℝ → ℝ
_⁻¹ = _\<_

@0 +p≤+q⇒1/q≤1/p : ∀ {p q} -> (posp : ℚ.Positive p) -> (posq : ℚ.Positive q) -> p ℚ.≤ q ->
                (erased-1/ q) {ℚP.p≄0⇒∣↥p∣≢0 q (ℚ≠-helper q (inj₁ (ℚP.positive⁻¹ posq)))} ℚ.≤ (erased-1/ p) {ℚP.p≄0⇒∣↥p∣≢0 p (ℚ≠-helper p (inj₁ (ℚP.positive⁻¹ posp)))}
+p≤+q⇒1/q≤1/p {mkℚᵘ (+ suc p-1) q-1} {mkℚᵘ (+ suc u-1) v-1} posp/q posu/v p/q≤u/v = let p = + suc p-1; q = + suc q-1; u = + suc u-1; v = + suc v-1 in
                                                                                    ℚ.*≤* (begin
  v ℤ.* p ≡⟨ ℤP.*-comm v p ⟩
  p ℤ.* v ≤⟨ ℚP.drop-*≤* p/q≤u/v ⟩
  u ℤ.* q ≡⟨ ℤP.*-comm u q ⟩
  q ℤ.* u  ∎)
  where open ℤP.≤-Reasoning

-- Properties of _⁻¹

@0 *-inverseʳ : ∀ x -> (x≄0 : x ≄0) -> x * (x \< x≄0) ≃ oneℝ
*-inverseʳ x x≄0 = *≃* λ @0 {(suc k₁) ->
                     let n = suc k₁; x⁻¹ = (x ⁻¹) x≄0; k = fK x ℕ.⊔ fK x⁻¹
                            ; N = na x x≄0; x₂ₖₙ = seq x (2 ℕ.* k ℕ.* n)
                            ; xₛ = seq x ((2 ℕ.* k ℕ.* n ℕ.+ N) ℕ.* (N ℕ.* N))
                            ; y₂ₖₙ = (erased-1/ xₛ) {not0-helper x x≄0 (2 ℕ.* k ℕ.* n)} in begin
  ℚ.∣ x₂ₖₙ ℚ.* y₂ₖₙ ℚ.- 1ℚᵘ ∣                                   ≈⟨ ℚP.∣-∣-cong (ℚP.+-congʳ (x₂ₖₙ ℚ.* y₂ₖₙ) (ℚP.-‿cong
                                                                   (ℚP.≃-sym (e-*-inverseʳ xₛ {not0-helper x x≄0 (2 ℕ.* k ℕ.* n)})))) ⟩
  ℚ.∣ x₂ₖₙ ℚ.* y₂ₖₙ ℚ.- xₛ ℚ.* y₂ₖₙ ∣                           ≈⟨ ℚP.≃-trans
                                                                   (ℚP.∣-∣-cong (solve 3 (λ x₂ₖₙ xₛ y₂ₖₙ ->
                                                                   (x₂ₖₙ ⊗ y₂ₖₙ ⊖ xₛ ⊗ y₂ₖₙ) ⊜ (y₂ₖₙ ⊗ (x₂ₖₙ ⊖ xₛ)))
                                                                   ℚP.≃-refl x₂ₖₙ xₛ y₂ₖₙ))
                                                                   (ℚP.∣p*q∣≃∣p∣*∣q∣ y₂ₖₙ (x₂ₖₙ ℚ.- xₛ))⟩
  ℚ.∣ y₂ₖₙ ∣  ℚ.* ℚ.∣ x₂ₖₙ ℚ.- xₛ ∣                             ≤⟨ ℚ-*-mono-≤ _ _
                                                                   (ℚP.≤-trans (ℚP.<⇒≤ (canonical-strict-upper-bound x⁻¹ (2 ℕ.* k ℕ.* n)))
                                                                               (p≤q⇒p/r≤q/r (+ fK x⁻¹) (+ k) 1 (ℤ.+≤+ (ℕP.m≤n⊔m (fK x) (fK x⁻¹)))))
                                                                   (reg x (2 ℕ.* k ℕ.* n) ((2 ℕ.* k ℕ.* n ℕ.+ N) ℕ.* (N ℕ.* N))) ⟩
  + k / 1 ℚ.* (+ 1 / (2 ℕ.* k ℕ.* n) ℚ.+
  + 1 / ((2 ℕ.* k ℕ.* n ℕ.+ N) ℕ.* (N ℕ.* N)))                  ≤⟨ ℚP.*-monoʳ-≤-nonNeg {+ k / 1} _ (ℚP.+-monoʳ-≤ (+ 1 / (2 ℕ.* k ℕ.* n))
                                                                   (q≤r⇒+p/r≤+p/q 1 (2 ℕ.* k ℕ.* n) ((2 ℕ.* k ℕ.* n ℕ.+ N) ℕ.* (N ℕ.* N))
                                                                   (ℕP.≤-trans (ℕP.m≤m+n (2 ℕ.* k ℕ.* n) N) (ℕP.m≤m*n (2 ℕ.* k ℕ.* n ℕ.+ N) {N ℕ.* N} ℕP.0<1+n)))) ⟩
  + k / 1 ℚ.* (+ 1 / (2 ℕ.* k ℕ.* n) ℚ.+ + 1 / (2 ℕ.* k ℕ.* n)) ≈⟨ ℚ.*≡* (ℤsolve 2 (λ k n ->
                                                                   (k :* (κ (+ 1) :* (κ (+ 2) :* k :* n) :+ κ (+ 1) :* (κ (+ 2) :* k :* n))) :* n :=
                                                                   κ (+ 1) :* (κ (+ 1) :* (κ (+ 2) :* k :* n :* (κ (+ 2) :* k :* n))))
                                                                   refl (+ k) (+ n)) ⟩
  + 1 / n                                                       ≤⟨ p≤q⇒p/r≤q/r (+ 1) (+ 2) n (ℤ.+≤+ (ℕ.s≤s ℕ.z≤n)) ⟩
  + 2 / n                                                                                    ∎}
  where
    open ℚP.≤-Reasoning
    open ℚ-Solver
    open ℤ-Solver using ()
      renaming
        ( solve to ℤsolve
        ; _⊕_   to _:+_
        ; _⊗_   to _:*_
        ; _⊜_   to _:=_
        ; Κ     to κ
        )

@0 *-inverseˡ : ∀ x -> (x≄0 : x ≄0) -> (x \< x≄0) * x ≃ oneℝ
*-inverseˡ x x≄0 = let x⁻¹ = (x ⁻¹) x≄0 in begin
  x⁻¹ * x ≈⟨ *-comm x⁻¹ x ⟩
  x * x⁻¹ ≈⟨ *-inverseʳ x x≄0 ⟩
  oneℝ       ∎
  where open ≃-Reasoning

abstract
  @0 ⁻¹-unique : ∀ (t x : ℝ) -> (x≄0 : x ≄0) -> t * x ≃ oneℝ -> t ≃ x \< x≄0
  ⁻¹-unique t x x≄0 tx=1 = let x⁻¹ = (x ⁻¹) x≄0 in begin 
    t             ≈⟨ ≃-sym (*-identityʳ t) ⟩
    t * oneℝ        ≈⟨ *-congˡ (≃-sym (*-inverseʳ x x≄0)) ⟩
    t * (x * x⁻¹) ≈⟨ ≃-sym (*-assoc t x x⁻¹) ⟩
    (t * x) * x⁻¹ ≈⟨ *-congʳ tx=1 ⟩
    oneℝ * x⁻¹      ≈⟨ *-identityˡ x⁻¹ ⟩
    x⁻¹            ∎
    where open ≃-Reasoning

@0 ⁻¹-cong : ∀ {x y} -> (x≄0 : x ≄0) -> (y≄0 : y ≄0) -> x ≃ y -> x \< x≄0 ≃ y \< y≄0
⁻¹-cong {x} {y} x≄0 y≄0 x≃y = ⁻¹-unique x⁻¹ y y≄0 lem 
  where
    open ≃-Reasoning
    x⁻¹ = (x ⁻¹) x≄0
    y⁻¹ = (y ⁻¹) y≄0
    lem : x⁻¹ * y ≃ oneℝ
    lem = begin
      x⁻¹ * y ≈⟨ *-congˡ (≃-sym x≃y) ⟩
      x⁻¹ * x ≈⟨ *-inverseˡ x x≄0 ⟩
      oneℝ       ∎

posxThenPosxInv : ∀ (x : ℝ) -> (xNeq0 : x ≄ zeroℝ) -> Positive x -> Positive (x \< xNeq0)
posxThenPosxInv x xNeq0 posx = let fromPosx = fastLemma281If x posx; M = suc (proj₁ fromPosx) in
                           lemma281OnlyIf (x \< xNeq0) (ℕ.pred (fK x ℕ.⊔ M) :&: λ @0 {(suc k₁) m≥Kₓ⊔M ->
                           let m = suc k₁; N = na x xNeq0; xₛ = seq x ((m ℕ.+ N) ℕ.* (N ℕ.* N)); yₘ = (erased-1/ xₛ) {not0-helper x xNeq0 m} in begin
 + 1 / (fK x ℕ.⊔ M) ≤⟨ q≤r⇒+p/r≤+p/q 1 (fK x) (fK x ℕ.⊔ M) (ℕP.m≤m⊔n (fK x) M) ⟩
 + 1 / (fK x)       ≤⟨ +p≤+q⇒1/q≤1/p {xₛ} {+ fK x / 1}
                      (ℚ.positive (ℚP.<-≤-trans (ℚP.positive⁻¹ {+ 1 / M} _) (proj₂ fromPosx ((m ℕ.+ N) ℕ.* (N ℕ.* N))
                                  (ℕP.≤-trans (ℕP.≤-trans (ℕP.≤-trans (ℕP.m≤n⊔m (fK x) M) m≥Kₓ⊔M) (ℕP.m≤m+n m N)) (ℕP.m≤m*n (m ℕ.+ N) {N ℕ.* N} ℕP.0<1+n))))) _
                      (ℚP.≤-trans (p≤∣p∣ xₛ) (ℚP.<⇒≤ (canonical-strict-upper-bound x ((m ℕ.+ N) ℕ.* (N ℕ.* N))))) ⟩
 yₘ                  ∎})
  where open ℚP.≤-Reasoning
{-# COMPILE AGDA2HS posxThenPosxInv #-}

-- For some reason, it stucks when we work with (negate x)⁻¹. So for now, we postulate them.
postulate @0 neg-distrib-⁻¹ : ∀ {x : ℝ} -> (x≄0 : x ≄0) -> negate (x \< x≄0) ≃ (negate x) \< x≄0⇒-x≄0 x x≄0
{-
neg-distrib-⁻¹ {x} x≄0 = {!theProof!}
  where
    x⁻¹ -x⁻¹ : ℝ
    x⁻¹ = x \< x≄0
    -x⁻¹ = negate x⁻¹
    -x≄0 : negate x ≄0
    -x≄0 = x≄0⇒-x≄0 x x≄0
    ≃-helper : -x⁻¹ * negate x ≃ oneℝ
    ≃-helper = begin
      -x⁻¹ * negate x            ≈⟨ ≃-sym {negate (x⁻¹ * (negate x))} {negate x⁻¹ * negate x} (neg-distribˡ-* x⁻¹ (negate x)) ⟩
      negate (x⁻¹ * (negate x))        ≈⟨ -‿cong {x⁻¹ * (negate x)} {negate (x⁻¹ * x)} (≃-sym (neg-distribʳ-* x⁻¹ x)) ⟩
      negate (negate (x⁻¹ * x))        ≈⟨ neg-involutive (x⁻¹ * x) ⟩
      x⁻¹ * x                          ≈⟨ *-inverseˡ x x≄0 ⟩
      oneℝ                            ∎
      where open ≃-Reasoning
    [-x]⁻¹ : ℝ
    [-x]⁻¹ = (negate x) \< -x≄0
    theProof : -x⁻¹ ≃ [-x]⁻¹
    theProof = {!⁻¹-unique {!-x⁻¹!} {!negate x!} {!-x≄0!} {!≃-helper!}!}
-}

private
  -- abstract
  postulate @0 pos-[-x]⁻¹-helper : ∀ {x : ℝ} (x≄0 : x ≄0) -> Negative x -> Positive (((negate x) ⁻¹) (x≄0⇒-x≄0 x x≄0))
    -- pos-[-x]⁻¹-helper {x} x≄0 negx = {!posxThenPosxInv (negate x) {!x≄0⇒-x≄0 x x≄0!} {!negx!}!}

@0 negx⇒negx⁻¹ : ∀ {x : ℝ} -> (x≄0 : x ≄0) -> Negative x -> Negative ((x ⁻¹) x≄0)
negx⇒negx⁻¹ {x} x≄0 negx = posCong [-x]⁻¹ (negate x⁻¹) (≃-sym (neg-distrib-⁻¹ {x} x≄0)) (pos-[-x]⁻¹-helper {x} x≄0 negx)
  where
  x⁻¹ [-x]⁻¹ : ℝ
  x⁻¹ = (x ⁻¹) x≄0
  [-x]⁻¹ = ((negate x) ⁻¹) (x≄0⇒-x≄0 x x≄0)


@0 x<0⇒x⁻¹<0 : ∀ {x : ℝ} -> (x≄0 : x ≄0) -> x < zeroℝ -> (x ⁻¹) x≄0 < zeroℝ
x<0⇒x⁻¹<0 {x} x≄0 x<0 = let x⁻¹ = (x ⁻¹) x≄0 in
                        negxThenxLtZero x⁻¹ (negx⇒negx⁻¹ {x} x≄0 (xLtZeroThenNegx x x<0))

-- had to use erased resp here
invMonoLt : ∀ (x y : ℝ) -> x < y -> (x≄0 : x ≄ zeroℝ) -> (y≄0 : y ≄ zeroℝ) -> Positive x -> Positive y ->
                     y \< y≄0 < x \< x≄0
invMonoLt x y xLty xNeqZero yNeqZero posx posy = ltRespLEq xInv (x * xInv * yInv) yInv (≃-trans {x * xInv * yInv} {oneℝ * yInv} {yInv} (*-congʳ (*-inverseʳ x xNeqZero)) (*-identityˡ yInv))
                                                     (ltRespREq (x * xInv * yInv) (y * xInv * yInv) (xInv)
                                                                     (≃-trans {y * xInv * yInv} {xInv * (y * yInv)} {xInv} (≃-trans (*-congʳ (*-comm y xInv)) (*-assoc xInv y yInv)) (≃-trans (*-congˡ (*-inverseʳ y yNeqZero)) (*-identityʳ xInv)))
                                                                     (multiMonoLLtPos yInv (posxThenPosxInv y yNeqZero posy) (x * xInv) (y * xInv)
                                                                       (multiMonoLLtPos xInv (posxThenPosxInv x xNeqZero posx) x y xLty)))
  {-begin-strict
  y⁻¹             ≈⟨ ≃-sym (≃-trans {x * x⁻¹ * y⁻¹} {oneℝ * y⁻¹} {y⁻¹} (*-congʳ (*-inverseʳ x x≄0)) (*-identityˡ y⁻¹)) ⟩
  x * x⁻¹ * y⁻¹   <⟨ *-monoˡ-<-pos {y⁻¹} (posxThenPosxInv y y≄0 posy) {x * x⁻¹} {y * x⁻¹}
                     (*-monoˡ-<-pos {x⁻¹} (posxThenPosxInv x x≄0 posx) x<y) ⟩
  y * x⁻¹ * y⁻¹   ≈⟨ ≃-trans (*-congʳ (*-comm y x⁻¹)) (*-assoc x⁻¹ y y⁻¹) ⟩
  x⁻¹ * (y * y⁻¹) ≈⟨ ≃-trans (*-congˡ (*-inverseʳ y y≄0)) (*-identityʳ x⁻¹) ⟩
  x⁻¹              ∎-}
  where
    -- open ≤-Reasoning
    xInv yInv : ℝ
    xInv = x \< xNeqZero ; yInv = y \< yNeqZero
{-# COMPILE AGDA2HS invMonoLt #-}

-- Alias.
@0 x<y∧posx,y⇒y⁻¹<x⁻¹ : ∀ {x y : ℝ} -> x < y -> (x≄0 : x ≄0) -> (y≄0 : y ≄0) -> Positive x -> Positive y ->
                     (y ⁻¹) y≄0 < (x ⁻¹) x≄0
x<y∧posx,y⇒y⁻¹<x⁻¹ {x} {y} = invMonoLt x y

@0 ⁻¹-involutive : ∀ {x} -> (x≄0 : x ≄0) -> (x⁻¹≄0 : (x ⁻¹) x≄0 ≄0) ->
                (((x ⁻¹) x≄0) ⁻¹) x⁻¹≄0 ≃ x
⁻¹-involutive {x} x≄0 x⁻¹≄0 = let x⁻¹ = (x ⁻¹) x≄0 in ≃-sym (⁻¹-unique x x⁻¹ x⁻¹≄0 (*-inverseʳ x x≄0))

@0 0<x⇒0<x⁻¹ : ∀ {x} -> (x≄0 : x ≄0) -> zeroℝ < x -> zeroℝ < (x ⁻¹) x≄0
0<x⇒0<x⁻¹ {x} x≄0 0<x = posxThenZeroLtx ((x ⁻¹) x≄0) (posxThenPosxInv x x≄0 (zeroLtxThenPosx x 0<x))

-- A default proof for the ≄0-ity of the inverse.
@0 x⁻¹≄0 : ∀ (x : ℝ) (x≄0 : x ≄0) -> (x \< x≄0) ≄0
x⁻¹≄0 x x≄0 = Either.either (λ x<0 -> Either.Left (x<0⇒x⁻¹<0 {x} x≄0 x<0)) (λ 0<x -> Either.Right (0<x⇒0<x⁻¹ {x} x≄0 0<x)) x≄0

-- A version of ⁻¹-involutive which uses the default proof.
@0 ⁻¹-involutive-default : ∀ {x} -> (x≄0 : x ≄0) ->
                (((x ⁻¹) x≄0) ⁻¹) (x⁻¹≄0 x x≄0) ≃ x
⁻¹-involutive-default {x} x≄0 = ⁻¹-involutive {x} x≄0 (x⁻¹≄0 x x≄0)
