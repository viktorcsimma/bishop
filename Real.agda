-- Definition of the real numbers with arithmetic operations and ordering

-- {-# OPTIONS --without-K --safe #-}       -- commented out so that we can use Haskell.Prelude

module Real where

-- {-# FOREIGN AGDA2HS {-# LANGUAGE TypeOperators #-} #-}          -- maybe for _<_

open import Algebra
open import Data.Bool.Base using (Bool; if_then_else_)
-- open import Function.Base using (_∘_)
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
open import Data.List hiding (sum)

-- we have to import this for the Num type class
-- but with lots of hidings
open import Haskell.Prim.Num -- hiding (seq; step-≡; _∎; cong; _×_; _×_×_; sym; begin_; _,_; m; max; Negative; _<_; _>_; sum) --is --cubical-compatible and not --without-K
open import Haskell.Prim using (_∘_)

open import Agda.Builtin.Unit
open import ErasureProduct
open import ExtraProperties

-- In Haskell we use Rational, which is a normalised type.
open ℚᵘ public

record ℝ : Set where
  constructor Mkℝ
  field
    -- No n≢0 condition for seq
    seq : ℕ → ℚᵘ
    @0 reg : (m n : ℕ) {@0 m≢0 : m ≢0} {@0 n≢0 : n ≢0} →  -- @0 means runtime irrelevance
          ℚ.∣ seq m ℚ.- seq n ∣ ℚ.≤
          (+ 1 / m) {m≢0} ℚ.+ (+ 1 / n) {n≢0}
{-# COMPILE AGDA2HS ℝ newtype #-}

open ℝ public

-- I took out those that are in the Num type class and those that got renamed.
infix 4 _≃_
infixl 6 _⊔_ _⊓_ _⊓₂_

data _≃_ : Rel ℝ Level.zero where
  *≃* : {x y : ℝ} → @0 ((n : ℕ) {n≢0 : n ≢0} →
        ℚ.∣ seq x n ℚ.- seq y n ∣ ℚ.≤ (+ 2 / n) {n≢0}) →
        x ≃ y

-- Before defining the arithmetic operations, we will need something called
-- a canonical bound of a real number x ≡ (xₙ). The canonical bound is just the least
-- least integer than or equal to ∣x₁∣ + 2.
-- We will also need a couple of small technical results about it.

-- f for function
-- has to start with a lowercase letter; otherwise agda2hs won't accept it

-- denominatorℕ and ↧ₙ simply didn't work in agda2hs; it was losing the parameters... I think that was a bug
-- so we have to circumvent this
-- I think the problem is that they are functions within the record definition, but not destructors
-- what about suc ∘ denominator-1?
fK : ℝ -> ℕ
fK x = let p = ↥ (ℚ.∣ seq x 1 ∣ ℚ.+ (+ 2 / 1)); q = (suc ∘ denominator-1) (ℚ.∣ seq x 1 ∣ ℚ.+ (+ 2 / 1)) in suc ℤ.∣ p divℕ q ∣
{-# COMPILE AGDA2HS fK #-}


private
  abstract
    @0 Kx=1+t : ∀ x -> + fK x ≡ + 1 ℤ.+ ((↥ (ℚ.∣ seq x 1 ∣ ℚ.+ 2ℚᵘ) divℕ ↧ₙ (ℚ.∣ seq x 1 ∣ ℚ.+ 2ℚᵘ)))
    Kx=1+t x = let t = (↥ (ℚ.∣ seq x 1 ∣ ℚ.+ 2ℚᵘ) divℕ ↧ₙ (ℚ.∣ seq x 1 ∣ ℚ.+ 2ℚᵘ)) in begin-equality
      + fK x             ≡⟨ _≡_.refl ⟩
      + 1 ℤ.+ + ℤ.∣ t ∣ ≡⟨ cong (λ x -> + 1 ℤ.+ x) (ℤP.0≤n⇒+∣n∣≡n (0≤n⇒0≤n/ℕd (↥ (ℚ.∣ seq x 1 ∣ ℚ.+ 2ℚᵘ)) (↧ₙ (ℚ.∣ seq x 1 ∣ ℚ.+ 2ℚᵘ))
                                (ℚP.≥0⇒↥≥0 (ℚP.≤-trans (ℚP.0≤∣p∣ (seq x 1)) (ℚP.p≤p+q {ℚ.∣ seq x 1 ∣} {2ℚᵘ} _))))) ⟩
      + 1 ℤ.+ t          ∎
      where
        open ℤP.≤-Reasoning

abstract
  @0 canonical-well-defined : ∀ (x : ℝ) -> ((ℚ.∣ seq x 1 ∣ ℚ.+ 2ℚᵘ) ℚ.< (+ fK x / 1)) ×
                           (∀ (n : ℤ) -> (ℚ.∣ seq x 1 ∣ ℚ.+ 2ℚᵘ) ℚ.< (n / 1) -> (+ fK x) ℤ.≤ n)
  canonical-well-defined x = left , right
    where
      left : ℚ.∣ seq x 1 ∣ ℚ.+ 2ℚᵘ ℚ.< + fK x / 1
      left = let t = ↥ (ℚ.∣ seq x 1 ∣ ℚ.+ 2ℚᵘ) divℕ ↧ₙ (ℚ.∣ seq x 1 ∣ ℚ.+ 2ℚᵘ) in begin-strict
        ℚ.∣ seq x 1 ∣ ℚ.+ 2ℚᵘ <⟨ proj₁ (proj₂ (least-ℤ>ℚ (ℚ.∣ seq x 1 ∣ ℚ.+ 2ℚᵘ))) ⟩
        (+ 1 ℤ.+ t) / 1       ≈⟨ ℚP.≃-reflexive (ℚP./-cong (sym (Kx=1+t x)) _≡_.refl _ _) ⟩
        + fK x / 1              ∎
        where open ℚP.≤-Reasoning

      right : ∀ (n : ℤ) -> ℚ.∣ seq x 1 ∣ ℚ.+ 2ℚᵘ ℚ.< n / 1 -> + fK x ℤ.≤ n
      right n hyp = let t = ↥ (ℚ.∣ seq x 1 ∣ ℚ.+ 2ℚᵘ) divℕ ↧ₙ (ℚ.∣ seq x 1 ∣ ℚ.+ 2ℚᵘ) in begin
        + fK x     ≡⟨ Kx=1+t x ⟩
        + 1 ℤ.+ t ≤⟨ proj₂ (proj₂ (least-ℤ>ℚ (ℚ.∣ seq x 1 ∣ ℚ.+ 2ℚᵘ))) n hyp ⟩
        n          ∎
      
        where open ℤP.≤-Reasoning

@0 canonical-strict-upper-bound : ∀ (x : ℝ) -> ∀ (n : ℕ) -> {n ≢0} -> ℚ.∣ seq x n ∣ ℚ.< + fK x / 1
canonical-strict-upper-bound x (suc k₁) = let n = suc k₁ in begin-strict
  ℚ.∣ seq x n ∣                               ≈⟨ ℚP.∣-∣-cong (solve 2 (λ xₙ x₁ ->
                                                 xₙ ⊜ (x₁ ⊕ (xₙ ⊖ x₁))) ℚP.≃-refl (seq x n) (seq x 1)) ⟩
  ℚ.∣ seq x 1 ℚ.+ (seq x n ℚ.- seq x 1)∣      ≤⟨ ℚP.∣p+q∣≤∣p∣+∣q∣ (seq x 1) (seq x n ℚ.- seq x 1) ⟩
  ℚ.∣ seq x 1 ∣ ℚ.+ ℚ.∣ seq x n ℚ.- seq x 1 ∣ ≤⟨ ℚP.+-monoʳ-≤ ℚ.∣ seq x 1 ∣ (reg x n 1) ⟩
  ℚ.∣ seq x 1 ∣ ℚ.+ (+ 1 / n ℚ.+ ℚ.1ℚᵘ)       ≤⟨ ℚP.+-monoʳ-≤ ℚ.∣ seq x 1 ∣ (ℚP.+-monoˡ-≤ ℚ.1ℚᵘ {+ 1 / n} {1ℚᵘ} (1/n≤1 n)) ⟩
  ℚ.∣ seq x 1 ∣ ℚ.+ 2ℚᵘ                       <⟨ proj₁ (canonical-well-defined x) ⟩
  + fK x / 1                                    ∎
  where
    open ℚP.≤-Reasoning
    open ℚ-Solver

-- Arithmetic operations

-- agda2hs doesn't like copatterns. Unfortunately for us. But this can be solved by doing some refactoring so that we use the constructor.
-- We will have to do this with many functions.
-- One more thing: there might be some extra parantheses added at the end of the function body. These have to be removed when restoring things to their original form.

-- The _⋆ function lifts a rational number into its real representation.
-- The sequence of p ⋆ is just the constant sequence (p).
-- But a renaming is needed...
toReal : ℚᵘ -> ℝ
-- seq (p ⋆) n = p
-- reg (p ⋆) (suc k₁) (suc k₂) =
toReal p = Mkℝ (λ _ → p) (λ @0 {(suc k₁) (suc k₂) →
  let m = suc k₁; n = suc k₂ in begin
  ℚ.∣ p ℚ.- p ∣       ≈⟨ ℚP.∣-∣-cong (ℚP.+-inverseʳ p) ⟩
  0ℚᵘ                 ≤⟨ ℚP.nonNegative⁻¹ _ ⟩
  + 1 / m ℚ.+ + 1 / n  ∎})
  where
    open ℚP.≤-Reasoning
{-# COMPILE AGDA2HS toReal #-}

-- This is needed for Num.
import Agda.Builtin.FromNat using (Number)

instance
  iℕNumber : Agda.Builtin.FromNat.Number ℕ
  -- Whether a natural number can be converted. But this is always true.
  Agda.Builtin.FromNat.Number.Constraint iℕNumber _ = ⊤

  Agda.Builtin.FromNat.Number.fromNat iℕNumber n = n

-- This is needed for Num either.
instance
  iℝNumber : Agda.Builtin.FromNat.Number ℝ

  -- Whether a natural number can be converted to ℝ. But this is always true.
  Agda.Builtin.FromNat.Number.Constraint iℝNumber _ = ⊤

  Agda.Builtin.FromNat.Number.fromNat iℝNumber n = toReal (+ n / 1)

instance
  -- I don't know why it moaned for that.
  -- Of course this needs to be fixed, but that can be done later.
  {-# TERMINATING #-}
  iℝNum : Num ℝ

  -- Whether we can subtract two numbers from each other. But it's always true.
  iℝNum .MinusOK _ _ = ⊤

  -- Whether we can negate a number. But this is always true either.
  iℝNum .NegateOK _ = ⊤

  -- Whether we can convert a given integer to a real.
  iℝNum .Haskell.Prim.Num.Num.FromIntegerOK _ = ⊤
  
  -- seq (x + y) n = seq x (2 ℕ.* n) ℚ.+ seq y (2 ℕ.* n)
  -- reg (x + y) (suc k₁) (suc k₂) = let m = suc k₁; n = suc k₂ in begin
  iℝNum ._+_ x y = Mkℝ (λ n → seq x (2 ℕ.* n) ℚ.+ seq y (2 ℕ.* n))
                (λ @0 {(suc k₁) (suc k₂) → let m = suc k₁; n = suc k₂ in begin
    ℚ.∣ seq x (2 ℕ.* m) ℚ.+ seq y (2 ℕ.* m) ℚ.-
       (seq x (2 ℕ.* n) ℚ.+ seq y (2 ℕ.* n)) ∣    ≈⟨ ℚP.∣-∣-cong (solve 4 (λ xₘ yₘ xₙ yₙ ->
                                                     xₘ ⊕ yₘ ⊖ (xₙ ⊕ yₙ) ⊜ (xₘ ⊖ xₙ ⊕ (yₘ ⊖ yₙ)))
                                                     ℚP.≃-refl (seq x (2 ℕ.* m)) (seq y (2 ℕ.* m)) (seq x (2 ℕ.* n)) (seq y (2 ℕ.* n))) ⟩
    ℚ.∣ seq x (2 ℕ.* m) ℚ.- seq x (2 ℕ.* n) ℚ.+
        (seq y (2 ℕ.* m) ℚ.- seq y (2 ℕ.* n)) ∣   ≤⟨ ℚP.∣p+q∣≤∣p∣+∣q∣ (seq x (2 ℕ.* m) ℚ.- seq x (2 ℕ.* n)) (seq y (2 ℕ.* m) ℚ.- seq y (2 ℕ.* n)) ⟩
    ℚ.∣ seq x (2 ℕ.* m) ℚ.- seq x (2 ℕ.* n) ∣ ℚ.+
    ℚ.∣ seq y (2 ℕ.* m) ℚ.- seq y (2 ℕ.* n) ∣     ≤⟨ ℚP.+-mono-≤ (reg x (2 ℕ.* m) (2 ℕ.* n)) (reg y (2 ℕ.* m) (2 ℕ.* n)) ⟩
    + 1 / (2 ℕ.* m) ℚ.+ + 1 / (2 ℕ.* n) ℚ.+
    (+ 1 / (2 ℕ.* m) ℚ.+ + 1 / (2 ℕ.* n))         ≈⟨ ℚ.*≡* (ℤsolve 2 (λ m n ->
                                                     (((κ (+ 1) :* (κ (+ 2) :* n) :+ κ (+ 1) :* (κ (+ 2) :* m))
                                                     :* ((κ (+ 2) :* m) :* (κ (+ 2) :* n))) :+
                                                     (κ (+ 1) :* (κ (+ 2) :* n) :+ κ (+ 1) :* (κ (+ 2) :* m))
                                                     :* ((κ (+ 2) :* m) :* (κ (+ 2) :* n))) :* (m :* n) :=
                                                     (κ (+ 1) :* n :+ κ (+ 1) :* m) :*
                                                     (((κ (+ 2) :* m) :* (κ (+ 2) :* n)) :*
                                                     (((κ (+ 2) :* m) :* (κ (+ 2) :* n)))))
                                                     _≡_.refl (+ m) (+ n)) ⟩
    + 1 / m ℚ.+ + 1 / n                            ∎})
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

  -- seq (- x) n = ℚ.- seq x n
  -- reg (- x) (suc k₁) (suc k₂) = let m = suc k₁; n = suc k₂ in begin
  iℝNum .negate x = Mkℝ (λ n → ℚ.- (seq x n)) (λ @0 { (suc k₁) (suc k₂) → let m = suc k₁; n = suc k₂ in begin
    ℚ.∣ ℚ.- seq x m ℚ.- ℚ.- seq x n ∣ ≈⟨ ℚP.∣-∣-cong (ℚP.≃-sym (ℚP.≃-reflexive (ℚP.neg-distrib-+ (seq x m) (ℚ.- seq x n)))) ⟩
    ℚ.∣ ℚ.- (seq x m ℚ.- seq x n) ∣   ≤⟨ ℚP.≤-respˡ-≃ (ℚP.≃-sym (ℚP.∣-p∣≃∣p∣ (seq x m ℚ.- seq x n))) (reg x m n) ⟩
    + 1 / m ℚ.+ + 1 / n                ∎})
    where open ℚP.≤-Reasoning

  iℝNum ._-_ x y = x + negate y

  -- seq (x * y) n = seq x (2 ℕ.* (fK x ℕ.⊔ fK y) ℕ.* n) ℚ.* seq y (2 ℕ.* (fK x ℕ.⊔ fK y) ℕ.* n)
  -- reg (x * y) (suc k₁) (suc k₂) =
  iℝNum ._*_ x y = Mkℝ (λ n → seq x (2 ℕ.* (fK x ℕ.⊔ fK y) ℕ.* n) ℚ.* seq y (2 ℕ.* (fK x ℕ.⊔ fK y) ℕ.* n)) (λ @0 {(suc k₁) (suc k₂) → let m = suc k₁; n = suc k₂; k = fK x ℕ.⊔ fK y; 2km = 2 ℕ.* k ℕ.* m; 2kn = 2 ℕ.* k ℕ.* n ; x₂ₖₘ = seq x 2km; y₂ₖₘ = seq y 2km; x₂ₖₙ = seq x 2kn; y₂ₖₙ = seq y 2kn ; ∣x₂ₖₘ∣≤k = ℚP.≤-trans (ℚP.<⇒≤ (canonical-strict-upper-bound x 2km)) (p≤r⇒p/q≤r/q (+ fK x) (+ k) 1 (ℤP.i≤i⊔j (+ fK x) (+ fK y))) ; ∣y₂ₖₙ∣≤k = ℚP.≤-trans (ℚP.<⇒≤ (canonical-strict-upper-bound y 2kn)) (p≤r⇒p/q≤r/q (+ fK y) (+ k) 1 (ℤP.i≤j⊔i (+ fK x) (+ fK y))) in
                                        begin
    ℚ.∣ x₂ₖₘ ℚ.* y₂ₖₘ ℚ.- x₂ₖₙ ℚ.* y₂ₖₙ ∣        ≈⟨ ℚP.∣-∣-cong (solve 4 (λ xm ym xn yn ->
                                                    (xm ⊗ ym ⊖ xn ⊗ yn) ⊜
                                                    (xm ⊗ (ym ⊖ yn) ⊕ yn ⊗ (xm ⊖ xn)))
                                                    ℚP.≃-refl x₂ₖₘ y₂ₖₘ x₂ₖₙ y₂ₖₙ) ⟩
    ℚ.∣ x₂ₖₘ ℚ.* (y₂ₖₘ ℚ.- y₂ₖₙ) ℚ.+
        y₂ₖₙ ℚ.* (x₂ₖₘ ℚ.- x₂ₖₙ) ∣              ≤⟨ ℚP.∣p+q∣≤∣p∣+∣q∣ (x₂ₖₘ ℚ.* (y₂ₖₘ ℚ.- y₂ₖₙ))
                                                                  (y₂ₖₙ ℚ.* (x₂ₖₘ ℚ.- x₂ₖₙ)) ⟩
    ℚ.∣ x₂ₖₘ ℚ.* (y₂ₖₘ ℚ.- y₂ₖₙ) ∣ ℚ.+
    ℚ.∣ y₂ₖₙ ℚ.* (x₂ₖₘ ℚ.- x₂ₖₙ) ∣              ≈⟨ ℚP.+-cong (ℚP.∣p*q∣≃∣p∣*∣q∣ x₂ₖₘ (y₂ₖₘ ℚ.- y₂ₖₙ)) (ℚP.∣p*q∣≃∣p∣*∣q∣ y₂ₖₙ (x₂ₖₘ ℚ.- x₂ₖₙ)) ⟩
    ℚ.∣ x₂ₖₘ ∣ ℚ.* ℚ.∣ y₂ₖₘ ℚ.- y₂ₖₙ ∣ ℚ.+
    ℚ.∣ y₂ₖₙ ∣ ℚ.* ℚ.∣ x₂ₖₘ ℚ.- x₂ₖₙ ∣           ≤⟨ ℚP.+-mono-≤
                                                    (ℚP.*-monoˡ-≤-nonNeg {ℚ.∣ y₂ₖₘ ℚ.- y₂ₖₙ ∣} _ ∣x₂ₖₘ∣≤k)
                                                    (ℚP.*-monoˡ-≤-nonNeg {ℚ.∣ x₂ₖₘ ℚ.- x₂ₖₙ ∣} _ ∣y₂ₖₙ∣≤k) ⟩
    (+ k / 1) ℚ.* ℚ.∣ y₂ₖₘ ℚ.- y₂ₖₙ ∣ ℚ.+
    (+ k / 1) ℚ.* ℚ.∣ x₂ₖₘ ℚ.- x₂ₖₙ ∣           ≤⟨ ℚP.+-mono-≤
                                                   (ℚP.*-monoʳ-≤-nonNeg {+ k / 1} _ (reg y 2km 2kn))
                                                   (ℚP.*-monoʳ-≤-nonNeg {+ k / 1} _ (reg x 2km 2kn)) ⟩
    (+ k / 1) ℚ.* ((+ 1 / 2km) ℚ.+
    (+ 1 / 2kn)) ℚ.+
    (+ k / 1) ℚ.* ((+ 1 / 2km) ℚ.+
    (+ 1 / 2kn))                               ≈⟨ ℚP.≃-sym (ℚP.*-distribˡ-+ (+ k / 1) ((+ 1 / 2km) ℚ.+ (+ 1 / 2kn)) ((+ 1 / 2km) ℚ.+ (+ 1 / 2kn))) ⟩

    (+ k / 1) ℚ.* ((+ 1 / 2km) ℚ.+ (+ 1 / 2kn)
    ℚ.+ ((+ 1 / 2km) ℚ.+ (+ 1 / 2kn)))         ≈⟨ ℚ.*≡* (ℤsolve 3 (λ k m n ->

    {- Function for the solver -}
    ((k :* ((((κ (+ 1) :* (κ (+ 2) :* k :* n)) :+ (κ (+ 1) :* (κ (+ 2) :* k :* m))) :* ((κ (+ 2) :* k :* m) :* (κ (+ 2) :* k :* n))) :+
    (((κ (+ 1) :* (κ (+ 2) :* k :* n)) :+ (κ (+ 1) :* (κ (+ 2) :* k :* m))) :* ((κ (+ 2) :* k :* m) :* (κ (+ 2) :* k :* n)))))
    :* (m :* n)) :=
    ((κ (+ 1) :* n :+ κ (+ 1) :* m) :*
    (κ (+ 1) :* (((κ (+ 2) :* k :* m) :* (κ (+ 2) :* k :* n)):* ((κ (+ 2) :* k :* m) :* (κ (+ 2) :* k :* n))))))
    -- Other solver inputs
    refl (+ k) (+ m) (+ n)) ⟩

    (+ 1 / m) ℚ.+ (+ 1 / n)                     ∎})
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

  -- seq ∣ x ∣ n = ℚ.∣ seq x n ∣
  -- reg ∣ x ∣ (suc k₁) (suc k₂) =
  iℝNum .abs x = Mkℝ (λ n → ℚ.∣ seq x n ∣) (λ @0 {(suc k₁) (suc k₂) → let m = suc k₁; n = suc k₂ in begin
    ℚ.∣ ℚ.∣ seq x m ∣ ℚ.- ℚ.∣ seq x n ∣ ∣ ≤⟨ ∣∣p∣-∣q∣∣≤∣p-q∣ (seq x m) (seq x n) ⟩
    ℚ.∣ seq x m ℚ.- seq x n ∣            ≤⟨ reg x m n ⟩
    + 1 / m ℚ.+ + 1 / n                   ∎})
    where open ℚP.≤-Reasoning

  iℝNum .fromInteger z = toReal (z / 1)

  -- And this is going to be the problematic one.
  -- Since we cannot determine whether a real number is greater than zero, we cannot really write anything meaningful here.
  -- But we cannot fail either... so let's do this.
  iℝNum .signum _ = fromInteger (+ 42)
{-# COMPILE AGDA2HS iℝNum #-}

{-
-- It does complain for this one too... this time for the name.
_-_ : ℝ -> ℝ -> ℝ
x - y = x + negate y

-- Let's go cheating for now.
{-# FOREIGN AGDA2HS
  (-) :: ℝ -> ℝ -> ℝ
  x - y = x + negate y
#-}
-}

-- x ⊔ y is the maximum of x and y.
-- Here I had to create a new helper called `reg-main` so that the where clause can access the parameters.
-- But it complains for the type, although it is erased...
-- Jesper said he would take a look at it. See https://github.com/agda/agda2hs/issues/182.
_⊔_ : ℝ -> ℝ -> ℝ
-- seq (x ⊔ y) n = (seq x n) ℚ.⊔ (seq y n)
-- reg (x ⊔ y) (suc k₁) (suc k₂) = [ left , right ]′ (ℚP.≤-total (seq x m ℚ.⊔ seq y m) (seq x n ℚ.⊔ seq y n))
x ⊔ y = Mkℝ (λ n → (seq x n) ℚ.⊔ (seq y n)) reg_main
  where
  @0 reg_main : (m n : ℕ) {@0 m≢0 : m ≢0} {@0 n≢0 : n ≢0} →
      ℚ.∣ seq x m ℚ.⊔ seq y m ℚ.- (seq x n ℚ.⊔ seq y n) ∣ ℚ.≤
      + 1 / m ℚ.+ + 1 / n
  reg_main (suc k₁) (suc k₂) = [ left , right ]′ (ℚP.≤-total (seq x m ℚ.⊔ seq y m) (seq x n ℚ.⊔ seq y n))
    where
    open ℚP.≤-Reasoning
    open ℚ-Solver
    @0 m n : ℕ
    m = suc k₁
    n = suc k₂

    @0 lem : ∀ (a b c d : ℚᵘ) -> a ℚ.≤ b -> ∀ (r s : ℕ) -> {r≢0 : r ≢0} -> {s≢0 : s ≢0} ->
                               ℚ.∣ b ℚ.- d ∣ ℚ.≤ ((+ 1) / r) {r≢0} ℚ.+ ((+ 1) / s) {s≢0} ->
                               (a ℚ.⊔ b) ℚ.- (c ℚ.⊔ d) ℚ.≤ ((+ 1) / r) {r≢0} ℚ.+ ((+ 1) / s) {s≢0} 
    lem a b c d a≤b r s hyp = begin
      (a ℚ.⊔ b) ℚ.- (c ℚ.⊔ d)     ≤⟨ ℚP.+-monoʳ-≤ (a ℚ.⊔ b) (ℚP.neg-mono-≤ (ℚP.p≤q⊔p c d)) ⟩
      (a ℚ.⊔ b) ℚ.- d             ≈⟨ ℚP.+-congˡ (ℚ.- d) (ℚP.p≤q⇒p⊔q≃q a≤b) ⟩
      b ℚ.- d                     ≤⟨ p≤∣p∣ (b ℚ.- d) ⟩
      ℚ.∣ b ℚ.- d ∣               ≤⟨ hyp ⟩
      ((+ 1) / r) ℚ.+ ((+ 1) / s)  ∎

    @0 left : seq x m ℚ.⊔ seq y m ℚ.≤ seq x n ℚ.⊔ seq y n ->
           ℚ.∣ (seq x m ℚ.⊔ seq y m) ℚ.- (seq x n ℚ.⊔ seq y n) ∣ ℚ.≤ ((+ 1) / m) ℚ.+ ((+ 1) / n)
    left hyp1 = [ xn≤yn , yn≤xn ]′ (ℚP.≤-total (seq x n) (seq y n))
      where
        xn≤yn : seq x n ℚ.≤ seq y n -> ℚ.∣ (seq x m ℚ.⊔ seq y m) ℚ.- (seq x n ℚ.⊔ seq y n) ∣ ℚ.≤ ((+ 1) / m) ℚ.+ ((+ 1) / n)
        xn≤yn hyp2 = begin
          ℚ.∣ (seq x m ℚ.⊔ seq y m) ℚ.- (seq x n ℚ.⊔ seq y n) ∣ ≈⟨ ℚP.≃-trans (ℚP.≃-sym (ℚP.∣-p∣≃∣p∣ ((seq x m ℚ.⊔ seq y m) ℚ.- (seq x n ℚ.⊔ seq y n))))
                                                                  (ℚP.∣-∣-cong (solve 2 (λ a b -> (⊝ (a ⊖ b)) ⊜ (b ⊖ a))
                                                                  ℚP.≃-refl (seq x m ℚ.⊔ seq y m) (seq x n ℚ.⊔ seq y n))) ⟩
          ℚ.∣ (seq x n ℚ.⊔ seq y n) ℚ.- (seq x m ℚ.⊔ seq y m) ∣ ≈⟨ ℚP.0≤p⇒∣p∣≃p (ℚP.p≤q⇒0≤q-p hyp1) ⟩
          (seq x n ℚ.⊔ seq y n) ℚ.- (seq x m ℚ.⊔ seq y m)       ≤⟨ lem (seq x n) (seq y n) (seq x m) (seq y m) hyp2 m n
                                                                   (ℚP.≤-respʳ-≃ (ℚP.+-comm (+ 1 / n) (+ 1 / m)) (reg y n m)) ⟩
          (+ 1 / m) ℚ.+ (+ 1 / n)                                ∎ 

        yn≤xn : seq y n ℚ.≤ seq x n -> ℚ.∣ (seq x m ℚ.⊔ seq y m) ℚ.- (seq x n ℚ.⊔ seq y n) ∣ ℚ.≤ ((+ 1) / m) ℚ.+ ((+ 1) / n)
        yn≤xn hyp2 = begin
          ℚ.∣ (seq x m ℚ.⊔ seq y m) ℚ.- (seq x n ℚ.⊔ seq y n) ∣ ≈⟨ ℚP.≃-trans (ℚP.≃-sym (ℚP.∣-p∣≃∣p∣ ((seq x m ℚ.⊔ seq y m) ℚ.- (seq x n ℚ.⊔ seq y n))))
                                                                  (ℚP.∣-∣-cong (solve 2 (λ a b -> (⊝ (a ⊖ b)) ⊜ (b ⊖ a))
                                                                  ℚP.≃-refl (seq x m ℚ.⊔ seq y m) (seq x n ℚ.⊔ seq y n))) ⟩
          ℚ.∣ (seq x n ℚ.⊔ seq y n) ℚ.- (seq x m ℚ.⊔ seq y m) ∣ ≈⟨ ℚP.0≤p⇒∣p∣≃p (ℚP.p≤q⇒0≤q-p hyp1) ⟩
          (seq x n ℚ.⊔ seq y n) ℚ.- (seq x m ℚ.⊔ seq y m)       ≈⟨ ℚP.≃-trans (ℚP.+-congʳ (seq x n ℚ.⊔ seq y n)
                                                                   (ℚP.-‿cong {seq x m ℚ.⊔ seq y m} {seq y m ℚ.⊔ seq x m} (ℚP.⊔-comm (seq x m) (seq y m))))
                                                                   (ℚP.+-congˡ (ℚ.- (seq y m ℚ.⊔ seq x m)) (ℚP.⊔-comm (seq x n) (seq y n))) ⟩
          (seq y n ℚ.⊔ seq x n) ℚ.- (seq y m ℚ.⊔ seq x m) 
                                                                ≤⟨ lem (seq y n) (seq x n) (seq y m) (seq x m) hyp2 m n
                                                                   (ℚP.≤-respʳ-≃ (ℚP.+-comm (+ 1 / n) (+ 1 / m)) (reg x n m)) ⟩
          (+ 1 / m) ℚ.+ (+ 1 / n)                                ∎

    @0 right : seq x n ℚ.⊔ seq y n ℚ.≤ seq x m ℚ.⊔ seq y m ->
            ℚ.∣ (seq x m ℚ.⊔ seq y m) ℚ.- (seq x n ℚ.⊔ seq y n) ∣ ℚ.≤ ((+ 1) / m) ℚ.+ ((+ 1) / n)
    right hyp1 = [ xm≤ym , ym≤xm ]′ (ℚP.≤-total (seq x m) (seq y m))
      where
        xm≤ym : seq x m ℚ.≤ seq y m -> ℚ.∣ (seq x m ℚ.⊔ seq y m) ℚ.- (seq x n ℚ.⊔ seq y n) ∣ ℚ.≤ ((+ 1) / m) ℚ.+ ((+ 1) / n)
        xm≤ym hyp2 = ℚP.≤-respˡ-≃ (ℚP.≃-sym (ℚP.0≤p⇒∣p∣≃p (ℚP.p≤q⇒0≤q-p hyp1))) (lem (seq x m) (seq y m) (seq x n) (seq y n) hyp2 m n (reg y m n)) 

        ym≤xm : seq y m ℚ.≤ seq x m -> ℚ.∣ (seq x m ℚ.⊔ seq y m) ℚ.- (seq x n ℚ.⊔ seq y n) ∣ ℚ.≤ ((+ 1) / m) ℚ.+ ((+ 1) / n)
        ym≤xm hyp2 = begin
           ℚ.∣ (seq x m ℚ.⊔ seq y m) ℚ.- (seq x n ℚ.⊔ seq y n) ∣ ≈⟨ ℚP.0≤p⇒∣p∣≃p (ℚP.p≤q⇒0≤q-p hyp1) ⟩
           (seq x m ℚ.⊔ seq y m) ℚ.- (seq x n ℚ.⊔ seq y n)       ≈⟨ ℚP.≃-trans (ℚP.+-congˡ (ℚ.- (seq x n ℚ.⊔ seq y n)) (ℚP.⊔-comm (seq x m) (seq y m)))
                                                                    (ℚP.+-congʳ (seq y m ℚ.⊔ seq x m)
                                                                    (ℚP.-‿cong {seq x n ℚ.⊔ seq y n} {seq y n ℚ.⊔ seq x n} (ℚP.⊔-comm (seq x n) (seq y n)))) ⟩
           (seq y m ℚ.⊔ seq x m) ℚ.- (seq y n ℚ.⊔ seq x n)       ≤⟨ lem (seq y m) (seq x m) (seq y n) (seq x n) hyp2 m n (reg x m n) ⟩
           (+ 1 / m) ℚ.+ (+ 1 / n)                                                      ∎
-- {-# COMPILE AGDA2HS _⊔_ #-}

-- x ⊓ y is the minimum of x and y.
-- This seems to be more agda2hs-compatible. What if we rewrote _⊔_ too?
_⊓_ : ℝ -> ℝ -> ℝ
-- seq (x ⊓ y) n = seq x n ℚ.⊓ seq y n
-- reg (x ⊓ y) (suc k₁) (suc k₂) =
x ⊓ y = Mkℝ (λ n → seq x n ℚ.⊓ seq y n) (λ @0 {(suc k₁) (suc k₂) →
  let m = suc k₁; n = suc k₂; xₘ = seq x m; yₘ = seq y m; xₙ = seq x n; yₙ = seq y n in begin
  ℚ.∣ xₘ ℚ.⊓ yₘ ℚ.- xₙ ℚ.⊓ yₙ ∣               ≈⟨ ℚP.∣-∣-cong (ℚP.+-cong
                                                 (ℚP.⊓-cong (ℚP.≃-sym (ℚP.neg-involutive xₘ)) (ℚP.≃-sym (ℚP.neg-involutive yₘ)))
                                                 (ℚP.-‿cong (ℚP.⊓-cong (ℚP.≃-sym (ℚP.neg-involutive xₙ)) (ℚP.≃-sym (ℚP.neg-involutive yₙ))))) ⟩
  ℚ.∣ ((ℚ.- (ℚ.- xₘ)) ℚ.⊓ (ℚ.- (ℚ.- yₘ))) ℚ.-
      ((ℚ.- (ℚ.- xₙ)) ℚ.⊓ (ℚ.- (ℚ.- yₙ))) ∣   ≈⟨ ℚP.∣-∣-cong (ℚP.+-cong
                                                 (ℚP.≃-sym (ℚP.neg-distrib-⊔-⊓ (ℚ.- xₘ) (ℚ.- yₘ)))
                                                 (ℚP.-‿cong (ℚP.≃-sym (ℚP.neg-distrib-⊔-⊓ (ℚ.- xₙ) (ℚ.- yₙ))))) ⟩
  ℚ.∣ ℚ.- ((ℚ.- xₘ) ℚ.⊔ (ℚ.- yₘ)) ℚ.-
     (ℚ.- ((ℚ.- xₙ) ℚ.⊔ (ℚ.- yₙ))) ∣          ≈⟨ ℚP.∣-∣-cong (solve 2 (λ m n -> ((⊝ m) ⊖ (⊝ n)) ⊜ (n ⊖ m)) ℚP.≃-refl ((ℚ.- xₘ) ℚ.⊔ (ℚ.- yₘ)) ((ℚ.- xₙ) ℚ.⊔ (ℚ.- yₙ))) ⟩
  ℚ.∣ ((ℚ.- xₙ) ℚ.⊔ (ℚ.- yₙ)) ℚ.-
      ((ℚ.- xₘ) ℚ.⊔ (ℚ.- yₘ)) ∣               ≤⟨ reg (negate x ⊔ negate y) n m ⟩
  + 1 / n ℚ.+ + 1 / m                         ≈⟨ ℚP.+-comm (+ 1 / n) (+ 1 / m) ⟩
  + 1 / m ℚ.+ + 1 / n                          ∎})
  where
    open ℚP.≤-Reasoning
    open ℚ-Solver
{-# COMPILE AGDA2HS _⊓_ #-}


-- An alternative (but equivalent) definition of minimum for convenience.
_⊓₂_ : ℝ -> ℝ -> ℝ
x ⊓₂ y = negate ((negate x) ⊔ (negate y))

-- Identities
zeroℝ : ℝ
zeroℝ = toReal (+ 0 / 1)
{-# COMPILE AGDA2HS zeroℝ #-}

oneℝ : ℝ
oneℝ = toReal (+ 1 / 1)
{-# COMPILE AGDA2HS oneℝ #-}

-- Exponentiation for natural powers
-- Beware: this gets stuck for strangify (+ 1 / 2), at least when we get the denominator of an element of the rational sequence!
pow : ℝ -> ℕ -> ℝ
pow x 0 = oneℝ
pow x (suc n) = pow x n * x
-- And now a nasty trick for fast exponentiation.
-- Maybe we should prove the correctness of this sometime. Well, we should.
{-# FOREIGN AGDA2HS
  pow :: ℝ -> Natural -> ℝ
  pow x n = go x n oneℝ
    where
      go :: ℝ -> Natural -> ℝ -> ℝ
      go base 0 res = res
      go base exp res = go (base * base) (exp ℕD./ 2) (if (even exp) then res else res * base)
#-}
-- Or if we opt for fairness:
-- {-# COMPILE AGDA2HS pow #-}

-- Maximum over a sequence
{-
Taking the max over a sequence instead of over a list for convenience.
It seems to make it easier to take the max over a list of a variable length n, since I don't
think we can write x₁ :: x₂ :: ... :: xₙ :: nil in Agda. 
For an example of this, see the convergent⇒bounded proof, particularly the part where M is defined.
-}
max : (ℕ → ℝ) → (n : ℕ) → ℝ
max f 0 = f 0
max f (suc n) = max f n ⊔ f (suc n)
-- {-# COMPILE AGDA2HS max #-}      -- we would need _⊔_ for this

-- We will have to use Σ0 instead of ∃0 and MkΣ0 instead of _,_.
-- But I think this is bearable.

-- Sign predicates
-- Have to use this syntax instead of Pred.
-- And of course, MkPos instead of pos*.
data Positive (@0 x : ℝ) : Set where              -- this is it! it can be erased too
  MkPos : (Σ0 ℕ (λ (n-1 : ℕ) -> seq x (suc n-1) ℚ.> + 1 / (suc n-1))) -> Positive x
{-# COMPILE AGDA2HS Positive newtype #-}

data NonNegative : Pred ℝ 0ℓ where
  nonNeg* : ∀ {x} -> @0 (∀ (n : ℕ) -> {n≢0 : n ≢0} -> seq x n ℚ.≥ ℚ.- ((+ 1 / n) {n≢0})) -> NonNegative x
-- I think this doesn't need to be compiled

Negative : (@0 x : ℝ) → Set
Negative x = Positive (negate x)
{-# COMPILE AGDA2HS Negative #-}

-- Ordering of ℝ
infix 4 _<_ _>_ _≤_ _≥_

-- Now this nasty one. This must be compiled, but (<) cannot be a type name in Haskell.
-- At least in standard Haskell;)
-- What about this?
-- {-# FOREIGN AGDA2HS {-# LANGUAGE TypeOperators #-} #-}
_<_ : Rel ℝ 0ℓ
x < y = Positive (y - x)
-- {-# COMPILE AGDA2HS _<_ #-}
{-
{-# FOREIGN AGDA2HS
  type (<) = Positive -- this doesn't work; the parantheses disappear
                      -- but it would work if the parantheses were left there
#-}
-}
-- well, this remains a TODO

_>_ : Rel ℝ 0ℓ
x > y = y < x

_≤_ : Rel ℝ 0ℓ
x ≤ y = NonNegative (y - x)

_≥_ : Rel ℝ 0ℓ
x ≥ y = y ≤ x

_≄_ : Rel ℝ 0ℓ
x ≄ y = x < y ⊎ y < x

_≄0 : ℝ -> Set
x ≄0 = x ≄ zeroℝ

_<_<_ : (x y z : ℝ) -> Set
x < y < z = (x < y) × (y < z)

_<_≤_ : (x y z : ℝ) -> Set
x < y ≤ z = (x < y) × (y ≤ z)

_≤_<_ : (x y z : ℝ) -> Set
x ≤ y < z = (x ≤ y) × (y < z)

_≤_≤_ : (x y z : ℝ) -> Set
x ≤ y ≤ z = (x ≤ y) × (y ≤ z)

_≮_ : Rel ℝ 0ℓ
x ≮ y = ¬ (x < y)

_≰_ : Rel ℝ 0ℓ
x ≰ y = ¬ (x ≤ y)

_≱_ : Rel ℝ 0ℓ
x ≱ y = y ≰ x

-- Summations
-- Again a renaming...
sum0 : (ℕ -> ℝ) -> ℕ -> ℝ
sum0 a 0 = zeroℝ
sum0 a (suc n) = sum0 a n + a n
-- And cannot pattern match here. So let's cheat.
{-# FOREIGN AGDA2HS
  sum0 :: (Natural -> ℝ) -> Natural -> ℝ
  sum0 a n = if (n == 0) then zeroℝ else (sum0 a (n-1) + a (n-1))
#-}

sum : (ℕ -> ℝ) -> ℕ -> ℕ -> ℝ
sum a 0 n = sum0 a n
sum a (suc i) n = sum0 a n - sum0 a (suc i)
{-# FOREIGN AGDA2HS
  sum :: (Natural -> ℝ) -> Natural -> Natural -> ℝ
  sum a i n = if (i == 0) then (sum0 a n) else (sum0 a n - sum0 a i)
#-}
