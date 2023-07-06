-- A planned function for a modular exponentiation function.
-- Created because pow (strangify (+ 1 / 2)) seems to hang when trying to take a denominator of a member of the sequence.

{-# OPTIONS --without-K #-}

module FastPow where

open import Algebra
open import Data.Bool.Base using (Bool; if_then_else_)
open import Function.Base using (_∘_)
open import Data.Integer.Base as ℤ using (ℤ; +_; +0; +[1+_]; -[1+_])
import Data.Integer.Properties as ℤP
open import Data.Integer.DivMod as ℤD
open import Data.Nat as ℕ using (ℕ; zero; suc)
open import Data.Nat.Properties as ℕP using (≤-step)
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

open import ErasureProduct
open import ExtraProperties
open import Real
open import RealProperties

open import Data.Nat.DivMod as ℕD

even : ℕ → Bool
even n = is0 (n % 2)
  where
    is0 : ℕ → Bool
    is0 zero = Bool.true
    is0 _    = Bool.false

-- https://en.wikipedia.org/wiki/Modular_exponentiation
-- Postulating termination for now.
{-# TERMINATING #-}
fast-pow : ℝ → ℕ → ℝ
fast-pow x n = go x n 1ℝ
  where
    go : ℝ → ℕ → ℝ → ℝ
    go base zero res = res
    go base exp res = go (base * base) (exp ℕD./ 2) (if (even exp) then res else res * base)

-- Postulating correctness for now.
postulate
  @0 fast-pow≃pow : ∀ (x : ℝ) (n : ℕ) → fast-pow x n ≃ pow x n
