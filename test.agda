{-# OPTIONS --without-K #-}

module test where

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

open import ExtraProperties
open import Real
open import RealProperties
-- open import Inverse

postulate cheat : ∀{i}{A : Set i} → A

Nₐ : (x : ℝ) -> (x≄0 : x ≄0) ->  ℕ
Nₐ x x≄0 = suc (proj₁ (lemma-2-8-1-if {∣ x ∣} (x≄0⇒pos∣x∣ {x} x≄0)))

_⁻¹ : (x : ℝ) -> (x≄0 : x ≄ 0ℝ) -> ℝ
seq ((x ⁻¹) x≄0) n = (ℚ.1/ xₛ) {cheat}
  where
    N = 3
    -- N = Nₐ x x≄0
    xₛ = seq x ((n ℕ.+ N) ℕ.* (N ℕ.* N))
reg ((x ⁻¹) x≄0) _ _ = cheat



strange1 : ℝ
-- seq strange1 n = 1ℚᵘ
-- seq strange1 n = + n / 1
-- seq strange1 n = + 0 / suc n
seq strange1 n = + 1 / suc n
-- seq strange1 n = 1ℚᵘ ℚ.+ (+ 1 / suc n)
reg strange1 m n = {!!}
  
postulate
  w : strange1 ≄ 0ℝ

asdf : ℚᵘ
asdf = seq ((strange1 ⁻¹) w) 0
