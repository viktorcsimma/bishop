{-# OPTIONS --without-K #-}

module Test where

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
{-
--branch 1

tarchimedean-ℚ : ∀ p r -> ℚ.Positive p -> ∃ λ (N : ℕ) -> r ℚ.< ((+ N) ℤ.* ↥ p) / (↧ₙ p)
tarchimedean-ℚ (mkℚᵘ +[1+ g ] q-1) (mkℚᵘ u v-1) _ = suc ℤ.∣ (u ℤ.* + (suc q-1)) divℕ ((suc g) ℕ.* (suc v-1)) ∣ , cheat

{-
--this is fine
testarch : ℕ
testarch = proj₁ (tarchimedean-ℚ (+ 1 / 2) (+ 10000 / 3) _)
-}

noabst-archimedean-ℚ₂ : ∀ (p : ℚᵘ) -> ∀ (r : ℤ) -> ℚ.Positive p -> ∃ λ (N-1 : ℕ) -> r / (suc N-1) ℚ.< p
noabst-archimedean-ℚ₂ (mkℚᵘ (+_ p) q-1) r posp/q = proj₁ (tarchimedean-ℚ (+ p / (suc q-1)) (r / 1) posp/q) , cheat

noabst-lemma-2-8-1-if : ∀ {x} -> Positive x -> ∃ λ (N-1 : ℕ) -> ∀ (m : ℕ) -> m ℕ.≥ suc N-1 -> seq x m ℚ.≥ + 1 / (suc N-1)
noabst-lemma-2-8-1-if {x} (pos* (n-1 , posx)) = let n = suc n-1 in (proj₁ (noabst-archimedean-ℚ₂ (seq x n ℚ.- + 1 / n) (+ 2) (ℚ.positive (p<q⇒0<q-p (+ 1 / n) (seq x n) posx))) , cheat)

--branch 2
{-
x-0≃x : ∀ {x} -> x - 0ℝ ≃ x
x-0≃x {x} = ≃-trans (+-congʳ x (≃-symm 0≃-0)) (+-identityʳ x)

t0<x⇒posx : ∀ {x} -> 0ℝ < x -> Positive x
t0<x⇒posx {x} 0<x = pos-cong x-0≃x 0<x

tx≄0⇒pos∣x∣ : ∀ {x} -> x ≄0 -> Positive ∣ x ∣
tx≄0⇒pos∣x∣ {x} x≄0 = t0<x⇒posx (x≄0⇒0<∣x∣ x≄0)
-}

-}
Nₐ : (x : ℝ) -> (x≄0 : x ≄0) ->  ℕ
Nₐ x x≄0 = suc (proj₁ (lemma-2-8-1-if {∣ x ∣} (x≄0⇒pos∣x∣ {x} cheat)))

_⁻¹ : (x : ℝ) -> (x≄0 : x ≄ 0ℝ) -> ℝ
seq ((x ⁻¹) x≄0) n = (ℚ.1/ xₛ) {cheat}
  where
    N = Nₐ x x≄0
    xₛ = seq x ((n ℕ.+ N) ℕ.* (N ℕ.* N))
reg ((x ⁻¹) x≄0) _ _ = cheat



strange1 : ℝ
-- seq strange1 n = 1ℚᵘ
-- seq strange1 n = + n / 1
-- seq strange1 n = + 0 / suc n
-- seq strange1 n = + 1 / suc n
seq strange1 n = 1ℚᵘ ℚ.+ (+ 1 / suc n)
reg strange1 m n = cheat

tonormalise : ℚᵘ
tonormalise = seq ((strange1 ⁻¹) cheat) 100
