-- A number of basic properties regarding the real numbers.
-- Note that these properties are only for the operations defined in
-- Real.agda. For definitions and properties regarding inverses, see Inverse.agda.

-- {-# OPTIONS --without-K --safe #-}

module RealProperties where

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
open import Data.Rational.Unnormalised as ℚ using (ℚᵘ; mkℚᵘ; _≢0; _/_; ↥_; ↧_; ↧ₙ_)
import Data.Rational.Unnormalised.Properties as ℚP
open import Algebra.Bundles
open import Algebra.Structures
open import Data.Empty
open import Data.Sum
open import Data.Maybe.Base
import NonReflectiveQ as ℚ-Solver
import NonReflectiveZ as ℤ-Solver
open import Data.List hiding (sum)

open import Agda.Builtin.Unit
open import Haskell.Prim.Either
open import Haskell.Prim.Num
import Haskell.Prim.Tuple as Tuple

open import ErasureProduct
open import ExtraProperties
open import Real

{-
-- Here is a test code which demonstrates where erasure did not work:

@0 testf : @0 ℕ → ℕ
-- testf = λ { zero → zero ; (suc n) → (suc n)} -- This does not work...
testf zero = zero
testf (suc n) = suc n -- ...but this does

-- The solution is to write an @0 before the curly brace too:
-- testf = λ @0 { zero → zero ; (suc n) → (suc n)}
-- See Agda issue #6430: https://github.com/agda/agda/issues/6430.
-}

-- Actually, for the proofs we can use an alias with the old operators.
@0 _⋆ : ℚᵘ → ℝ
_⋆ = toReal
@0 -_ : ℝ → ℝ
- x = negate x                 -- Here it moans because of the proof argument of negate.
@0 ∣_∣ : ℝ → ℝ
∣_∣ = abs
infix 8 _⋆ -_

-- Properties to show real equality is an equivalence relation

≃-refl : Reflexive _≃_
≃-refl {x} = *≃* λ { (suc k₁) → let n = suc k₁ in begin
  ℚ.∣ seq x n ℚ.- seq x n ∣ ≈⟨ ℚP.∣-∣-cong (ℚP.+-inverseʳ (seq x n)) ⟩
  (+ 0 / 1)                       ≤⟨ ℚP.nonNegative⁻¹ _ ⟩
  + 2 / n                    ∎}
  where open ℚP.≤-Reasoning

≃-sym : Symmetric _≃_
≃-sym {x} {y} (*≃* x₁) = *≃* lem
  where
    @0 lem : (n : ℕ) {n≢0 : n ≢0} → ℚ.∣ seq y n ℚ.- seq x n ∣ ℚ.≤ + 2 / n
    lem (suc k) = let n = suc k in begin
        ℚ.∣ seq y n ℚ.- seq x n ∣ ≈⟨ ∣p-q∣≃∣q-p∣ (seq y n) (seq x n) ⟩
        ℚ.∣ seq x n ℚ.- seq y n ∣ ≤⟨ x₁ n ⟩
        + 2 / n                    ∎
      where
      open ℚP.≤-Reasoning

≃-reflexive : ∀ {x y} -> (∀ n -> {n ≢0} -> seq x n ℚ.≃ seq y n) -> x ≃ y
≃-reflexive {x} {y} hyp = *≃* (λ {(suc n-1) -> let n = suc n-1 in begin
  ℚ.∣ seq x n ℚ.- seq y n ∣ ≈⟨ ℚP.∣-∣-cong (ℚP.+-congʳ (seq x n) (ℚP.-‿cong (ℚP.≃-sym (hyp n)))) ⟩
  ℚ.∣ seq x n ℚ.- seq x n ∣ ≈⟨ ℚP.∣-∣-cong (ℚP.+-inverseʳ (seq x n)) ⟩
  (+ 0 / 1)                       ≤⟨ ℚP.nonNegative⁻¹ _ ⟩
  + 2 / n                    ∎})
  where open ℚP.≤-Reasoning

-- The following equality lemma is Lemma 2.3 in Bishop & Bridges.
-- It is used to prove that equality is transitive.
equalityLemmaIf : ∀ x y -> @0 (x ≃ y) -> ∀ (j : ℕ) -> {@0 j≢0 : j ≢0} ->
                  Σ0 ℕ λ (N : ℕ) -> ∀ (n : ℕ) -> n ℕ.≥ N ->
                  ℚ.∣ seq x n ℚ.- seq y n ∣ ℚ.≤ (+ 1 / j) {j≢0}
equalityLemmaIf x y (*≃* x₁) (suc k₁) = ((2 ℕ.* j) :&: lem)
  where
    open ℚP.≤-Reasoning
    j : ℕ
    j = suc k₁
    @0 lem : (n : ℕ) → n ℕ.≥ suc (k₁ ℕ.+ suc (k₁ ℕ.+ zero)) → ℚ.∣ seq x n ℚ.- seq y n ∣ ℚ.≤ mkℚᵘ (+ 1) k₁
    lem (suc k₂) n≥N = let N = 2 ℕ.* j ; n = suc k₂ in begin
        ℚ.∣ seq x n ℚ.- seq y n ∣ ≤⟨ x₁ n ⟩
        + 2 / n                   ≤⟨ ℚ.*≤* (ℤP.*-monoˡ-≤-nonNeg 2 (ℤ.+≤+ n≥N)) ⟩
        + 2 / N                   ≈⟨ ℚ.*≡* (sym (ℤP.*-identityˡ (+ 2 ℤ.* + j))) ⟩
        + 1 / j                     ∎

-- The compiled version does not pattern match on suc.
equalityLemmaIf' : ∀ x y -> @0 (x ≃ y) -> ∀ (j : ℕ) -> {@0 j≢0 : j ≢0} ->
                  Σ0 ℕ λ (N : ℕ) -> ⊤
equalityLemmaIf' _ _ (*≃* _) j = (2 ℕ.* j :&: tt)
{-# COMPILE AGDA2HS equalityLemmaIf' #-}

@0 proj₁equalityLemmaIf≡proj₁equalityLemmaIf' : ∀ x y -> (@0 x≃y : x ≃ y) -> ∀ (j : ℕ) -> {@0 j≢0 : j ≢0} ->
                                         proj₁ (equalityLemmaIf x y x≃y j {j≢0}) ≡ proj₁ (equalityLemmaIf' x y x≃y j {j≢0})
proj₁equalityLemmaIf≡proj₁equalityLemmaIf' _ _ (*≃* _) (suc k₁) = refl

abstract
  fastEqualityLemmaIf : ∀ x y -> @0 (x ≃ y) -> ∀ (j : ℕ) -> {@0 j≢0 : j ≢0} ->
                           Σ0 ℕ λ (N : ℕ) -> ∀ (n : ℕ) -> n ℕ.≥ N ->
                           ℚ.∣ seq x n ℚ.- seq y n ∣ ℚ.≤ (+ 1 / j) {j≢0}
  fastEqualityLemmaIf = equalityLemmaIf

equality-lemma-onlyif : ∀ x y ->
                        @0 (∀ (j : ℕ) -> {j≢0 : j ≢0} -> ∃ λ (N : ℕ) -> ∀ (n : ℕ) -> n ℕ.≥ N ->
                         ℚ.∣ seq x n ℚ.- seq y n ∣ ℚ.≤ (+ 1 / j) {j≢0}) ->
                        x ≃ y                  
equality-lemma-onlyif x y hyp1 = *≃* (λ n {n≢0} -> lem n {n≢0} (∣xₙ-yₙ∣≤2/n+3/j n {n≢0}))
  where
    open ℚP.≤-Reasoning
    open ℚ-Solver
    open ℤ-Solver using ()
      renaming
        ( solve to ℤsolve
        ; _⊕_ to _:+_
        ; _⊗_ to _:*_
        ; _⊜_ to _:=_
        ; Κ   to κ
        )

    @0 ∣xₙ-yₙ∣≤2/n+3/j : ∀ (n : ℕ) -> {n≢0 : n ≢0} -> ∀ (j : ℕ) -> {j≢0 : j ≢0} ->
                      ℚ.∣ seq x n ℚ.- seq y n ∣ ℚ.≤ (+ 2 / n) {n≢0} ℚ.+ (+ 3 / j) {j≢0}
    ∣xₙ-yₙ∣≤2/n+3/j (suc k₁) (suc k₂) = let n = suc k₁; j = suc k₂; Nⱼ = suc (proj₁ (hyp1 j)); m = j ℕ.⊔ Nⱼ in begin
       ℚ.∣ seq x n ℚ.- seq y n ∣                         ≈⟨ ℚP.∣-∣-cong (solve 4 (λ xₘ yₘ xₙ yₙ ->
                                                            (xₙ ⊖ yₙ) ⊜ ((xₙ ⊖ xₘ) ⊕ (xₘ ⊖ yₘ) ⊕ (yₘ ⊖ yₙ)))
                                                            ℚP.≃-refl (seq x m) (seq y m) (seq x n) (seq y n)) ⟩
      ℚ.∣ seq x n ℚ.- seq x m  ℚ.+
         (seq x m ℚ.- seq y m) ℚ.+
         (seq y m ℚ.- seq y n) ∣                        ≤⟨ ℚP.≤-trans
                                                           (ℚP.∣p+q∣≤∣p∣+∣q∣ (seq x n ℚ.- seq x m ℚ.+ (seq x m ℚ.- seq y m)) (seq y m ℚ.- seq y n))
                                                           (ℚP.+-monoˡ-≤ ℚ.∣ seq y m ℚ.- seq y n ∣
                                                           (ℚP.∣p+q∣≤∣p∣+∣q∣ (seq x n ℚ.- seq x m) (seq x m ℚ.- seq y m))) ⟩
      ℚ.∣ seq x n ℚ.- seq x m ∣ ℚ.+
      ℚ.∣ seq x m ℚ.- seq y m ∣ ℚ.+
      ℚ.∣ seq y m ℚ.- seq y n ∣                         ≤⟨ ℚP.+-mono-≤
                                                           (ℚP.+-mono-≤ (reg x n m) (proj₂ (hyp1 j) m
                                                                        (ℕP.≤-trans (ℕP.n≤1+n (ℕ.pred Nⱼ)) (ℕP.m≤n⊔m j Nⱼ))))
                                                           (reg y m n) ⟩
      (+ 1 / n ℚ.+ + 1 / m) ℚ.+
      + 1 / j               ℚ.+
      (+ 1 / m ℚ.+ + 1 / n)                             ≈⟨ ℚ.*≡* (ℤsolve 3 (λ j m n ->
                                                           (((κ (+ 1) :* m :+ κ (+ 1) :* n) :* j :+ κ (+ 1) :* (n :* m)) :* (m :* n) :+
                                                           ((κ (+ 1) :* n :+ κ (+ 1) :* m) :* (n :* m :* j))) :* (n :* (m :* j)) :=
                                                           (κ (+ 2) :* (m :* j) :+ (κ (+ 2) :* j :+ κ (+ 1) :* m) :* n) :* ((n :* m :* j) :* (m :* n)))
                                                           refl (+ j) (+ m) (+ n)) ⟩
      + 2 / n ℚ.+ (+ 2 / m ℚ.+ + 1 / j)                 ≤⟨ ℚP.+-monoʳ-≤ (+ 2 / n) {+ 2 / m ℚ.+ + 1 / j} {+ 3 / j}
                                                           (ℚP.≤-respʳ-≃ {+ 2 / m ℚ.+ + 1 / j} {+ 2 / j ℚ.+ + 1 / j} {+ 3 / j}
                                                           (ℚ.*≡* {+ 2 / j ℚ.+ + 1 / j} {+ 3 / j}
                                                           (ℤsolve 1 (λ j -> (κ (+ 2) :* j :+ κ (+ 1) :* j) :* j := κ (+ 3) :* (j :* j)) refl (+ j)))
                                                           (ℚP.+-monoˡ-≤ (+ 1 / j) {+ 2 / m} {+ 2 / j} (ℚ.*≤* (ℤP.*-monoˡ-≤-nonNeg 2 (ℤP.i≤i⊔j (+ j) (+ Nⱼ)))))) ⟩
      + 2 / n ℚ.+ + 3 / j                                ∎
      

    @0 lem : ∀ (n : ℕ) -> {n≢0 : n ≢0} ->
          (∀ (j : ℕ) -> {j≢0 : j ≢0} ->
          ℚ.∣ seq x n ℚ.- seq y n ∣ ℚ.≤ (+ 2 / n) {n≢0} ℚ.+ (+ 3 / j) {j≢0}) ->
          ℚ.∣ seq x n ℚ.- seq y n ∣ ℚ.≤ (+ 2 / n) {n≢0}
    lem (suc k₂) hyp2 = let n = suc k₂ in
                          ℚP.≮⇒≥ (λ hyp3 -> let arch = fastArchimedeanℚ₂ (ℚ.∣ seq x n ℚ.- seq y n ∣ ℚ.- + 2 / n) (+ 3)
                                                        (ℚ.positive (p<q⇒0<q-p (+ 2 / n) ℚ.∣ seq x n ℚ.- seq y n ∣ hyp3))
                                                        ; j = suc (proj₁ arch)
                                                        ; Nⱼ = suc (proj₁ (hyp1 j))
                                                        ; m = j ℕ.⊔ Nⱼ in
                          ℚP.<-irrefl ℚP.≃-refl (begin-strict
      + 2 / n ℚ.+ + 3 / j                               ≈⟨ ℚP.+-comm (+ 2 / n) (+ 3 / j) ⟩
      + 3 / j ℚ.+ + 2 / n                               <⟨ ℚP.+-monoˡ-< (+ 2 / n) (proj₂ arch) ⟩
      ℚ.∣ seq x n ℚ.- seq y n ∣ ℚ.- + 2 / n ℚ.+ + 2 / n ≈⟨ solve 2 (λ a b -> a ⊖ b ⊕ b ⊜ a) ℚP.≃-refl
                                                           ℚ.∣ seq x n ℚ.- seq y n ∣ (+ 2 / n) ⟩
      ℚ.∣ seq x n ℚ.- seq y n ∣                         ≤⟨ ∣xₙ-yₙ∣≤2/n+3/j n j ⟩
      + 2 / n ℚ.+ + 3 / j                                ∎))

≃-trans : Transitive _≃_
≃-trans {x} {y} {z} x≃y y≃z = equality-lemma-onlyif x z lem
  where
    open ℚP.≤-Reasoning
    open ℚ-Solver
    open ℤ-Solver using ()
      renaming
        ( solve to ℤsolve
        ; _⊕_  to _:+_
        ; _⊗_  to _:*_
        ; _⊜_  to _:=_
        ; Κ    to κ
        )
    @0 lem : (j : ℕ) {j≢0 : j ≢0} →
      ∃ (λ N → (n : ℕ) → n ℕ.≥ N → ℚ.∣ seq x n ℚ.- seq z n ∣ ℚ.≤ + 1 / j)
    lem (suc k₁) = N , lem₂
      where
        j = suc k₁
        eqxy = fastEqualityLemmaIf x y x≃y
        eqyz = fastEqualityLemmaIf y z y≃z
        N₁ = proj₁ (eqxy (2 ℕ.* j)); N₂ = proj₁ (eqyz (2 ℕ.* j))
        N = suc (N₁ ℕ.⊔ N₂)
        
        lem₂ : (n : ℕ) → n ℕ.≥ suc (proj₁ (fastEqualityLemmaIf x y x≃y (suc (k₁ ℕ.+ suc (k₁ ℕ.+ zero)))) ℕ.⊔ proj₁ (fastEqualityLemmaIf y z y≃z (suc (k₁ ℕ.+ suc (k₁ ℕ.+ zero))))) →
             ℚ.∣ seq x n ℚ.- seq z n ∣ ℚ.≤ mkℚᵘ (+ 1) k₁
        lem₂ (suc k₂) n≥N = let n = suc k₂ ; N₁⊔N₂≤n = ℕP.≤-trans (ℕP.n≤1+n (ℕ.pred N)) n≥N in begin
                  ℚ.∣ seq x n ℚ.- seq z n ∣                               ≈⟨ ℚP.∣-∣-cong (solve 3 (λ xₙ yₙ zₙ ->
                                                                              xₙ ⊖ zₙ ⊜ (xₙ ⊖ yₙ ⊕ (yₙ ⊖ zₙ)))
                                                                              ℚP.≃-refl (seq x n) (seq y n) (seq z n)) ⟩
                  ℚ.∣ seq x n ℚ.- seq y n ℚ.+ (seq y n ℚ.- seq z n) ∣     ≤⟨ ℚP.∣p+q∣≤∣p∣+∣q∣ (seq x n ℚ.- seq y n) (seq y n ℚ.- seq z n) ⟩
                  ℚ.∣ seq x n ℚ.- seq y n ∣ ℚ.+ ℚ.∣ seq y n ℚ.- seq z n ∣ ≤⟨ ℚP.+-mono-≤
                                                                             (proj₂ (eqxy (2 ℕ.* j)) n (ℕP.≤-trans (ℕP.m≤m⊔n N₁ N₂) N₁⊔N₂≤n))
                                                                             (proj₂ (eqyz (2 ℕ.* j)) n (ℕP.≤-trans (ℕP.m≤n⊔m N₁ N₂) N₁⊔N₂≤n)) ⟩
                  + 1 / (2 ℕ.* j) ℚ.+ + 1 / (2 ℕ.* j)                    ≈⟨ ℚ.*≡* (ℤsolve 1 (λ j ->
                                                                             (κ (+ 1) :* (κ (+ 2) :* j) :+ κ (+ 1) :* (κ (+ 2) :* j)) :* j :=
                                                                             κ (+ 1) :* ((κ (+ 2) :* j) :* (κ (+ 2) :* j)))
                                                                            refl (+ j)) ⟩
                  + 1 / j                                                 ∎

-- Equivalence relatiion structures and reasoning packages

≃-isEquivalence : IsEquivalence _≃_
≃-isEquivalence = record
  { refl = ≃-refl
  ; sym = ≃-sym
  ; trans = ≃-trans
  }

≃-setoid : Setoid 0ℓ 0ℓ
≃-setoid = record
  { isEquivalence = ≃-isEquivalence
  }


module ≃-Reasoning where
  open import Relation.Binary.Reasoning.Setoid ≃-setoid
    public

-- Extras for proving properties of arithmetic operations
@0 regular⇒cauchy : ∀ (x : ℝ) -> ∀ (j : ℕ) -> {j≢0 : j ≢0} -> ∃ λ (N : ℕ) -> ∀ (m n : ℕ) ->
                 m ℕ.≥ N -> n ℕ.≥ N -> ℚ.∣ seq x m ℚ.- seq x n ∣ ℚ.≤ (+ 1 / j) {j≢0}
regular⇒cauchy x (suc k₁) = 2 ℕ.* j , lem
  where
    open ℚP.≤-Reasoning
    open ℤ-Solver

    j = suc k₁

    @0 lem : (m n : ℕ) → m ℕ.≥ suc (k₁ ℕ.+ suc (k₁ ℕ.+ zero)) → n ℕ.≥ suc (k₁ ℕ.+ suc (k₁ ℕ.+ zero)) →
           ℚ.∣ seq x m ℚ.- seq x n ∣ ℚ.≤ mkℚᵘ (+ 1) k₁
    lem (suc k₂) (suc k₃) m≥N n≥N = let m = suc k₂; n = suc k₃ in begin 
           ℚ.∣ seq x m ℚ.- seq x n ∣                ≤⟨ reg x m n ⟩
           (+ 1 / m) ℚ.+ (+ 1 / n)                 ≤⟨ ℚP.+-mono-≤ (q≤r⇒+p/r≤+p/q 1 (2 ℕ.* j) m m≥N) (q≤r⇒+p/r≤+p/q 1 (2 ℕ.* j) n n≥N) ⟩
           (+ 1 / (2 ℕ.* j)) ℚ.+ (+ 1 / (2 ℕ.* j)) ≈⟨ ℚ.*≡* (solve 1 (λ j ->
                                                            (Κ (+ 1) ⊗ (Κ (+ 2) ⊗ j) ⊕ Κ (+ 1) ⊗ (Κ (+ 2) ⊗ j)) ⊗ j ⊜
                                                            (Κ (+ 1) ⊗ ((Κ (+ 2) ⊗ j) ⊗ (Κ (+ 2) ⊗ j)))) refl (+ j)) ⟩
           + 1 / j                                  ∎

abstract
  @0 fast-regular⇒cauchy : ∀ (x : ℝ) -> ∀ (j : ℕ) -> {j≢0 : j ≢0} -> ∃ λ (N : ℕ) -> ∀ (m n : ℕ) ->
                        m ℕ.≥ N -> n ℕ.≥ N -> ℚ.∣ seq x m ℚ.- seq x n ∣ ℚ.≤ (+ 1 / j) {j≢0}
  fast-regular⇒cauchy = regular⇒cauchy


@0 equals-to-cauchy : ∀ x y -> x ≃ y -> ∀ (j : ℕ) -> {j≢0 : j ≢0} ->
                   ∃ λ (N : ℕ) -> ∀ (m n : ℕ) -> m ℕ.≥ N -> n ℕ.≥ N ->
                   ℚ.∣ seq x m ℚ.- seq y n ∣ ℚ.≤ (+ 1 / j) {j≢0}
equals-to-cauchy x y x≃y (suc k₁) = N , lem
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

    j N₁ N₂ N : ℕ
    j = suc k₁
    N₁ = suc (proj₁ (fastEqualityLemmaIf x y x≃y (2 ℕ.* j)))
    N₂ = proj₁ (regular⇒cauchy x (2 ℕ.* j))
    N = N₁ ℕ.⊔ N₂
    lem : (m n : ℕ) → m ℕ.≥ N → n ℕ.≥ N → ℚ.∣ seq x m ℚ.- seq y n ∣ ℚ.≤ mkℚᵘ (+ 1) k₁
    lem (suc k₂) (suc k₃) m≥N n≥N = let m = suc k₂; n = suc k₃ in begin
          ℚ.∣ seq x m ℚ.- seq y n ∣     ≈⟨ ℚP.∣-∣-cong (solve 3 (λ xm yn xn ->
                                           (xm ⊖ yn) ⊜ ((xm ⊖ xn) ⊕ (xn ⊖ yn)))
                                           ℚP.≃-refl (seq x m) (seq y n) (seq x n)) ⟩
          ℚ.∣ (seq x m ℚ.- seq x n) ℚ.+
              (seq x n ℚ.- seq y n) ∣   ≤⟨ ℚP.∣p+q∣≤∣p∣+∣q∣ (seq x m ℚ.- seq x n)
                                                             (seq x n ℚ.- seq y n) ⟩
          ℚ.∣ seq x m ℚ.- seq x n ∣ ℚ.+
          ℚ.∣ seq x n ℚ.- seq y n ∣     ≤⟨ ℚP.+-mono-≤
                                           (proj₂ (regular⇒cauchy x (2 ℕ.* j)) m n (ℕP.≤-trans (ℕP.m≤n⊔m N₁ N₂) m≥N) (ℕP.≤-trans (ℕP.m≤n⊔m N₁ N₂) n≥N))
                                           (proj₂ (fastEqualityLemmaIf x y x≃y (2 ℕ.* j)) n (ℕP.≤-trans (ℕP.n≤1+n (ℕ.pred N₁)) (ℕP.≤-trans (ℕP.m≤m⊔n N₁ N₂) n≥N))) ⟩
          (+ 1 / (2 ℕ.* j)) ℚ.+
          (+ 1 / (2 ℕ.* j))             ≈⟨ ℚ.*≡* (ℤsolve 1 (λ j ->
                                           (κ (+ 1) :* (κ (+ 2) :* j) :+ (κ (+ 1) :* (κ (+ 2) :* j))) :* j :=
                                           (κ (+ 1) :* ((κ (+ 2) :* j) :* (κ (+ 2) :* j))))
                                           refl (+ j)) ⟩
          + 1 / j                        ∎

abstract
  @0 fast-equals-to-cauchy : ∀ x y -> x ≃ y -> ∀ (j : ℕ) -> {j≢0 : j ≢0} ->
                          ∃ λ (N : ℕ) -> ∀ (m n : ℕ) -> m ℕ.≥ N -> n ℕ.≥ N ->
                          ℚ.∣ seq x m ℚ.- seq y n ∣ ℚ.≤ (+ 1 / j) {j≢0}
  fast-equals-to-cauchy = equals-to-cauchy

-- Properties of _+_

+-cong : Congruent₂ _≃_ _+_
+-cong {x} {z} {y} {w} (*≃* x₁) (*≃* x₂) = *≃* (lem)
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
    @0 lem : (n : ℕ) {n≢0 : n ≢0} → ℚ.∣ seq (x + y) n ℚ.- seq (z + w) n ∣ ℚ.≤ (_/_ (+ 2) n {n≢0})
    lem (suc k₁) = let n = suc k₁ in begin
           ℚ.∣ seq x (2 ℕ.* n) ℚ.+ seq y (2 ℕ.* n) ℚ.-
              (seq z (2 ℕ.* n) ℚ.+ seq w (2 ℕ.* n)) ∣    ≈⟨ ℚP.∣-∣-cong (solve 4 (λ x y z w ->
                                                            (x ⊕ y ⊖ (z ⊕ w)) ⊜ ((x ⊖ z) ⊕ (y ⊖ w)))
                                                            ℚP.≃-refl (seq x (2 ℕ.* n)) (seq y (2 ℕ.* n)) (seq z (2 ℕ.* n)) (seq w (2 ℕ.* n))) ⟩
           ℚ.∣ seq x (2 ℕ.* n) ℚ.- seq z (2 ℕ.* n) ℚ.+
              (seq y (2 ℕ.* n) ℚ.- seq w (2 ℕ.* n)) ∣    ≤⟨ ℚP.∣p+q∣≤∣p∣+∣q∣ (seq x (2 ℕ.* n) ℚ.- seq z (2 ℕ.* n)) (seq y (2 ℕ.* n) ℚ.- seq w (2 ℕ.* n)) ⟩
           ℚ.∣ seq x (2 ℕ.* n) ℚ.- seq z (2 ℕ.* n) ∣ ℚ.+
           ℚ.∣ seq y (2 ℕ.* n) ℚ.- seq w (2 ℕ.* n) ∣     ≤⟨ ℚP.+-mono-≤ (x₁ (2 ℕ.* n)) (x₂ (2 ℕ.* n)) ⟩
           + 2 / (2 ℕ.* n) ℚ.+ + 2 / (2 ℕ.* n)           ≈⟨ ℚ.*≡* (ℤsolve 1 (λ n ->
                                                            (κ (+ 2) :* (κ (+ 2) :* n) :+ κ (+ 2) :* (κ (+ 2) :* n)) :* n :=
                                                            (κ (+ 2) :* ((κ (+ 2) :* n) :* (κ (+ 2) :* n)))) refl (+ n)) ⟩
           + 2 / n                                        ∎

+-congʳ : ∀ x {y z} -> y ≃ z -> x + y ≃ x + z
+-congʳ x y≃z = +-cong ≃-refl y≃z

+-congˡ : ∀ x {y z} -> y ≃ z -> y + x ≃ z + x
+-congˡ x y≃z = +-cong y≃z ≃-refl

+-comm : Commutative _≃_ _+_
+-comm x y = *≃* (λ @0 { (suc k₁) -> let n = suc k₁ in begin
  ℚ.∣ (seq x (2 ℕ.* n) ℚ.+ seq y (2 ℕ.* n)) ℚ.-
      (seq y (2 ℕ.* n) ℚ.+ seq x (2 ℕ.* n)) ∣   ≈⟨ ℚP.∣-∣-cong (solve 2 (λ x y ->
                                                   (x ⊕ y) ⊖ (y ⊕ x) ⊜ Κ (+ 0 / 1))
                                                   ℚP.≃-refl (seq x (2 ℕ.* n)) (seq y (2 ℕ.* n))) ⟩
  (+ 0 / 1)                                           ≤⟨ ℚP.nonNegative⁻¹ _ ⟩
  (+ 2) / n                                      ∎})
  where
    open ℚP.≤-Reasoning
    open ℚ-Solver

+-assoc : Associative _≃_ _+_
+-assoc x y z = *≃* lem
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
    --this is ugly, but that's what Agda gave...
    @0 lem : (n : ℕ) {n≢0 : n ≢0} → ℚ.∣ seq x (n ℕ.+ (n ℕ.+ zero) ℕ.+ (n ℕ.+ (n ℕ.+ zero) ℕ.+ zero)) ℚ.+ seq y (n ℕ.+ (n ℕ.+ zero) ℕ.+ (n ℕ.+ (n ℕ.+ zero) ℕ.+ zero)) ℚ.+ seq z (n ℕ.+ (n ℕ.+ zero))
      ℚ.-
      (seq x (n ℕ.+ (n ℕ.+ zero)) ℚ.+
       (seq y (n ℕ.+ (n ℕ.+ zero) ℕ.+ (n ℕ.+ (n ℕ.+ zero) ℕ.+ zero)) ℚ.+
        seq z (n ℕ.+ (n ℕ.+ zero) ℕ.+ (n ℕ.+ (n ℕ.+ zero) ℕ.+ zero))))
      ∣
      ℚ.≤ + 2 / n
    lem (suc k₁) = let n = suc k₁; 2n = 2 ℕ.* n; 4n = 2 ℕ.* 2n in begin
             ℚ.∣ ((seq x 4n ℚ.+ seq y 4n) ℚ.+ seq z 2n) ℚ.-
                 (seq x 2n ℚ.+ (seq y 4n ℚ.+ seq z 4n)) ∣                ≈⟨ ℚP.∣-∣-cong (solve 5 (λ x4 y4 z2 x2 z4 ->
                                                                                             (((x4 ⊕ y4) ⊕ z2) ⊖ (x2 ⊕ (y4 ⊕ z4))) ⊜
                                                                                             ((x4 ⊖ x2) ⊕ (z2 ⊖ z4)))
                                                                                             ℚP.≃-refl (seq x 4n) (seq y 4n) (seq z 2n) (seq x 2n) (seq z 4n)) ⟩
             ℚ.∣ (seq x 4n ℚ.- seq x 2n) ℚ.+ (seq z 2n ℚ.- seq z 4n) ∣   ≤⟨ ℚP.∣p+q∣≤∣p∣+∣q∣ (seq x 4n ℚ.- seq x 2n) (seq z 2n ℚ.- seq z 4n) ⟩
             ℚ.∣ seq x 4n ℚ.- seq x 2n ∣ ℚ.+ ℚ.∣ seq z 2n ℚ.- seq z 4n ∣ ≤⟨ ℚP.+-mono-≤ (reg x 4n 2n) (reg z 2n 4n) ⟩
             ((+ 1 / 4n) ℚ.+ (+ 1 / 2n)) ℚ.+ ((+ 1 / 2n) ℚ.+ (+ 1 / 4n)) ≈⟨ ℚ.*≡* (ℤsolve 1 ((λ 2n ->
                                                                            ((κ (+ 1) :* 2n :+ κ (+ 1) :* (κ (+ 2) :* 2n)) :*
                                                                            (2n :* (κ (+ 2) :* 2n)) :+
                                                                            (κ (+ 1) :* (κ (+ 2) :* 2n) :+ κ (+ 1) :* 2n) :*
                                                                            ((κ (+ 2) :* 2n) :* 2n)) :* 2n :=
                                                                            κ (+ 3) :* (((κ (+ 2) :* 2n) :* 2n) :*
                                                                            (2n :* (κ (+ 2) :* 2n)))))
                                                                            refl (+ 2n)) ⟩
             + 3 / 2n                                                    ≤⟨ ℚ.*≤* (ℤP.*-monoʳ-≤-nonNeg 2n (ℤ.+≤+ (ℕ.s≤s (ℕ.s≤s (ℕ.s≤s (ℕ.z≤n {1})))))) ⟩
             + 4 / 2n                                                    ≈⟨ ℚ.*≡* (ℤsolve 1 (λ n ->
                                                                                       κ (+ 4) :* n := κ (+ 2) :* (κ (+ 2) :* n))
                                                                                       refl (+ n)) ⟩
             + 2 / n                                                      ∎

+-identityˡ : LeftIdentity _≃_ zeroℝ _+_
+-identityˡ x = *≃* (lem)
  where
    open ℚP.≤-Reasoning
    open ℤ-Solver

    @0 lem : (n : ℕ) {n≢0 : n ≢0} → ℚ.∣ seq (zeroℝ + x) n ℚ.- seq x n ∣ ℚ.≤ + 2 / n
    lem (suc k₁) = let n = suc k₁ in begin
           ℚ.∣ ((+ 0 / 1) ℚ.+ seq x (2 ℕ.* n)) ℚ.- seq x n ∣ ≈⟨ ℚP.∣-∣-cong (ℚP.+-congˡ (ℚ.- seq x n) (ℚP.+-identityˡ (seq x (2 ℕ.* n)))) ⟩
           ℚ.∣ seq x (2 ℕ.* n) ℚ.- seq x n ∣           ≤⟨ reg x (2 ℕ.* n) n ⟩
           (+ 1 / (2 ℕ.* n)) ℚ.+ (+ 1 / n)             ≈⟨ ℚ.*≡* (solve 1 (λ n ->
                                                          (Κ (+ 1) ⊗ n ⊕ Κ (+ 1) ⊗ (Κ (+ 2) ⊗ n)) ⊗ (Κ (+ 2) ⊗ n) ⊜
                                                           Κ (+ 3) ⊗ ((Κ (+ 2) ⊗ n) ⊗ n))
                                                          refl (+ n)) ⟩
           + 3 / (2 ℕ.* n)                             ≤⟨ ℚ.*≤* (ℤP.*-monoʳ-≤-nonNeg (2 ℕ.* n) (ℤ.+≤+ (ℕ.s≤s (ℕ.s≤s (ℕ.s≤s (ℕ.z≤n {1})))))) ⟩
           + 4 / (2 ℕ.* n)                             ≈⟨ ℚ.*≡* (solve 1 (λ n ->
                                                          Κ (+ 4) ⊗ n ⊜ Κ (+ 2) ⊗ (Κ (+ 2) ⊗ n))
                                                          refl (+ n)) ⟩
           + 2 / n                                      ∎

+-identityʳ : RightIdentity _≃_ zeroℝ _+_
+-identityʳ x = ≃-trans (+-comm x zeroℝ) (+-identityˡ x)

+-identity : Identity _≃_ zeroℝ _+_
+-identity = +-identityˡ , +-identityʳ

+-inverseʳ : RightInverse _≃_ zeroℝ -_ _+_
+-inverseʳ x = *≃* (λ @0 { (suc k₁) -> let n = suc k₁ in begin
  ℚ.∣ (seq x (2 ℕ.* n) ℚ.- seq x (2 ℕ.* n)) ℚ.+ (+ 0 / 1) ∣ ≈⟨ ℚP.∣-∣-cong (solve 1 (λ x -> x ⊖ x ⊕ Κ (+ 0 / 1) ⊜ Κ (+ 0 / 1))
                                                         ℚP.≃-refl (seq x (2 ℕ.* n))) ⟩
  (+ 0 / 1)                                                 ≤⟨ ℚ.*≤* (ℤP.≤-trans (ℤP.≤-reflexive (ℤP.*-zeroˡ (+ n))) (ℤ.+≤+ ℕ.z≤n)) ⟩
  + 2 / n                                              ∎})
  where
    open ℚP.≤-Reasoning
    open ℚ-Solver

+-inverseˡ : LeftInverse _≃_ zeroℝ -_ _+_
+-inverseˡ x = ≃-trans (+-comm (negate x) x) (+-inverseʳ x)

+-inverse : Inverse _≃_ zeroℝ -_ _+_
+-inverse = +-inverseˡ , +-inverseʳ

-- Properties of toReal

⋆-cong : ∀ {p} {q} -> p ℚ.≃ q -> p ⋆ ≃ q ⋆
⋆-cong {p} {q} p≃q = *≃* (λ @0 {(suc k₁) -> let n = suc k₁ in begin
  ℚ.∣ p ℚ.- q ∣ ≈⟨ ℚP.∣-∣-cong (ℚP.p≃q⇒p-q≃0 p q p≃q) ⟩
  (+ 0 / 1)           ≤⟨ ℚP.nonNegative⁻¹ _ ⟩
  + 2 / n        ∎})
  where open ℚP.≤-Reasoning

⋆-distrib-+ : ∀ (p r : ℚᵘ) -> (p ℚ.+ r) ⋆ ≃ p ⋆ + r ⋆
⋆-distrib-+ x y = *≃* (λ @0 { (suc k₁) -> let n = suc k₁; p = ↥ x; q = ↧ₙ x; u = ↥ y; v = ↧ₙ y in begin
  ℚ.∣ ((p / q) ℚ.+ (u / v)) ℚ.- ((p / q) ℚ.+ (u / v)) ∣ ≈⟨ ℚP.∣-∣-cong (ℚP.+-inverseʳ ((p / q) ℚ.+ (u / v))) ⟩
  (+ 0 / 1)                                                   ≤⟨ ℚP.nonNegative⁻¹ _ ⟩
  (+ 2) / n                                              ∎})
  where open ℚP.≤-Reasoning

⋆-distrib-* : ∀ p q -> (p ℚ.* q) ⋆ ≃ p ⋆ * q ⋆
⋆-distrib-* p q = *≃* (λ @0 {(suc n-1) -> let n = suc n-1 in begin
  ℚ.∣ p ℚ.* q ℚ.- p ℚ.* q ∣ ≈⟨ ℚP.∣-∣-cong (ℚP.+-inverseʳ (p ℚ.* q)) ⟩
  (+ 0 / 1)                       ≤⟨ ℚP.nonNegative⁻¹ _ ⟩
  + 2 / n                    ∎})
  where open ℚP.≤-Reasoning

⋆-distrib-neg : ∀ (p : ℚᵘ) -> ((ℚ.- p) ⋆) ≃ negate (p ⋆)
⋆-distrib-neg p = *≃* λ @0 { (suc k₁) -> let n = suc k₁ in begin
  ℚ.∣ ℚ.- p ℚ.- (ℚ.- p) ∣ ≈⟨ ℚP.∣-∣-cong (ℚP.+-inverseʳ (ℚ.- p)) ⟩
  (+ 0 / 1)                     ≤⟨ ℚP.nonNegative⁻¹ _ ⟩
  (+ 2) / n                ∎}
  where open ℚP.≤-Reasoning

@0 ∣p∣⋆≃∣p⋆∣ : ∀ p -> (ℚ.∣ p ∣ ⋆) ≃ abs (p ⋆)
∣p∣⋆≃∣p⋆∣ p = ≃-reflexive (λ {n -> ℚP.≃-refl})

-- Properties of _*_

*-cong : Congruent₂ _≃_ _*_
*-cong {x} {z} {y} {w} x≃z y≃w = equality-lemma-onlyif (x * y) (z * w) partA                                                     
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

    @0 partA : ∀ (j : ℕ) -> {j≢0 : j ≢0} -> ∃ λ (N : ℕ) -> ∀ (n : ℕ) -> n ℕ.≥ N ->
            ℚ.∣ seq (x * y) n ℚ.- seq (z * w) n ∣ ℚ.≤ (+ 1 / j) {j≢0}
    partA (suc k₁) = N , partB
      where
        j = suc k₁
        r = fK x ℕ.⊔ fK y
        t = fK z ℕ.⊔ fK w
        N₁ = proj₁ (fast-equals-to-cauchy x z x≃z (fK y ℕ.* (2 ℕ.* j)))
        N₂ = proj₁ (fast-equals-to-cauchy y w y≃w (fK z ℕ.* (2 ℕ.* j)))
        N = suc (N₁ ℕ.⊔ N₂)

        partB : ∀ (n : ℕ) -> n ℕ.≥ N -> ℚ.∣ seq (x * y) n ℚ.- seq (z * w) n ∣ ℚ.≤ (+ 1 / j)
        partB (suc k₂) n≥N = let n = suc k₂
                                   ; x₂ᵣₙ = seq x (2 ℕ.* r ℕ.* n)
                                   ; y₂ᵣₙ = seq y (2 ℕ.* r ℕ.* n)
                                   ; z₂ₜₙ = seq z (2 ℕ.* t ℕ.* n)
                                   ; w₂ₜₙ = seq w (2 ℕ.* t ℕ.* n) in begin
          ℚ.∣ x₂ᵣₙ ℚ.* y₂ᵣₙ ℚ.- z₂ₜₙ ℚ.* w₂ₜₙ ∣             ≈⟨ ℚP.∣-∣-cong (solve 4 (λ x y z w ->
                                                               (x ⊗ y ⊖ z ⊗ w) ⊜ (y ⊗ (x ⊖ z) ⊕ z ⊗ (y ⊖ w)))
                                                               ℚP.≃-refl x₂ᵣₙ y₂ᵣₙ z₂ₜₙ w₂ₜₙ) ⟩
          ℚ.∣ y₂ᵣₙ ℚ.* (x₂ᵣₙ ℚ.- z₂ₜₙ) ℚ.+
              z₂ₜₙ ℚ.* (y₂ᵣₙ ℚ.- w₂ₜₙ) ∣                   ≤⟨ ℚP.∣p+q∣≤∣p∣+∣q∣ (y₂ᵣₙ ℚ.* (x₂ᵣₙ ℚ.- z₂ₜₙ))
                                                                              (z₂ₜₙ ℚ.* (y₂ᵣₙ ℚ.- w₂ₜₙ)) ⟩
          ℚ.∣ y₂ᵣₙ ℚ.* (x₂ᵣₙ ℚ.- z₂ₜₙ) ∣ ℚ.+
          ℚ.∣ z₂ₜₙ ℚ.* (y₂ᵣₙ ℚ.- w₂ₜₙ) ∣                   ≈⟨ ℚP.+-cong (ℚP.∣p*q∣≃∣p∣*∣q∣ y₂ᵣₙ ((x₂ᵣₙ ℚ.- z₂ₜₙ)))
                                                                        (ℚP.∣p*q∣≃∣p∣*∣q∣ z₂ₜₙ (y₂ᵣₙ ℚ.- w₂ₜₙ)) ⟩
          ℚ.∣ y₂ᵣₙ ∣ ℚ.* ℚ.∣ x₂ᵣₙ ℚ.- z₂ₜₙ ∣ ℚ.+
          ℚ.∣ z₂ₜₙ ∣ ℚ.* ℚ.∣ y₂ᵣₙ ℚ.- w₂ₜₙ ∣               ≤⟨ ℚP.+-mono-≤ (ℚP.≤-trans
                                                                          (ℚP.*-monoˡ-≤-nonNeg {ℚ.∣ x₂ᵣₙ ℚ.- z₂ₜₙ ∣} _
                                                                                               (ℚP.<⇒≤ (canonical-strict-upper-bound y (2 ℕ.* r ℕ.* n))))
                                                                          (ℚP.*-monoʳ-≤-nonNeg {+ fK y / 1} _
                                                                                               (proj₂ (fast-equals-to-cauchy x z x≃z (fK y ℕ.* (2 ℕ.* j)))
                                                                                                      (2 ℕ.* r ℕ.* n) (2 ℕ.* t ℕ.* n)
                                                                                                      (N₁≤ (2 ℕ.* r ℕ.* n) (N≤2kn r))
                                                                                                      (N₁≤ (2 ℕ.* t ℕ.* n) (N≤2kn t)))))
                                                                          (ℚP.≤-trans
                                                                          (ℚP.*-monoˡ-≤-nonNeg {ℚ.∣ y₂ᵣₙ ℚ.- w₂ₜₙ ∣} _
                                                                                               (ℚP.<⇒≤ (canonical-strict-upper-bound z (2 ℕ.* t ℕ.* n))))
                                                                          (ℚP.*-monoʳ-≤-nonNeg {+ fK z / 1} _
                                                                                               (proj₂ (fast-equals-to-cauchy y w y≃w (fK z ℕ.* (2 ℕ.* j)))
                                                                                               (2 ℕ.* r ℕ.* n) (2 ℕ.* t ℕ.* n)
                                                                                               (N₂≤ (2 ℕ.* r ℕ.* n) (N≤2kn r))
                                                                                               (N₂≤ (2 ℕ.* t ℕ.* n) (N≤2kn t))))) ⟩
          (+ fK y / 1) ℚ.* (+ 1 / (fK y ℕ.* (2 ℕ.* j))) ℚ.+
          (+ fK z / 1) ℚ.* (+ 1 / (fK z ℕ.* (2 ℕ.* j)))     ≈⟨ ℚ.*≡* (ℤsolve 3 (λ Ky Kz j ->

          -- Function for solver
          ((Ky :* κ (+ 1)) :* (κ (+ 1) :* (Kz :* (κ (+ 2) :* j))) :+ (Kz :* κ (+ 1) :* (κ (+ 1) :* (Ky :* (κ (+ 2) :* j))))) :* j :=
          κ (+ 1) :* ((κ (+ 1) :* (Ky :* (κ (+ 2) :* j))) :* (κ (+ 1) :* (Kz :* (κ (+ 2) :* j)))))
          refl (+ fK y) (+ fK z) (+ j)) ⟩
          
          + 1 / j                                          ∎
          where
            N≤2kn : ∀ (k : ℕ) -> {k ≢0} -> N ℕ.≤ 2 ℕ.* k ℕ.* (suc k₂)
            N≤2kn (suc k) = ℕP.≤-trans n≥N (ℕP.m≤n*m (suc k₂) {2 ℕ.* (suc k)} ℕP.0<1+n)

            N₁≤ : ∀ (k : ℕ) -> N ℕ.≤ k -> N₁ ℕ.≤ k
            N₁≤ k N≤k = ℕP.≤-trans (ℕP.m≤m⊔n N₁ N₂) (ℕP.≤-trans (ℕP.n≤1+n (ℕ.pred N)) N≤k)

            N₂≤ : ∀ (k : ℕ) -> N ℕ.≤ k -> N₂ ℕ.≤ k
            N₂≤ k N≤k = ℕP.≤-trans (ℕP.m≤n⊔m N₁ N₂) (ℕP.≤-trans (ℕP.n≤1+n (ℕ.pred N)) N≤k)

@0 *-congˡ : LeftCongruent _≃_ _*_
*-congˡ y≃z = *-cong ≃-refl y≃z

@0 *-congʳ : RightCongruent _≃_ _*_
*-congʳ y≃z = *-cong y≃z ≃-refl

*-comm : Commutative _≃_ _*_
*-comm x y = *≃* lem
  where
    open ℚP.≤-Reasoning
    @0 xyℚ≃yxℚ : ∀ (n : ℕ) -> seq (x * y) n ℚ.≃ seq (y * x) n
    xyℚ≃yxℚ n = begin-equality
      seq x (2 ℕ.* (fK x ℕ.⊔ fK y) ℕ.* n) ℚ.*
      seq y (2 ℕ.* (fK x ℕ.⊔ fK y) ℕ.* n)     ≡⟨ cong (λ r ->
                                               seq x (2 ℕ.* r ℕ.* n) ℚ.* seq y (2 ℕ.* r ℕ.* n))
                                               (ℕP.⊔-comm (fK x) (fK y)) ⟩
      seq x (2 ℕ.* (fK y ℕ.⊔ fK x) ℕ.* n) ℚ.*
      seq y (2 ℕ.* (fK y ℕ.⊔ fK x) ℕ.* n)     ≈⟨ ℚP.*-comm (seq x (2 ℕ.* (fK y ℕ.⊔ fK x) ℕ.* n))
                                                         (seq y (2 ℕ.* (fK y ℕ.⊔ fK x) ℕ.* n)) ⟩
      seq y (2 ℕ.* (fK y ℕ.⊔ fK x) ℕ.* n) ℚ.*
      seq x (2 ℕ.* (fK y ℕ.⊔ fK x) ℕ.* n)      ∎

    @0 lem : (n : ℕ) {n≢0 : n ≢0} → ℚ.∣ seq (x * y) n ℚ.- seq (y * x) n ∣ ℚ.≤ + 2 / n
    lem (suc k₁) = let n = suc k₁ in begin
           ℚ.∣ seq (x * y) n ℚ.- seq (y * x) n ∣ ≈⟨ ℚP.∣-∣-cong (ℚP.+-congʳ (seq (x * y) n)
                                                               (ℚP.-‿cong (ℚP.≃-sym (xyℚ≃yxℚ n)))) ⟩
           ℚ.∣ seq (x * y) n ℚ.- seq (x * y) n ∣ ≈⟨ ℚP.∣-∣-cong (ℚP.+-inverseʳ (seq (x * y) n)) ⟩
           (+ 0 / 1)                                   ≤⟨ ℚP.nonNegative⁻¹ _ ⟩
           + 2 / n                                ∎

*-assoc : Associative _≃_ _*_
*-assoc x y z = equality-lemma-onlyif (x * y * z) (x * (y * z)) lemA
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
    @0 lemA : ∀ (j : ℕ) -> {j≢0 : j ≢0} -> ∃ λ (N : ℕ) -> ∀ (n : ℕ) -> n ℕ.≥ N ->
          ℚ.∣ seq (x * y * z) n ℚ.- seq (x * (y * z)) n ∣ ℚ.≤ (+ 1 / j) {j≢0}
    lemA (suc k₁) = N , lemB
      where
        j = suc k₁
        N₁ = proj₁ (fast-regular⇒cauchy x (fK y ℕ.* fK z ℕ.* (3 ℕ.* j)))
        N₂ = proj₁ (fast-regular⇒cauchy y (fK x ℕ.* fK z ℕ.* (3 ℕ.* j)))
        N₃ = proj₁ (fast-regular⇒cauchy z (fK x ℕ.* fK y ℕ.* (3 ℕ.* j)))
        N = suc (N₁ ℕ.⊔ N₂ ℕ.⊔ N₃)

        lemB : ∀ (n : ℕ) -> n ℕ.≥ N -> ℚ.∣ seq (x * y * z) n ℚ.- seq (x * (y * z)) n ∣ ℚ.≤ + 1 / j
        lemB (suc k₂) n≥N = begin
          ℚ.∣ x₄ᵣₛₙ ℚ.* y₄ᵣₛₙ ℚ.* z₂ₛₙ ℚ.- x₂ᵤₙ ℚ.* (y₄ₜᵤₙ ℚ.* z₄ₜᵤₙ) ∣ ≈⟨ ℚP.∣-∣-cong (solve 6 (λ a b c d e f ->
                                                                           (a ⊗ b ⊗ c ⊖ d ⊗ (e ⊗ f)) ⊜
                                                                           ((b ⊗ c) ⊗ (a ⊖ d) ⊕ d ⊗ (c ⊗ (b ⊖ e) ⊕ e ⊗ (c ⊖ f))))
                                                                           ℚP.≃-refl x₄ᵣₛₙ y₄ᵣₛₙ z₂ₛₙ x₂ᵤₙ y₄ₜᵤₙ z₄ₜᵤₙ) ⟩
          ℚ.∣ (y₄ᵣₛₙ ℚ.* z₂ₛₙ) ℚ.* (x₄ᵣₛₙ ℚ.- x₂ᵤₙ) ℚ.+
          x₂ᵤₙ ℚ.* (z₂ₛₙ ℚ.* (y₄ᵣₛₙ ℚ.- y₄ₜᵤₙ) ℚ.+
          y₄ₜᵤₙ ℚ.* (z₂ₛₙ ℚ.- z₄ₜᵤₙ)) ∣                                 ≤⟨ ℚP.∣p+q∣≤∣p∣+∣q∣ ((y₄ᵣₛₙ ℚ.* z₂ₛₙ) ℚ.* (x₄ᵣₛₙ ℚ.- x₂ᵤₙ))
                                                                           (x₂ᵤₙ ℚ.* (z₂ₛₙ ℚ.* (y₄ᵣₛₙ ℚ.- y₄ₜᵤₙ) ℚ.+ y₄ₜᵤₙ ℚ.* (z₂ₛₙ ℚ.- z₄ₜᵤₙ))) ⟩
          ℚ.∣ (y₄ᵣₛₙ ℚ.* z₂ₛₙ) ℚ.* (x₄ᵣₛₙ ℚ.- x₂ᵤₙ) ∣ ℚ.+
          ℚ.∣ x₂ᵤₙ ℚ.* (z₂ₛₙ ℚ.* (y₄ᵣₛₙ ℚ.- y₄ₜᵤₙ) ℚ.+
          y₄ₜᵤₙ ℚ.* (z₂ₛₙ ℚ.- z₄ₜᵤₙ)) ∣                                 ≤⟨ ℚP.≤-respˡ-≃ (ℚP.≃-sym (ℚP.+-congʳ ℚ.∣ (y₄ᵣₛₙ ℚ.* z₂ₛₙ) ℚ.* (x₄ᵣₛₙ ℚ.- x₂ᵤₙ) ∣
                                                                           (ℚP.∣p*q∣≃∣p∣*∣q∣ x₂ᵤₙ (z₂ₛₙ ℚ.* (y₄ᵣₛₙ ℚ.- y₄ₜᵤₙ) ℚ.+ y₄ₜᵤₙ ℚ.* (z₂ₛₙ ℚ.- z₄ₜᵤₙ)))))
                                                                           (ℚP.+-monoʳ-≤ ℚ.∣ (y₄ᵣₛₙ ℚ.* z₂ₛₙ) ℚ.* (x₄ᵣₛₙ ℚ.- x₂ᵤₙ) ∣
                                                                           (ℚP.*-monoʳ-≤-nonNeg {ℚ.∣ x₂ᵤₙ ∣} _ (ℚP.∣p+q∣≤∣p∣+∣q∣
                                                                           (z₂ₛₙ ℚ.* (y₄ᵣₛₙ ℚ.- y₄ₜᵤₙ)) (y₄ₜᵤₙ ℚ.* (z₂ₛₙ ℚ.- z₄ₜᵤₙ))))) ⟩
          ℚ.∣ (y₄ᵣₛₙ ℚ.* z₂ₛₙ) ℚ.* (x₄ᵣₛₙ ℚ.- x₂ᵤₙ) ∣ ℚ.+
          ℚ.∣ x₂ᵤₙ ∣ ℚ.* (ℚ.∣ z₂ₛₙ ℚ.* (y₄ᵣₛₙ ℚ.- y₄ₜᵤₙ) ∣ ℚ.+
          ℚ.∣ y₄ₜᵤₙ ℚ.* (z₂ₛₙ ℚ.- z₄ₜᵤₙ) ∣)                             ≈⟨ ℚP.+-congˡ
                                                                          (ℚ.∣ x₂ᵤₙ ∣ ℚ.* (ℚ.∣ z₂ₛₙ ℚ.* (y₄ᵣₛₙ ℚ.- y₄ₜᵤₙ) ∣ ℚ.+  ℚ.∣ y₄ₜᵤₙ ℚ.* (z₂ₛₙ ℚ.- z₄ₜᵤₙ) ∣))
                                                                          (ℚP.≃-trans (ℚP.∣p*q∣≃∣p∣*∣q∣ (y₄ᵣₛₙ ℚ.* z₂ₛₙ) (x₄ᵣₛₙ ℚ.- x₂ᵤₙ))
                                                                          (ℚP.*-congʳ (ℚP.∣p*q∣≃∣p∣*∣q∣ y₄ᵣₛₙ z₂ₛₙ))) ⟩
          ℚ.∣ y₄ᵣₛₙ ∣ ℚ.* ℚ.∣ z₂ₛₙ ∣ ℚ.* ℚ.∣ x₄ᵣₛₙ ℚ.- x₂ᵤₙ ∣ ℚ.+
          ℚ.∣ x₂ᵤₙ ∣ ℚ.* (ℚ.∣ z₂ₛₙ ℚ.* (y₄ᵣₛₙ ℚ.- y₄ₜᵤₙ) ∣ ℚ.+
          ℚ.∣ y₄ₜᵤₙ ℚ.* (z₂ₛₙ ℚ.- z₄ₜᵤₙ) ∣)                             ≈⟨ ℚP.+-congʳ (ℚ.∣ y₄ᵣₛₙ ∣ ℚ.* ℚ.∣ z₂ₛₙ ∣ ℚ.* ℚ.∣ x₄ᵣₛₙ ℚ.- x₂ᵤₙ ∣)
                                                                           (ℚP.*-distribˡ-+ ℚ.∣ x₂ᵤₙ ∣ ℚ.∣ z₂ₛₙ ℚ.* (y₄ᵣₛₙ ℚ.- y₄ₜᵤₙ) ∣
                                                                           ℚ.∣ y₄ₜᵤₙ ℚ.* (z₂ₛₙ ℚ.- z₄ₜᵤₙ) ∣) ⟩
          ℚ.∣ y₄ᵣₛₙ ∣ ℚ.* ℚ.∣ z₂ₛₙ ∣ ℚ.* ℚ.∣ x₄ᵣₛₙ ℚ.- x₂ᵤₙ ∣ ℚ.+
          (ℚ.∣ x₂ᵤₙ ∣ ℚ.* ℚ.∣ z₂ₛₙ ℚ.* (y₄ᵣₛₙ ℚ.- y₄ₜᵤₙ) ∣ ℚ.+
          ℚ.∣ x₂ᵤₙ ∣ ℚ.* ℚ.∣ y₄ₜᵤₙ ℚ.* (z₂ₛₙ ℚ.- z₄ₜᵤₙ) ∣)              ≤⟨ ℚP.≤-trans (ℚP.+-monoʳ-≤ (ℚ.∣ y₄ᵣₛₙ ∣ ℚ.* ℚ.∣ z₂ₛₙ ∣ ℚ.* ℚ.∣ x₄ᵣₛₙ ℚ.- x₂ᵤₙ ∣)
                                                                          (ℚP.≤-trans (ℚP.+-monoʳ-≤ (ℚ.∣ x₂ᵤₙ ∣ ℚ.* ℚ.∣ z₂ₛₙ ℚ.* (y₄ᵣₛₙ ℚ.- y₄ₜᵤₙ) ∣) part3)
                                                                          (ℚP.+-monoˡ-≤ (+ 1 / (3 ℕ.* j)) part2)))
                                                                          (ℚP.+-monoˡ-≤ (+ 1 / (3 ℕ.* j) ℚ.+ + 1 / (3 ℕ.* j)) part1) ⟩
          (+ 1 / (3 ℕ.* j)) ℚ.+ ((+ 1 / (3 ℕ.* j)) ℚ.+ (+ 1 / (3 ℕ.* j))) ≈⟨ ℚ.*≡* (ℤsolve 1 (λ j ->

          (κ (+ 1) :* ((κ (+ 3) :* j) :* (κ (+ 3) :* j)) :+ ((κ (+ 1) :* (κ (+ 3) :* j)) :+ (κ (+ 1) :* (κ (+ 3) :* j))) :* (κ (+ 3) :* j)) :* j :=
          (κ (+ 1) :* ((κ (+ 3) :* j) :* ((κ (+ 3) :* j) :* (κ (+ 3) :* j)))))
          
          refl (+ j)) ⟩
          + 1 / j                                                        ∎
          where
            n = suc k₂
            r = fK x ℕ.⊔ fK y
            s = fK (x * y) ℕ.⊔ fK z
            u = fK x ℕ.⊔ fK (y * z)
            t = fK y ℕ.⊔ fK z

            x₄ᵣₛₙ = seq x (2 ℕ.* r ℕ.* (2 ℕ.* s ℕ.* n))
            y₄ᵣₛₙ = seq y (2 ℕ.* r ℕ.* (2 ℕ.* s ℕ.* n))
            z₂ₛₙ = seq z (2 ℕ.* s ℕ.* n)
            x₂ᵤₙ = seq x (2 ℕ.* u ℕ.* n)
            y₄ₜᵤₙ = seq y (2 ℕ.* t ℕ.* (2 ℕ.* u ℕ.* n))
            z₄ₜᵤₙ = seq z (2 ℕ.* t ℕ.* (2 ℕ.* u ℕ.* n))

            N≤2an : ∀ (a : ℕ) -> {a ≢0} -> N ℕ.≤ 2 ℕ.* a ℕ.* n
            N≤2an (suc a) = ℕP.≤-trans n≥N (ℕP.m≤n*m n {2 ℕ.* (suc a)} ℕP.0<1+n)

            N≤4abn : ∀ (a b : ℕ) -> {a ≢0} -> {b ≢0} -> N ℕ.≤ 2 ℕ.* a ℕ.* (2 ℕ.* b ℕ.* n)
            N≤4abn (suc a) (suc b) = let a = suc a; b = suc b in
                                     ℕP.≤-trans (N≤2an b) (ℕP.m≤n*m (2 ℕ.* b ℕ.* n) {2 ℕ.* a} ℕP.0<1+n)

            N₁≤_ : {m : ℕ} -> N ℕ.≤ m -> N₁ ℕ.≤ m
            N₁≤ N≤m = ℕP.≤-trans (ℕP.≤-trans (ℕP.m≤m⊔n N₁ N₂) (ℕP.≤-trans (ℕP.m≤m⊔n (N₁ ℕ.⊔ N₂) N₃) (ℕP.n≤1+n (ℕ.pred N)))) N≤m

            N₂≤_ : {m : ℕ} -> N ℕ.≤ m -> N₂ ℕ.≤ m
            N₂≤_ N≤m = ℕP.≤-trans (ℕP.≤-trans (ℕP.m≤n⊔m N₁ N₂) (ℕP.≤-trans (ℕP.m≤m⊔n (N₁ ℕ.⊔ N₂) N₃) (ℕP.n≤1+n (ℕ.pred N)))) N≤m

            N₃≤ : {m : ℕ} -> N ℕ.≤ m -> N₃ ℕ.≤ m
            N₃≤ N≤m = ℕP.≤-trans (ℕP.≤-trans (ℕP.m≤n⊔m (N₁ ℕ.⊔ N₂) N₃) (ℕP.n≤1+n (ℕ.pred N))) N≤m

            part1 : ℚ.∣ y₄ᵣₛₙ ∣ ℚ.* ℚ.∣ z₂ₛₙ ∣ ℚ.* ℚ.∣ x₄ᵣₛₙ ℚ.- x₂ᵤₙ ∣ ℚ.≤ + 1 / (3 ℕ.* j)
            part1 = begin
              ℚ.∣ y₄ᵣₛₙ ∣ ℚ.* ℚ.∣ z₂ₛₙ ∣ ℚ.* ℚ.∣ x₄ᵣₛₙ ℚ.- x₂ᵤₙ ∣            ≤⟨ ℚP.*-monoˡ-≤-nonNeg {ℚ.∣ x₄ᵣₛₙ ℚ.- x₂ᵤₙ ∣} _ (ℚP.≤-trans
                                                                               (ℚP.*-monoˡ-≤-nonNeg {ℚ.∣ z₂ₛₙ ∣} _ (ℚP.<⇒≤
                                                                               (canonical-strict-upper-bound y (2 ℕ.* r ℕ.* (2 ℕ.* s ℕ.* n)))))
                                                                               (ℚP.*-monoʳ-≤-nonNeg {(+ fK y) / 1} _ (ℚP.<⇒≤
                                                                               (canonical-strict-upper-bound z (2 ℕ.* s ℕ.* n))))) ⟩
              (+ (fK y ℕ.* fK z) / 1) ℚ.* ℚ.∣ x₄ᵣₛₙ ℚ.- x₂ᵤₙ ∣                ≤⟨ ℚP.*-monoʳ-≤-nonNeg {+ (fK y ℕ.* fK z) / 1} _
                                                                               (proj₂ (fast-regular⇒cauchy x (fK y ℕ.* fK z ℕ.* (3 ℕ.* j)))
                                                                               (2 ℕ.* r ℕ.* (2 ℕ.* s ℕ.* n)) (2 ℕ.* u ℕ.* n)
                                                                               (N₁≤ (N≤4abn r s))
                                                                               (N₁≤ (N≤2an u))) ⟩
              (+ (fK y ℕ.* fK z) / 1) ℚ.* (+ 1 / (fK y ℕ.* fK z ℕ.* (3 ℕ.* j))) ≈⟨ ℚ.*≡* (ℤsolve 3 (λ Ky Kz j ->
                                                                               ((Ky :* Kz) :* κ (+ 1)) :* (κ (+ 3) :* j) :=
                                                                               (κ (+ 1) :* (κ (+ 1) :* (Ky :* Kz :* (κ (+ 3) :* j)))))
                                                                               refl (+ fK y) (+ fK z) (+ j)) ⟩
              + 1 / (3 ℕ.* j)                                                ∎

            part2 : ℚ.∣ x₂ᵤₙ ∣ ℚ.* ℚ.∣ z₂ₛₙ ℚ.* (y₄ᵣₛₙ ℚ.- y₄ₜᵤₙ) ∣ ℚ.≤ + 1 / (3 ℕ.* j)
            part2 = begin
              ℚ.∣ x₂ᵤₙ ∣ ℚ.* ℚ.∣ z₂ₛₙ ℚ.* (y₄ᵣₛₙ ℚ.- y₄ₜᵤₙ) ∣     ≈⟨ ℚP.≃-trans (ℚP.*-congˡ {ℚ.∣ x₂ᵤₙ ∣} (ℚP.∣p*q∣≃∣p∣*∣q∣ z₂ₛₙ (y₄ᵣₛₙ ℚ.- y₄ₜᵤₙ)))
                                                                    (ℚP.≃-sym (ℚP.*-assoc ℚ.∣ x₂ᵤₙ ∣ ℚ.∣ z₂ₛₙ ∣ ℚ.∣ y₄ᵣₛₙ ℚ.- y₄ₜᵤₙ ∣)) ⟩
              ℚ.∣ x₂ᵤₙ ∣ ℚ.* ℚ.∣ z₂ₛₙ ∣ ℚ.* ℚ.∣ y₄ᵣₛₙ ℚ.- y₄ₜᵤₙ ∣ ≤⟨ ℚP.*-monoˡ-≤-nonNeg {ℚ.∣ y₄ᵣₛₙ ℚ.- y₄ₜᵤₙ ∣} _ (ℚP.≤-trans
                                                                    (ℚP.*-monoˡ-≤-nonNeg {ℚ.∣ z₂ₛₙ ∣} _
                                                                    (ℚP.<⇒≤ (canonical-strict-upper-bound x (2 ℕ.* u ℕ.* n))))
                                                                    (ℚP.*-monoʳ-≤-nonNeg {+ fK x / 1} _
                                                                    (ℚP.<⇒≤ (canonical-strict-upper-bound z (2 ℕ.* s ℕ.* n))))) ⟩
              (+ (fK x ℕ.* fK z) / 1) ℚ.* ℚ.∣ y₄ᵣₛₙ ℚ.- y₄ₜᵤₙ ∣    ≤⟨ ℚP.*-monoʳ-≤-nonNeg {+ (fK x ℕ.* fK z) / 1} _
                                                                    (proj₂ (fast-regular⇒cauchy y (fK x ℕ.* fK z ℕ.* (3 ℕ.* j)))
                                                                    (2 ℕ.* r ℕ.* (2 ℕ.* s ℕ.* n)) (2 ℕ.* t ℕ.* (2 ℕ.* u ℕ.* n))
                                                                    (N₂≤ (N≤4abn r s))
                                                                    (N₂≤ (N≤4abn t u))) ⟩
              (+ (fK x ℕ.* fK z) / 1) ℚ.*
              (+ 1 / (fK x ℕ.* fK z ℕ.* (3 ℕ.* j)))                ≈⟨ ℚ.*≡* (ℤsolve 3 (λ Kx Kz j ->
                                                                    (Kx :* Kz :* κ (+ 1)) :* (κ (+ 3) :* j) :=
                                                                    (κ (+ 1) :* (κ (+ 1) :* (Kx :* Kz :* (κ (+ 3) :* j)))))
                                                                    refl (+ fK x) (+ fK z) (+ j)) ⟩
              + 1 / (3 ℕ.* j)                                     ∎

            part3 : ℚ.∣ x₂ᵤₙ ∣ ℚ.* ℚ.∣ y₄ₜᵤₙ ℚ.* (z₂ₛₙ ℚ.- z₄ₜᵤₙ) ∣ ℚ.≤ + 1 / (3 ℕ.* j)
            part3 = begin
              ℚ.∣ x₂ᵤₙ ∣ ℚ.* ℚ.∣ y₄ₜᵤₙ ℚ.* (z₂ₛₙ ℚ.- z₄ₜᵤₙ) ∣     ≈⟨ ℚP.≃-trans (ℚP.*-congˡ {ℚ.∣ x₂ᵤₙ ∣} (ℚP.∣p*q∣≃∣p∣*∣q∣ y₄ₜᵤₙ (z₂ₛₙ ℚ.- z₄ₜᵤₙ)))
                                                                    (ℚP.≃-sym (ℚP.*-assoc ℚ.∣ x₂ᵤₙ ∣ ℚ.∣ y₄ₜᵤₙ ∣ ℚ.∣ z₂ₛₙ ℚ.- z₄ₜᵤₙ ∣)) ⟩
              ℚ.∣ x₂ᵤₙ ∣ ℚ.* ℚ.∣ y₄ₜᵤₙ ∣ ℚ.* ℚ.∣ z₂ₛₙ ℚ.- z₄ₜᵤₙ ∣ ≤⟨ ℚP.*-monoˡ-≤-nonNeg {ℚ.∣ z₂ₛₙ ℚ.- z₄ₜᵤₙ ∣} _ (ℚP.≤-trans
                                                                    (ℚP.*-monoˡ-≤-nonNeg {ℚ.∣ y₄ₜᵤₙ ∣} _
                                                                    (ℚP.<⇒≤ (canonical-strict-upper-bound x (2 ℕ.* u ℕ.* n))))
                                                                    (ℚP.*-monoʳ-≤-nonNeg {+ fK x / 1} _
                                                                    (ℚP.<⇒≤ (canonical-strict-upper-bound y (2 ℕ.* t ℕ.* (2 ℕ.* u ℕ.* n)))))) ⟩
              (+ (fK x ℕ.* fK y) / 1) ℚ.* ℚ.∣ z₂ₛₙ ℚ.- z₄ₜᵤₙ ∣      ≤⟨ ℚP.*-monoʳ-≤-nonNeg {+ (fK x ℕ.* fK y) / 1} _
                                                                     (proj₂ (fast-regular⇒cauchy z (fK x ℕ.* fK y ℕ.* (3 ℕ.* j)))
                                                                     (2 ℕ.* s ℕ.* n) (2 ℕ.* t ℕ.* (2 ℕ.* u ℕ.* n))
                                                                     (N₃≤ (N≤2an s))
                                                                     (N₃≤ (N≤4abn t u))) ⟩
              (+ (fK x ℕ.* fK y) / 1) ℚ.*
              (+ 1 / (fK x ℕ.* fK y ℕ.* (3 ℕ.* j)))                 ≈⟨ ℚ.*≡* (ℤsolve 3 (λ Kx Ky j ->
                                                                     (((Kx :* Ky) :* κ (+ 1)) :* (κ (+ 3) :* j)) :=
                                                                     (κ (+ 1) :* (κ (+ 1) :* (Kx :* Ky :* (κ (+ 3) :* j)))))
                                                                     refl (+ fK x) (+ fK y) (+ j)) ⟩
              + 1 / (3 ℕ.* j)                                      ∎

*-distribˡ-+ : _DistributesOverˡ_ _≃_ _*_ _+_
*-distribˡ-+ x y z = equality-lemma-onlyif (x * (y + z)) ((x * y) + (x * z)) lemA
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

    @0 lemA : ∀ (j : ℕ) -> {j≢0 : j ≢0} -> ∃ λ (N : ℕ) -> ∀ (n : ℕ) -> n ℕ.≥ N ->
           ℚ.∣ seq (x * (y + z)) n ℚ.- seq ((x * y) + (x * z)) n ∣ ℚ.≤ (+ 1 / j) {j≢0}
    lemA (suc k₁) = N , lemB
      where
        j = suc k₁
        r = fK x ℕ.⊔ fK (y + z)
        s = fK x ℕ.⊔ fK y
        t = fK x ℕ.⊔ fK z
        N₁ = proj₁ (fast-regular⇒cauchy x (fK y ℕ.* (4 ℕ.* j)))
        N₂ = proj₁ (fast-regular⇒cauchy y (fK x ℕ.* (4 ℕ.* j)))
        N₃ = proj₁ (fast-regular⇒cauchy x (fK z ℕ.* (4 ℕ.* j)))
        N₄ = proj₁ (fast-regular⇒cauchy z (fK x ℕ.* (4 ℕ.* j)))
        N = suc (N₁ ℕ.⊔ N₂ ℕ.⊔ N₃ ℕ.⊔ N₄)

        lemB : ∀ (n : ℕ) -> n ℕ.≥ N ->
               ℚ.∣ seq (x * (y + z)) n ℚ.- seq ((x * y) + (x * z)) n ∣ ℚ.≤ + 1 / j
        lemB (suc k₂) n≥N = let x₂ᵣₙ = seq x (2 ℕ.* r ℕ.* n)
                                      ; x₄ₛₙ = seq x (2 ℕ.* s ℕ.* (2 ℕ.* n))
                                      ; x₄ₜₙ = seq x (2 ℕ.* t ℕ.* (2 ℕ.* n))
                                      ; y₄ᵣₙ = seq y (2 ℕ.* (2 ℕ.* r ℕ.* n))
                                      ; y₄ₛₙ = seq y (2 ℕ.* s ℕ.* (2 ℕ.* n))
                                      ; z₄ᵣₙ = seq z (2 ℕ.* (2 ℕ.* r ℕ.* n))
                                      ; z₄ₜₙ = seq z (2 ℕ.* t ℕ.* (2 ℕ.* n)) in begin
          ℚ.∣ x₂ᵣₙ ℚ.* (y₄ᵣₙ ℚ.+ z₄ᵣₙ) ℚ.-
            (x₄ₛₙ ℚ.* y₄ₛₙ ℚ.+ x₄ₜₙ ℚ.* z₄ₜₙ) ∣             ≈⟨ ℚP.∣-∣-cong (solve 7 (λ a b c d e f g ->
                                                               (a ⊗ (b ⊕ c) ⊖ (d ⊗ e ⊕ f ⊗ g)) ⊜
                                                               ((b ⊗ (a ⊖ d) ⊕ (d ⊗ (b ⊖ e)) ⊕
                                                               ((c ⊗ (a ⊖ f)) ⊕ (f ⊗ (c ⊖ g))))))
                                                               ℚP.≃-refl
                                                               x₂ᵣₙ y₄ᵣₙ z₄ᵣₙ x₄ₛₙ y₄ₛₙ x₄ₜₙ z₄ₜₙ) ⟩

           ℚ.∣ y₄ᵣₙ ℚ.* (x₂ᵣₙ ℚ.- x₄ₛₙ) ℚ.+
              x₄ₛₙ ℚ.* (y₄ᵣₙ ℚ.- y₄ₛₙ) ℚ.+
             (z₄ᵣₙ ℚ.* (x₂ᵣₙ ℚ.- x₄ₜₙ) ℚ.+
              x₄ₜₙ ℚ.* (z₄ᵣₙ ℚ.- z₄ₜₙ)) ∣                   ≤⟨ ℚP.≤-trans (ℚP.∣p+q∣≤∣p∣+∣q∣
                                                               (y₄ᵣₙ ℚ.* (x₂ᵣₙ ℚ.- x₄ₛₙ) ℚ.+ x₄ₛₙ ℚ.* (y₄ᵣₙ ℚ.- y₄ₛₙ))
                                                               (z₄ᵣₙ ℚ.* (x₂ᵣₙ ℚ.- x₄ₜₙ) ℚ.+ x₄ₜₙ ℚ.* (z₄ᵣₙ ℚ.- z₄ₜₙ)))
                                                               (ℚP.+-mono-≤
                                                               (ℚP.∣p+q∣≤∣p∣+∣q∣ (y₄ᵣₙ ℚ.* (x₂ᵣₙ ℚ.- x₄ₛₙ)) ( x₄ₛₙ ℚ.* (y₄ᵣₙ ℚ.- y₄ₛₙ)))
                                                               (ℚP.∣p+q∣≤∣p∣+∣q∣ (z₄ᵣₙ ℚ.* (x₂ᵣₙ ℚ.- x₄ₜₙ)) ( x₄ₜₙ ℚ.* (z₄ᵣₙ ℚ.- z₄ₜₙ)))) ⟩
           ℚ.∣ y₄ᵣₙ ℚ.* (x₂ᵣₙ ℚ.- x₄ₛₙ) ∣ ℚ.+
           ℚ.∣ x₄ₛₙ ℚ.* (y₄ᵣₙ ℚ.- y₄ₛₙ) ∣ ℚ.+
          (ℚ.∣ z₄ᵣₙ ℚ.* (x₂ᵣₙ ℚ.- x₄ₜₙ) ∣ ℚ.+
           ℚ.∣ x₄ₜₙ ℚ.* (z₄ᵣₙ ℚ.- z₄ₜₙ) ∣)                  ≈⟨ ℚP.+-cong (ℚP.+-cong (ℚP.∣p*q∣≃∣p∣*∣q∣ y₄ᵣₙ (x₂ᵣₙ ℚ.- x₄ₛₙ))
                                                                                    (ℚP.∣p*q∣≃∣p∣*∣q∣ x₄ₛₙ (y₄ᵣₙ ℚ.- y₄ₛₙ)))
                                                                         (ℚP.+-cong (ℚP.∣p*q∣≃∣p∣*∣q∣ z₄ᵣₙ (x₂ᵣₙ ℚ.- x₄ₜₙ))
                                                                                    (ℚP.∣p*q∣≃∣p∣*∣q∣ x₄ₜₙ (z₄ᵣₙ ℚ.- z₄ₜₙ))) ⟩
           ℚ.∣ y₄ᵣₙ ∣ ℚ.* ℚ.∣ x₂ᵣₙ ℚ.- x₄ₛₙ ∣ ℚ.+
           ℚ.∣ x₄ₛₙ ∣ ℚ.* ℚ.∣ y₄ᵣₙ ℚ.- y₄ₛₙ ∣ ℚ.+
          (ℚ.∣ z₄ᵣₙ ∣ ℚ.* ℚ.∣ x₂ᵣₙ ℚ.- x₄ₜₙ ∣ ℚ.+
           ℚ.∣ x₄ₜₙ ∣ ℚ.* ℚ.∣ z₄ᵣₙ ℚ.- z₄ₜₙ ∣)               ≤⟨ ℚP.+-mono-≤
                                                                (ℚP.+-mono-≤
                                                                            (ℚP.≤-trans
                                                                            (ℚP.*-monoˡ-≤-nonNeg {ℚ.∣ x₂ᵣₙ ℚ.- x₄ₛₙ ∣} _
                                                                                                 (ℚP.<⇒≤ (canonical-strict-upper-bound y
                                                                                                         (2 ℕ.* (2 ℕ.* r ℕ.* n)))))
                                                                            (ℚP.*-monoʳ-≤-nonNeg {+ fK y / 1} _
                                                                                                 (proj₂ (fast-regular⇒cauchy x (fK y ℕ.* (4 ℕ.* j)))
                                                                                                 (2 ℕ.* r ℕ.* n) (2 ℕ.* s ℕ.* (2 ℕ.* n))
                                                                                                 (N₁≤ N≤2rn) (N₁≤ N≤4sn))))
                                                                            (ℚP.≤-trans
                                                                            (ℚP.*-monoˡ-≤-nonNeg {ℚ.∣ y₄ᵣₙ ℚ.- y₄ₛₙ ∣} _
                                                                                                 (ℚP.<⇒≤ (canonical-strict-upper-bound x
                                                                                                         (2 ℕ.* s ℕ.* (2 ℕ.* n)))))
                                                                            (ℚP.*-monoʳ-≤-nonNeg {+ fK x / 1} _
                                                                                                 (proj₂ (fast-regular⇒cauchy y (fK x ℕ.* (4 ℕ.* j)))
                                                                                                 (2 ℕ.* (2 ℕ.* r ℕ.* n)) (2 ℕ.* s ℕ.* (2 ℕ.* n))
                                                                                                 (N₂≤ N≤4rn) (N₂≤ N≤4sn)))))
                                                                (ℚP.+-mono-≤
                                                                            (ℚP.≤-trans
                                                                            (ℚP.*-monoˡ-≤-nonNeg {ℚ.∣ x₂ᵣₙ ℚ.- x₄ₜₙ ∣} _
                                                                                                 (ℚP.<⇒≤ (canonical-strict-upper-bound z
                                                                                                         (2 ℕ.* (2 ℕ.* r ℕ.* n)))))
                                                                            (ℚP.*-monoʳ-≤-nonNeg {+ fK z / 1} _
                                                                                                  (proj₂ (fast-regular⇒cauchy x (fK z ℕ.* (4 ℕ.* j)))
                                                                                                  (2 ℕ.* r ℕ.* n) (2 ℕ.* t ℕ.* (2 ℕ.* n))
                                                                                                  (N₃≤ N≤2rn) (N₃≤ N≤4tn))))
                                                                            (ℚP.≤-trans
                                                                            (ℚP.*-monoˡ-≤-nonNeg {ℚ.∣ z₄ᵣₙ ℚ.- z₄ₜₙ ∣} _
                                                                                                 (ℚP.<⇒≤ (canonical-strict-upper-bound x
                                                                                                         (2 ℕ.* t ℕ.* (2 ℕ.* n)))))
                                                                            (ℚP.*-monoʳ-≤-nonNeg {+ fK x / 1} _
                                                                                                 (proj₂ (fast-regular⇒cauchy z (fK x ℕ.* (4 ℕ.* j)))
                                                                                                 (2 ℕ.* (2 ℕ.* r ℕ.* n)) (2 ℕ.* t ℕ.* (2 ℕ.* n))
                                                                                                 (N₄≤ N≤4rn) (N₄≤ N≤4tn))))) ⟩
           (+ fK y / 1) ℚ.* (+ 1 / (fK y ℕ.* (4 ℕ.* j))) ℚ.+
           (+ fK x / 1) ℚ.* (+ 1 / (fK x ℕ.* (4 ℕ.* j))) ℚ.+
          ((+ fK z / 1) ℚ.* (+ 1 / (fK z ℕ.* (4 ℕ.* j))) ℚ.+
           (+ fK x / 1) ℚ.* (+ 1 / (fK x ℕ.* (4 ℕ.* j))))     ≈⟨ ℚ.*≡* (ℤsolve 4 (λ Kx Ky Kz j ->

          {- Function for solver -}
          (((Ky :* κ (+ 1)) :* (κ (+ 1) :* (Kx :* (κ (+ 4) :* j))) :+ ((Kx :* κ (+ 1)) :* (κ (+ 1) :* (Ky :* (κ (+ 4) :* j))))) :*
          ((κ (+ 1) :* (Kz :* (κ (+ 4) :* j))) :* (κ (+ 1) :* (Kx :* (κ (+ 4) :* j)))) :+
          (((Kz :* κ (+ 1)) :* (κ (+ 1) :* (Kx :* (κ (+ 4) :* j)))) :+ ((Kx :* κ (+ 1)) :* (κ (+ 1) :* (Kz :* (κ (+ 4) :* j))))) :*
          ((κ (+ 1) :* (Ky :* (κ (+ 4) :* j))) :* (κ (+ 1) :* (Kx :* (κ (+ 4) :* j))))) :* j :=
          κ (+ 1) :* (((κ (+ 1) :* (Ky :* (κ (+ 4) :* j))) :* (κ (+ 1) :* (Kx :* (κ (+ 4) :* j)))) :*
          ((κ (+ 1) :* (Kz :* (κ (+ 4) :* j))) :* (κ (+ 1) :* (Kx :* (κ (+ 4) :* j))))))
          refl (+ fK x) (+ fK y) (+ fK z) (+ j)) ⟩
          + 1 / j                                            ∎
          where
            n : ℕ
            n = suc k₂

            N≤2rn : N ℕ.≤ 2 ℕ.* r ℕ.* n
            N≤2rn = ℕP.≤-trans n≥N (ℕP.m≤n*m n {2 ℕ.* r} ℕP.0<1+n)

            N≤4sn : N ℕ.≤ 2 ℕ.* s ℕ.* (2 ℕ.* n)
            N≤4sn = ℕP.≤-trans (ℕP.≤-trans n≥N (ℕP.m≤n*m n {2} ℕP.0<1+n)) (ℕP.m≤n*m (2 ℕ.* n) {2 ℕ.* s} ℕP.0<1+n)

            N≤4rn : N ℕ.≤ 2 ℕ.* (2 ℕ.* r ℕ.* n)
            N≤4rn = ℕP.≤-trans (ℕP.≤-trans n≥N (ℕP.m≤n*m n {2 ℕ.* r} ℕP.0<1+n)) (ℕP.m≤n*m (2 ℕ.* r ℕ.* n) {2} ℕP.0<1+n)

            N≤4tn : N ℕ.≤ 2 ℕ.* t ℕ.* (2 ℕ.* n)
            N≤4tn = ℕP.≤-trans (ℕP.≤-trans n≥N (ℕP.m≤n*m n {2} ℕP.0<1+n)) (ℕP.m≤n*m (2 ℕ.* n) {2 ℕ.* t} ℕP.0<1+n)

            N₁≤_ : {m : ℕ} -> N ℕ.≤ m -> N₁ ℕ.≤ m
            N₁≤ N≤m = ℕP.≤-trans (ℕP.≤-trans (ℕP.≤-trans (ℕP.m≤m⊔n N₁ N₂) (ℕP.m≤m⊔n (N₁ ℕ.⊔ N₂) N₃))
                      (ℕP.≤-trans (ℕP.m≤m⊔n (N₁ ℕ.⊔ N₂ ℕ.⊔ N₃) N₄) (ℕP.n≤1+n (ℕ.pred N)))) N≤m

            N₂≤_ : {m : ℕ} -> N ℕ.≤ m -> N₂ ℕ.≤ m
            N₂≤ N≤m = ℕP.≤-trans (ℕP.≤-trans (ℕP.≤-trans (ℕP.m≤n⊔m N₁ N₂) (ℕP.m≤m⊔n (N₁ ℕ.⊔ N₂) N₃))
                      (ℕP.≤-trans (ℕP.m≤m⊔n (N₁ ℕ.⊔ N₂ ℕ.⊔ N₃) N₄) (ℕP.n≤1+n (ℕ.pred N)))) N≤m

            N₃≤_ : {m : ℕ} -> N ℕ.≤ m -> N₃ ℕ.≤ m
            N₃≤ N≤m = ℕP.≤-trans (ℕP.≤-trans (ℕP.≤-trans (ℕP.m≤n⊔m (N₁ ℕ.⊔ N₂) N₃) (ℕP.m≤m⊔n (N₁ ℕ.⊔ N₂ ℕ.⊔ N₃) N₄))
                      (ℕP.n≤1+n (ℕ.pred N))) N≤m

            N₄≤_ : {m : ℕ} -> N ℕ.≤ m -> N₄ ℕ.≤ m
            N₄≤ N≤m = ℕP.≤-trans (ℕP.≤-trans (ℕP.m≤n⊔m (N₁ ℕ.⊔ N₂ ℕ.⊔ N₃) N₄) (ℕP.n≤1+n (ℕ.pred N))) N≤m

*-distribʳ-+ : _DistributesOverʳ_ _≃_ _*_ _+_
*-distribʳ-+ x y z = begin
  (y + z) * x   ≈⟨ *-comm (y + z) x ⟩
  x * (y + z)   ≈⟨ *-distribˡ-+ x y z ⟩
  x * y + x * z ≈⟨ +-cong (*-comm x y) (*-comm x z) ⟩
  y * x + z * x  ∎
  where open ≃-Reasoning

*-distrib-+ : _DistributesOver_ _≃_ _*_ _+_
*-distrib-+ = *-distribˡ-+ , *-distribʳ-+

*-identityˡ : LeftIdentity _≃_ oneℝ _*_
*-identityˡ x = *≃* lem
  where
    open ℚP.≤-Reasoning
    open ℤ-Solver

    @0 lem : (n : ℕ) {n≢0 : n ≢0} → ℚ.∣ seq (oneℝ * x) n ℚ.- seq x n ∣ ℚ.≤ + 2 / n
    lem (suc k₁) = let n = suc k₁; k = fK oneℝ ℕ.⊔ fK x in begin
           ℚ.∣ (+ 1 / 1) ℚ.* seq x (2 ℕ.* k ℕ.* n) ℚ.- seq x n ∣ ≈⟨ ℚP.∣-∣-cong (ℚP.+-congˡ (ℚ.- seq x n) (ℚP.*-identityˡ (seq x (2 ℕ.* k ℕ.* n)))) ⟩
           ℚ.∣ seq x (2 ℕ.* k ℕ.* n) ℚ.- seq x n ∣         ≤⟨ reg x (2 ℕ.* k ℕ.* n) n ⟩
           (+ 1 / (2 ℕ.* k ℕ.* n)) ℚ.+ (+ 1 / n)           ≤⟨ ℚP.+-monoˡ-≤ (+ 1 / n) {+ 1 / (2 ℕ.* k ℕ.* n)} {+ 1 / n} (ℚ.*≤* (ℤP.*-monoˡ-≤-nonNeg 1 (ℤ.+≤+ (ℕP.m≤n*m n {2 ℕ.* k} ℕP.0<1+n)))) ⟩
           (+ 1 / n) ℚ.+ (+ 1 / n)                         ≈⟨ ℚ.*≡* (solve 1 (λ n ->
                                                                    ((Κ (+ 1) ⊗ n ⊕ Κ (+ 1) ⊗ n) ⊗ n) ⊜ (Κ (+ 2) ⊗ (n ⊗ n)))
                                                                    refl (+ n)) ⟩
           + 2 / n                                          ∎

*-identityʳ : RightIdentity _≃_ oneℝ _*_
*-identityʳ x = ≃-trans (*-comm x oneℝ) (*-identityˡ x)

*-identity : Identity _≃_ oneℝ _*_
*-identity = *-identityˡ , *-identityʳ

*-zeroˡ : LeftZero _≃_ zeroℝ _*_
*-zeroˡ x = *≃* (λ @0 { (suc k₁) -> let n = suc k₁; k = fK zeroℝ ℕ.⊔ fK x in begin
  ℚ.∣ (+ 0 / 1) ℚ.* seq x (2 ℕ.* k ℕ.* n) ℚ.- (+ 0 / 1) ∣ ≈⟨ ℚP.∣-∣-cong (ℚP.+-congˡ (ℚ.- (+ 0 / 1)) (ℚP.*-zeroˡ (seq x (2 ℕ.* k ℕ.* n)))) ⟩
  (+ 0 / 1)                                         ≤⟨ ℚ.*≤* (ℤP.≤-trans (ℤP.≤-reflexive (ℤP.*-zeroˡ (+ n))) (ℤ.+≤+ ℕ.z≤n)) ⟩
  + 2 / n                                      ∎})
  where open ℚP.≤-Reasoning

*-zeroʳ : RightZero _≃_ zeroℝ _*_
*-zeroʳ x = ≃-trans (*-comm x zeroℝ) (*-zeroˡ x)

*-zero : Zero _≃_ zeroℝ _*_
*-zero = *-zeroˡ , *-zeroʳ

-- Properties of negate

-‿cong : Congruent₁ _≃_ (-_)
-‿cong {x} {y} (*≃* x₁) = *≃* lem
  where
    open ℚP.≤-Reasoning

    @0 lem : (n : ℕ) {n≢0 : n ≢0} → ℚ.∣ seq ((-_ Function.Base.-⟨ Function.Base.const ∣) x y) n ℚ.- seq ((Function.Base.∣ Function.Base.constᵣ ⟩- -_) x y) n ∣
          ℚ.≤ + 2 / n
    lem (suc k₁) = let n = suc k₁ in begin
             ℚ.∣ ℚ.- seq x n ℚ.- (ℚ.- seq y n) ∣ ≡⟨ trans (cong (λ x → ℚ.∣ x ∣) (sym (ℚP.neg-distrib-+ (seq x n) (ℚ.- seq y n))))
                                                          (ℚP.∣-p∣≡∣p∣ (seq x n ℚ.- seq y n)) ⟩
             ℚ.∣ seq x n ℚ.- seq y n ∣           ≤⟨ x₁ n ⟩
             + 2 / n                              ∎

@0 neg-involutive : Involutive _≃_ (-_)
neg-involutive x = *≃* λ { (suc k₁) -> let n = suc k₁ in begin
  ℚ.∣ ℚ.- (ℚ.- seq x n) ℚ.- seq x n ∣ ≈⟨ ℚP.∣-∣-cong (ℚP.+-inverseˡ (ℚ.- seq x n)) ⟩
  (+ 0 / 1)                                 ≤⟨ ℚP.nonNegative⁻¹ _ ⟩
  + 2 / n                              ∎}
  where open ℚP.≤-Reasoning

@0 neg-distrib-+ : ∀ x y -> - (x + y) ≃ - x + - y
neg-distrib-+ x y = *≃* (λ { (suc k₁) -> let n = suc k₁ in begin
  ℚ.∣ ℚ.- (seq x (2 ℕ.* n) ℚ.+ seq y (2 ℕ.* n)) ℚ.-
      (ℚ.- seq x (2 ℕ.* n) ℚ.- seq y (2 ℕ.* n)) ∣   ≈⟨ ℚP.∣-∣-cong (solve 2 (λ x y ->
                                                       (⊝ (x ⊕ y) ⊖ (⊝ x ⊖ y)) ⊜ Κ ((+ 0 / 1))) ℚP.≃-refl
                                                       (seq x (2 ℕ.* n)) (seq y (2 ℕ.* n))) ⟩
  (+ 0 / 1)                                               ≤⟨ ℚP.nonNegative⁻¹ _ ⟩
  + 2 / n                                            ∎})
  where
    open ℚP.≤-Reasoning
    open ℚ-Solver

-- Properties of _⊔_

@0 ⊔-cong : Congruent₂ _≃_ _⊔_
⊔-cong {x} {z} {y} {w} (*≃* x≃z) (*≃* y≃w) = *≃* partA
  where
    partA : ∀ (n : ℕ) -> {n≢0 : n ≢0} -> ℚ.∣ seq (x ⊔ y) n ℚ.- seq (z ⊔ w) n ∣ ℚ.≤ (+ 2 / n) {n≢0}
    partA (suc k₁) = [ left , right ]′ (ℚP.≤-total (seq x n ℚ.⊔ seq y n) (seq z n ℚ.⊔ seq w n))
      where
        open ℚP.≤-Reasoning
        open ℚ-Solver
        n = suc k₁

        partB : ∀ a b c d -> a ℚ.≤ b -> ℚ.∣ b ℚ.- d ∣ ℚ.≤ + 2 / n ->
              (a ℚ.⊔ b) ℚ.- (c ℚ.⊔ d) ℚ.≤ + 2 / n
        partB a b c d a≤b hyp = begin
          (a ℚ.⊔ b) ℚ.- (c ℚ.⊔ d) ≤⟨ ℚP.+-mono-≤ (ℚP.≤-reflexive (ℚP.p≤q⇒p⊔q≃q a≤b)) (ℚP.neg-mono-≤ (ℚP.p≤q⊔p c d)) ⟩
          b ℚ.- d                 ≤⟨ p≤∣p∣ (b ℚ.- d) ⟩
          ℚ.∣ b ℚ.- d ∣           ≤⟨ hyp ⟩
          + 2 / n                  ∎

        left : seq x n ℚ.⊔ seq y n ℚ.≤ seq z n ℚ.⊔ seq w n -> ℚ.∣ seq x n ℚ.⊔ seq y n ℚ.- (seq z n ℚ.⊔ seq w n) ∣ ℚ.≤ + 2 / n
        left hyp1 = [ zn≤wn , wn≤zn ]′ (ℚP.≤-total (seq z n) (seq w n))
          where
            first : ℚ.∣ (seq x n ℚ.⊔ seq y n) ℚ.- (seq z n ℚ.⊔ seq w n) ∣ ℚ.≃ (seq z n ℚ.⊔ seq w n) ℚ.- (seq x n ℚ.⊔ seq y n)
            first = begin-equality
              ℚ.∣ (seq x n ℚ.⊔ seq y n) ℚ.- (seq z n ℚ.⊔ seq w n) ∣ ≈⟨ ℚP.≃-trans (ℚP.≃-sym (ℚP.∣-p∣≃∣p∣ ((seq x n ℚ.⊔ seq y n) ℚ.- (seq z n ℚ.⊔ seq w n))))
                                                                                            (ℚP.∣-∣-cong (solve 2 (λ a b -> (⊝ (a ⊖ b)) ⊜ (b ⊖ a))
                                                                                            ℚP.≃-refl (seq x n ℚ.⊔ seq y n) (seq z n ℚ.⊔ seq w n))) ⟩
              ℚ.∣ (seq z n ℚ.⊔ seq w n) ℚ.- (seq x n ℚ.⊔ seq y n) ∣ ≈⟨ ℚP.0≤p⇒∣p∣≃p (ℚP.p≤q⇒0≤q-p hyp1) ⟩
              (seq z n ℚ.⊔ seq w n) ℚ.- (seq x n ℚ.⊔ seq y n)        ∎

            zn≤wn : seq z n ℚ.≤ seq w n -> ℚ.∣ (seq x n ℚ.⊔ seq y n) ℚ.- (seq z n ℚ.⊔ seq w n) ∣ ℚ.≤ + 2 / n
            zn≤wn hyp2 = begin
              ℚ.∣ (seq x n ℚ.⊔ seq y n) ℚ.- (seq z n ℚ.⊔ seq w n) ∣ ≈⟨ first ⟩
              (seq z n ℚ.⊔ seq w n) ℚ.- (seq x n ℚ.⊔ seq y n)       ≤⟨ partB (seq z n) (seq w n) (seq x n) (seq y n) hyp2
                                                                       (ℚP.≤-respˡ-≃ (∣p-q∣≃∣q-p∣ (seq y n) (seq w n)) (y≃w n)) ⟩
              + 2 / n                                            ∎

            wn≤zn : seq w n ℚ.≤ seq z n -> ℚ.∣ (seq x n ℚ.⊔ seq y n) ℚ.- (seq z n ℚ.⊔ seq w n) ∣ ℚ.≤ + 2 / n
            wn≤zn hyp2 = begin
              ℚ.∣ (seq x n ℚ.⊔ seq y n) ℚ.- (seq z n ℚ.⊔ seq w n) ∣ ≈⟨ first ⟩
              (seq z n ℚ.⊔ seq w n) ℚ.- (seq x n ℚ.⊔ seq y n)       ≈⟨ ℚP.+-cong (ℚP.⊔-comm (seq z n) (seq w n)) (ℚP.-‿cong (ℚP.⊔-comm (seq x n) (seq y n))) ⟩
              (seq w n ℚ.⊔ seq z n) ℚ.- (seq y n ℚ.⊔ seq x n)       ≤⟨ partB (seq w n) (seq z n) (seq y n) (seq x n) hyp2
                                                                       (ℚP.≤-respˡ-≃ (∣p-q∣≃∣q-p∣ (seq x n) (seq z n)) (x≃z n)) ⟩
              + 2 / n                                                ∎

        right : seq z n ℚ.⊔ seq w n ℚ.≤ seq x n ℚ.⊔ seq y n -> ℚ.∣ seq x n ℚ.⊔ seq y n ℚ.- (seq z n ℚ.⊔ seq w n) ∣ ℚ.≤ + 2 / n
        right hyp1 = [ xn≤yn , yn≤xn ]′ (ℚP.≤-total (seq x n) (seq y n))
          where
            xn≤yn : seq x n ℚ.≤ seq y n -> ℚ.∣ seq x n ℚ.⊔ seq y n ℚ.- (seq z n ℚ.⊔ seq w n) ∣ ℚ.≤ + 2 / n
            xn≤yn hyp2 = begin
              ℚ.∣ seq x n ℚ.⊔ seq y n ℚ.- (seq z n ℚ.⊔ seq w n) ∣ ≈⟨ ℚP.0≤p⇒∣p∣≃p (ℚP.p≤q⇒0≤q-p hyp1) ⟩
              seq x n ℚ.⊔ seq y n ℚ.- (seq z n ℚ.⊔ seq w n)       ≤⟨ partB (seq x n) (seq y n) (seq z n) (seq w n) hyp2 (y≃w n) ⟩
              + 2 / n                                              ∎

            yn≤xn : seq y n ℚ.≤ seq x n -> ℚ.∣ seq x n ℚ.⊔ seq y n ℚ.- (seq z n ℚ.⊔ seq w n) ∣ ℚ.≤ + 2 / n
            yn≤xn hyp2 = begin
              ℚ.∣ seq x n ℚ.⊔ seq y n ℚ.- (seq z n ℚ.⊔ seq w n) ∣ ≈⟨ ℚP.0≤p⇒∣p∣≃p (ℚP.p≤q⇒0≤q-p hyp1) ⟩
              seq x n ℚ.⊔ seq y n ℚ.- (seq z n ℚ.⊔ seq w n)       ≈⟨ ℚP.+-cong (ℚP.⊔-comm (seq x n) (seq y n)) (ℚP.-‿cong (ℚP.⊔-comm (seq z n) (seq w n))) ⟩
              seq y n ℚ.⊔ seq x n ℚ.- (seq w n ℚ.⊔ seq z n)       ≤⟨ partB (seq y n) (seq x n) (seq w n) (seq z n) hyp2 (x≃z n) ⟩
              + 2 / n                                              ∎

@0 ⊔-congˡ : LeftCongruent _≃_ _⊔_
⊔-congˡ y≃z = ⊔-cong ≃-refl y≃z

@0 ⊔-congʳ : RightCongruent _≃_ _⊔_
⊔-congʳ y≃z = ⊔-cong y≃z ≃-refl

@0 ⊔-comm : Commutative _≃_ _⊔_
⊔-comm x y = *≃* (λ { (suc k₁) -> let n = suc k₁ in begin
  ℚ.∣ seq x n ℚ.⊔ seq y n ℚ.- (seq y n ℚ.⊔ seq x n) ∣ ≈⟨ ℚP.∣-∣-cong (ℚP.+-congʳ (seq x n ℚ.⊔ seq y n) (ℚP.-‿cong (ℚP.⊔-comm (seq y n) (seq x n)))) ⟩
  ℚ.∣ seq x n ℚ.⊔ seq y n ℚ.- (seq x n ℚ.⊔ seq y n) ∣ ≈⟨ ℚP.∣-∣-cong (ℚP.+-inverseʳ (seq x n ℚ.⊔ seq y n)) ⟩
  (+ 0 / 1)                                                ≤⟨ ℚP.nonNegative⁻¹ _ ⟩
  + 2 / n                                              ∎})
  where open ℚP.≤-Reasoning

@0 ⊔-assoc : Associative _≃_ _⊔_
⊔-assoc x y z = *≃* (λ { (suc k₁) -> let n = suc k₁ in begin
  ℚ.∣ seq x n ℚ.⊔ seq y n ℚ.⊔ seq z n ℚ.- (seq x n ℚ.⊔ (seq y n ℚ.⊔ seq z n)) ∣ ≈⟨ ℚP.∣-∣-cong (ℚP.+-congʳ (seq x n ℚ.⊔ seq y n ℚ.⊔ seq z n)
                                                                                              (ℚP.-‿cong (ℚP.≃-sym (ℚP.⊔-assoc (seq x n) (seq y n) (seq z n))))) ⟩
  ℚ.∣ seq x n ℚ.⊔ seq y n ℚ.⊔ seq z n ℚ.- (seq x n ℚ.⊔ seq y n ℚ.⊔ seq z n) ∣   ≈⟨ ℚP.∣-∣-cong (ℚP.+-inverseʳ (seq x n ℚ.⊔ seq y n ℚ.⊔ seq z n)) ⟩
  (+ 0 / 1)                                                                          ≤⟨ ℚP.nonNegative⁻¹ _ ⟩
  + 2 / n                                                                       ∎})
  where open ℚP.≤-Reasoning

-- Properties of _⊓_

@0 x⊓y≃x⊓₂y : ∀ x y -> x ⊓ y ≃ x ⊓₂ y
x⊓y≃x⊓₂y x y = *≃* (λ { (suc k₁) -> let n = suc k₁; xₙ = seq x n; yₙ = seq y n in begin
  ℚ.∣ xₙ ℚ.⊓ yₙ ℚ.- ℚ.- ((ℚ.- xₙ) ℚ.⊔ (ℚ.- yₙ)) ∣     ≈⟨ ℚP.∣-∣-cong (ℚP.+-congʳ (xₙ ℚ.⊓ yₙ)
                                                         (ℚP.-‿cong (ℚP.≃-trans (ℚP.neg-distrib-⊔-⊓ (ℚ.- xₙ) (ℚ.- yₙ))
                                                         (ℚP.⊓-cong (ℚP.neg-involutive xₙ) (ℚP.neg-involutive yₙ))))) ⟩
  ℚ.∣ xₙ ℚ.⊓ yₙ ℚ.- xₙ ℚ.⊓ yₙ ∣                       ≈⟨ ℚP.∣-∣-cong (ℚP.+-inverseʳ (xₙ ℚ.⊓ yₙ)) ⟩
  (+ 0 / 1)                                                ≤⟨ ℚP.nonNegative⁻¹ _ ⟩
  + 2 / n                                             ∎})
  where open ℚP.≤-Reasoning

@0 ⊓₂-cong : Congruent₂ _≃_ _⊓₂_
⊓₂-cong x≃y u≃v = -‿cong (⊔-cong (-‿cong x≃y) (-‿cong u≃v))

@0 ⊓₂-congˡ : LeftCongruent _≃_ _⊓₂_
⊓₂-congˡ y≃z = ⊓₂-cong ≃-refl y≃z

@0 ⊓₂-congʳ : RightCongruent _≃_ _⊓₂_
⊓₂-congʳ y≃z = ⊓₂-cong y≃z ≃-refl

@0 ⊓₂-comm : Commutative _≃_ _⊓₂_
⊓₂-comm x y = -‿cong (⊔-comm (- x) (- y))

@0 ⊓₂-assoc : Associative _≃_ _⊓₂_
⊓₂-assoc x y z = -‿cong (begin
  (- (- (- x ⊔ - y))) ⊔ (- z) ≈⟨ ⊔-congʳ (neg-involutive (- x ⊔ - y)) ⟩
  (- x ⊔ - y) ⊔ (- z)         ≈⟨ ⊔-assoc (- x) (- y) (- z) ⟩
  (- x) ⊔ (- y ⊔ - z)         ≈⟨ ⊔-congˡ (≃-sym (neg-involutive (- y ⊔ - z))) ⟩
  (- x) ⊔ (- (- (- y ⊔ - z)))                            ∎)
  where open ≃-Reasoning

@0 ⊓-cong : Congruent₂ _≃_ _⊓_
⊓-cong {x} {u} {y} {v} x≃u y≃v = begin
  x ⊓ y  ≈⟨ x⊓y≃x⊓₂y x y ⟩
  x ⊓₂ y ≈⟨ ⊓₂-cong x≃u y≃v ⟩
  u ⊓₂ v ≈⟨ ≃-sym (x⊓y≃x⊓₂y u v) ⟩
  u ⊓ v   ∎
  where open ≃-Reasoning

@0 ⊓-congˡ : LeftCongruent _≃_ _⊓_
⊓-congˡ y≃z = ⊓-cong ≃-refl y≃z

@0 ⊓-congʳ : RightCongruent _≃_ _⊓_
⊓-congʳ y≃z = ⊓-cong y≃z ≃-refl

@0 ⊓-comm : Commutative _≃_ _⊓_
⊓-comm x y = begin
  x ⊓ y  ≈⟨ x⊓y≃x⊓₂y x y ⟩
  x ⊓₂ y ≈⟨ ⊓₂-comm x y ⟩
  y ⊓₂ x ≈⟨ ≃-sym (x⊓y≃x⊓₂y y x) ⟩
  y ⊓ x   ∎
  where open ≃-Reasoning

@0 ⊓-assoc : Associative _≃_ _⊓_
⊓-assoc x y z = begin
  x ⊓ y ⊓ z     ≈⟨ ≃-trans (⊓-congʳ (x⊓y≃x⊓₂y x y)) (x⊓y≃x⊓₂y (x ⊓₂ y) z) ⟩
  x ⊓₂ y ⊓₂ z   ≈⟨ ⊓₂-assoc x y z ⟩
  x ⊓₂ (y ⊓₂ z) ≈⟨ ≃-trans (⊓₂-congˡ (≃-sym (x⊓y≃x⊓₂y y z))) (≃-sym (x⊓y≃x⊓₂y x (y ⊓ z))) ⟩
  x ⊓ (y ⊓ z)    ∎
  where open ≃-Reasoning

-- Properties of ∣_∣

@0 ∣-∣-cong : Congruent₁ _≃_ ∣_∣
∣-∣-cong {x} {y} (*≃* x≃y) = *≃* lem
  where
    open ℚP.≤-Reasoning
    lem : (n : ℕ) {n≢0 : n ≢0} → ℚ.∣ seq ((∣_∣ Function.Base.-⟨ Function.Base.const ∣) x y) n ℚ.- seq ((Function.Base.∣ Function.Base.constᵣ ⟩- ∣_∣) x y) n ∣
      ℚ.≤ + 2 / n
    lem (suc k₁) = let n = suc k₁ in begin
           ℚ.∣ ℚ.∣ seq x n ∣ ℚ.- ℚ.∣ seq y n ∣ ∣ ≤⟨ ∣∣p∣-∣q∣∣≤∣p-q∣ (seq x n) (seq y n) ⟩
           ℚ.∣ seq x n ℚ.- seq y n ∣            ≤⟨ x≃y n ⟩
           + 2 / n                               ∎

@0 ∣x*y∣≃∣x∣*∣y∣ : ∀ x y -> ∣ x * y ∣ ≃ ∣ x ∣ * ∣ y ∣
∣x*y∣≃∣x∣*∣y∣ x y = *≃* (λ @0 { (suc k₁) -> let n = suc k₁; r = fK x ℕ.⊔ fK y in begin
  ℚ.∣ ℚ.∣ seq (x * y) n ∣ ℚ.- seq (∣ x ∣ * ∣ y ∣) n ∣ ≈⟨ ℚP.∣-∣-cong (ℚP.+-congʳ ℚ.∣ seq (x * y) n ∣
                                                        (ℚP.-‿cong (ℚP.≃-sym (ℚP.∣p*q∣≃∣p∣*∣q∣ (seq x (2 ℕ.* r ℕ.* n)) (seq y (2 ℕ.* r ℕ.* n)))))) ⟩
  ℚ.∣ ℚ.∣ seq (x * y) n ∣ ℚ.- ℚ.∣ seq (x * y) n ∣ ∣   ≈⟨ ℚP.∣-∣-cong (ℚP.+-inverseʳ ℚ.∣ seq (x * y) n ∣) ⟩
  (+ 0 / 1)                                                ≤⟨ ℚP.nonNegative⁻¹ _ ⟩
  + 2 / n ∎})
  where open ℚP.≤-Reasoning

-- Algebraic structures
@0 +-rawMagma : RawMagma 0ℓ 0ℓ
+-rawMagma = record
  { _≈_ = _≃_
  ; _∙_ = _+_
  }

@0 +-rawMonoid : RawMonoid 0ℓ 0ℓ
+-rawMonoid = record
  { _≈_ = _≃_
  ; _∙_ = _+_
  ; ε   = zeroℝ
  }

@0 +-0-rawGroup : RawGroup 0ℓ 0ℓ
+-0-rawGroup = record
  { Carrier = ℝ
  ; _≈_ = _≃_
  ; _∙_ = _+_
  ; ε = zeroℝ
  ; _⁻¹ = -_
  }

@0 +-*-rawSemiring : RawSemiring 0ℓ 0ℓ
+-*-rawSemiring = record
  { Carrier = ℝ
  ; _≈_     = _≃_
  ; _+_     = _+_
  ; _*_     = _*_
  ; 0#      = zeroℝ
  ; 1#      = oneℝ
  }

@0 +-*-rawRing : RawRing 0ℓ 0ℓ
+-*-rawRing = record
  { Carrier = ℝ
  ; _≈_ = _≃_
  ; _+_ = _+_
  ; _*_ = _*_
  ; -_ = -_
  ; 0# = zeroℝ
  ; 1# = oneℝ
  }

abstract
  ≃-isEquivalence₂ : IsEquivalence _≃_
  ≃-isEquivalence₂ = ≃-isEquivalence
  
+-cong₂ : Congruent₂ _≃_ _+_
+-cong₂ = +-cong

-‿cong₂ : Congruent₁ _≃_ (-_)
-‿cong₂ = -‿cong

+-inverse₂ : Inverse _≃_ zeroℝ -_ _+_
+-inverse₂ = +-inverse

+-identity₂ : Identity _≃_ zeroℝ _+_
+-identity₂ = +-identity

+-assoc₂ : Associative _≃_ _+_
+-assoc₂ = +-assoc

+-comm₂ : Commutative _≃_ _+_
+-comm₂ = +-comm

+-isMagma : IsMagma _≃_ _+_
+-isMagma = record
  { isEquivalence = ≃-isEquivalence₂
  ; ∙-cong = +-cong₂
  }


+-isSemigroup : IsSemigroup _≃_ _+_
+-isSemigroup = record
  { isMagma = +-isMagma
  ; assoc = +-assoc₂
  }

+-0-isMonoid : IsMonoid _≃_ _+_ zeroℝ
+-0-isMonoid = record
  { isSemigroup = +-isSemigroup
  ; identity = +-identity₂
  }

@0 +-0-isCommutativeMonoid : IsCommutativeMonoid _≃_ _+_ zeroℝ
+-0-isCommutativeMonoid = record
  { isMonoid = +-0-isMonoid
  ; comm     = +-comm
  }

+-0-isGroup : IsGroup _≃_ _+_ zeroℝ (-_)
+-0-isGroup = record
  { isMonoid = +-0-isMonoid
  ; inverse = +-inverse₂
  ; ⁻¹-cong = -‿cong₂
  }


+-0-isAbelianGroup : IsAbelianGroup _≃_ _+_ zeroℝ (-_)
+-0-isAbelianGroup = record
  { isGroup = +-0-isGroup
  ; comm    = +-comm₂
  }

@0 +-magma : Magma 0ℓ 0ℓ
+-magma = record
  { isMagma = +-isMagma
  }

@0 +-semigroup : Semigroup 0ℓ 0ℓ
+-semigroup = record
  { isSemigroup = +-isSemigroup
  }

@0 +-0-monoid : Monoid 0ℓ 0ℓ
+-0-monoid = record
  { isMonoid = +-0-isMonoid
  }

@0 +-0-commutativeMonoid : CommutativeMonoid 0ℓ 0ℓ
+-0-commutativeMonoid = record
  { isCommutativeMonoid = +-0-isCommutativeMonoid
  }

@0 +-0-group : Group 0ℓ 0ℓ
+-0-group = record
  { isGroup = +-0-isGroup
  }

@0 +-0-abelianGroup : AbelianGroup 0ℓ 0ℓ
+-0-abelianGroup = record
  { isAbelianGroup = +-0-isAbelianGroup
  }

@0 *-rawMagma : RawMagma 0ℓ 0ℓ
*-rawMagma = record
  { _≈_ = _≃_
  ; _∙_ = _*_
  }

@0 *-rawMonoid : RawMonoid 0ℓ 0ℓ
*-rawMonoid = record
  { _≈_ = _≃_
  ; _∙_ = _*_
  ; ε   = oneℝ
  }

abstract
  *-cong₂ : Congruent₂ _≃_ _*_
  *-cong₂ = *-cong

*-isMagma : IsMagma _≃_ _*_
*-isMagma = record
  { isEquivalence = ≃-isEquivalence₂
  ; ∙-cong = *-cong₂
  }

abstract
  *-assoc₂ : Associative _≃_ _*_
  *-assoc₂ = *-assoc

*-isSemigroup : IsSemigroup _≃_ _*_
*-isSemigroup = record
  { isMagma = *-isMagma
  ; assoc   = *-assoc₂
  }

abstract
  @0 *-identity₂ : Identity _≃_ oneℝ _*_
  *-identity₂ = *-identity

*-1-isMonoid : IsMonoid _≃_ _*_ oneℝ
*-1-isMonoid = record
  { isSemigroup = *-isSemigroup
  ; identity    = *-identity
  }

@0 *-1-isCommutativeMonoid : IsCommutativeMonoid _≃_ _*_ oneℝ
*-1-isCommutativeMonoid = record
  { isMonoid = *-1-isMonoid
  ; comm     = *-comm
  }


abstract
  *-distrib-+₂ : (_≃_ DistributesOver _*_) _+_
  *-distrib-+₂ = *-distrib-+

*-zero₂ : Zero _≃_ zeroℝ _*_
*-zero₂ = *-zero

*-comm₂ : Commutative _≃_ _*_
*-comm₂ = *-comm
  
+-*-isRing : IsRing _≃_ _+_ _*_ -_ zeroℝ oneℝ
+-*-isRing = record
  { +-isAbelianGroup = +-0-isAbelianGroup
  ; *-isMonoid       = *-1-isMonoid
  ; distrib          = *-distrib-+₂
  ; zero             = *-zero₂
  }

+-*-isCommutativeRing : IsCommutativeRing _≃_ _+_ _*_ -_ zeroℝ oneℝ
+-*-isCommutativeRing = record
  { isRing = +-*-isRing
  ; *-comm = *-comm₂
  }

@0 +-*-isSemiringWithoutAnnihilatingZero : IsSemiringWithoutAnnihilatingZero _≃_ _+_ _*_ zeroℝ oneℝ
+-*-isSemiringWithoutAnnihilatingZero = record
  { +-isCommutativeMonoid = +-0-isCommutativeMonoid
  ; *-isMonoid            = *-1-isMonoid
  ; distrib               = *-distrib-+
  }

@0 +-*-isSemiring : IsSemiring _≃_ _+_ _*_ zeroℝ oneℝ
+-*-isSemiring = record
  { isSemiringWithoutAnnihilatingZero = +-*-isSemiringWithoutAnnihilatingZero
  ; zero                              = *-zero
  }

@0 +-*-isCommutativeSemiring : IsCommutativeSemiring _≃_ _+_ _*_ zeroℝ oneℝ
+-*-isCommutativeSemiring = record
  { isSemiring = +-*-isSemiring
  ; *-comm     = *-comm
  }

@0 *-magma : Magma 0ℓ 0ℓ
*-magma = record
  { isMagma = *-isMagma
  }

@0 *-semigroup : Semigroup 0ℓ 0ℓ
*-semigroup = record
  { isSemigroup = *-isSemigroup
  }

@0 *-1-monoid : Monoid 0ℓ 0ℓ
*-1-monoid = record
  { isMonoid = *-1-isMonoid
  }

@0 *-1-commutativeMonoid : CommutativeMonoid 0ℓ 0ℓ
*-1-commutativeMonoid = record
  { isCommutativeMonoid = *-1-isCommutativeMonoid
  }

@0 +-*-semiring : Semiring 0ℓ 0ℓ
+-*-semiring = record
  { isSemiring = +-*-isSemiring
  }

@0 +-*-commutativeSemiring : CommutativeSemiring 0ℓ 0ℓ
+-*-commutativeSemiring = record
  { isCommutativeSemiring = +-*-isCommutativeSemiring
  }

@0 +-*-ring : Ring 0ℓ 0ℓ
+-*-ring = record
  { isRing = +-*-isRing
  }

+-*-commutativeRing : CommutativeRing 0ℓ 0ℓ
+-*-commutativeRing = record
  { isCommutativeRing = +-*-isCommutativeRing
  }

-- Properties of sign predicates
-- x has to be explicit (`implicit type argument not supported`)
lemma281If : ∀ (x : ℝ) -> Positive x -> Σ0 ℕ (λ (N-1 : ℕ) -> ∀ (m : ℕ) -> m ℕ.≥ suc N-1 -> seq x m ℚ.≥ + 1 / (suc N-1))
lemma281If x (MkPos (nm1 :&: posx)) = ℕ.pred l :&: lem
  where
    open ℚP.≤-Reasoning
    open ℚ-Solver
    open ℤ-Solver using ()
      renaming
        ( solve to ℤsolve
        ; _⊕_   to _:+_
        ; _⊖_   to _:-_
        ; _⊗_   to _:*_
        ; _⊜_   to _:=_
        ; Κ     to κ
        )
    n : ℕ
    n = suc nm1
    arch : Σ0 ℕ λ (N-1 : ℕ) -> (+ 2) / (suc N-1) ℚ.< (seq x n ℚ.- + 1 / n)
    arch = fastArchimedeanℚ₂ (seq x n ℚ.- + 1 / n) (+ 2) (ℚ.positive (p<q⇒0<q-p (+ 1 / n) (seq x n) posx))
    l : ℕ
    l = suc (proj₁ arch)

    @0 lem : (m : ℕ) → m ℕ.≥ suc (ℕ.pred l) → seq x m ℚ.≥ + 1 / suc (ℕ.pred l)
    lem (suc k₁) m≥l = let m = suc k₁ in begin
           + 1 / l                               ≈⟨ ℚ.*≡* (ℤsolve 1 (λ N ->
                                                    κ (+ 1) :* (N :* N) := ((κ (+ 2) :* N :- κ (+ 1) :* N) :* N))
                                                    refl (+ l)) ⟩
           + 2 / l ℚ.- + 1 / l                   ≤⟨ ℚP.+-mono-≤ (ℚP.<⇒≤ (proj₂ arch)) (ℚP.neg-mono-≤ (q≤r⇒+p/r≤+p/q 1 l m m≥l)) ⟩
           seq x n ℚ.- + 1 / n ℚ.- + 1 / m       ≈⟨ solve 3 (λ xₙ n⁻¹ m⁻¹ -> (xₙ ⊖ n⁻¹ ⊖ m⁻¹) ⊜ (xₙ ⊖ (n⁻¹ ⊕ m⁻¹))) ℚP.≃-refl (seq x n) (+ 1 / n) (+ 1 / m) ⟩
           seq x n ℚ.- (+ 1 / n ℚ.+ + 1 / m)     ≤⟨ ℚP.+-monoʳ-≤ (seq x n) (ℚP.neg-mono-≤ (reg x n m)) ⟩
           seq x n ℚ.- ℚ.∣ seq x n ℚ.- seq x m ∣ ≤⟨ ℚP.+-monoʳ-≤ (seq x n) (ℚP.neg-mono-≤ (p≤∣p∣ (seq x n ℚ.- seq x m))) ⟩
           seq x n ℚ.- (seq x n ℚ.- seq x m)     ≈⟨ solve 2 (λ xₙ xₘ -> (xₙ ⊖ (xₙ ⊖ xₘ)) ⊜ xₘ) ℚP.≃-refl (seq x n) (seq x m) ⟩
           seq x m  ∎
{-# COMPILE AGDA2HS lemma281If #-}

abstract
  fastLemma281If : ∀ (x : ℝ) -> Positive x -> Σ0 ℕ λ (N-1 : ℕ) -> ∀ (m : ℕ) -> m ℕ.≥ suc N-1 -> seq x m ℚ.≥ + 1 / (suc N-1)
  fastLemma281If = lemma281If
  {-# COMPILE AGDA2HS fastLemma281If #-}

lemma281OnlyIf : ∀ (x : ℝ) -> (Σ0 ℕ λ (k-1 : ℕ) -> ∀ (m : ℕ) -> m ℕ.≥ suc k-1 -> seq x m ℚ.≥ + 1 / (suc k-1)) -> Positive x
lemma281OnlyIf x (km1 :&: proof) = MkPos (k :&: (begin-strict
  + 1 / (suc k) <⟨ ℚ.*<* (ℤP.*-monoˡ-<-pos 0 (ℤ.+<+ (ℕP.n<1+n k))) ⟩
  + 1 / k       ≤⟨ proof (suc k) (ℕP.n≤1+n k) ⟩
  seq x (suc k)  ∎))
  where
    open ℚP.≤-Reasoning
    k : ℕ
    k = suc km1
{-# COMPILE AGDA2HS lemma281OnlyIf #-}

--to extract the erased proof from an erased NonNegative argument
@0 nonNeg-unpack : {x : ℝ} → NonNegative x → (∀ (n : ℕ) -> {@0 n≢0 : n ≢0} -> seq x n ℚ.≥ ℚ.- ((+ 1 / n) {n≢0}))
nonNeg-unpack (nonNeg* nonx) = nonx

lemma282If : ∀ {@0 x : ℝ} -> @0 NonNegative x -> ∀ (n : ℕ) -> {@0 n≢0 : n ≢0} ->
                 Σ0 ℕ λ (Nₙ : ℕ) -> Nₙ ≢0 × (∀ (m : ℕ) -> m ℕ.≥ Nₙ -> seq x m ℚ.≥ ℚ.- (+ 1 / n) {n≢0})
lemma282If {x} nonNegx (suc k₁) = n :&: (_ , lem)
  where
    open ℚP.≤-Reasoning
    n : ℕ
    n = suc k₁

    @0 lem : (m : ℕ) → m ℕ.≥ suc k₁ → seq x m ℚ.≥ ℚ.- (+ 1 / suc k₁)
    lem (suc k₂) m≥n = let m = suc k₂ in begin
                    ℚ.- (+ 1 / n) ≤⟨ ℚP.neg-mono-≤ (q≤r⇒+p/r≤+p/q 1 n m m≥n) ⟩
                    ℚ.- (+ 1 / m) ≤⟨ (nonNeg-unpack nonNegx) m ⟩
                    seq x m        ∎

lemma282If' : ∀ (@0 x : ℝ) -> @0 NonNegative x -> ∀ (n : ℕ) -> {@0 n≢0 : n ≢0} ->
                 Σ0 ℕ (λ _ → ⊤)
lemma282If' x _ n = n :&: tt
{-# COMPILE AGDA2HS lemma282If' #-}

proj₁lemma282If≡proj₁lemma282If' : ∀ (@0 x : ℝ) -> (@0 nonNegx : NonNegative x) -> ∀ (n : ℕ) -> {@0 n≢0 : n ≢0} ->
                                        proj₁ (lemma282If {x} nonNegx n {n≢0}) ≡ proj₁ (lemma282If' x nonNegx n {n≢0})
proj₁lemma282If≡proj₁lemma282If' x nonNegx (suc k₁) = refl

abstract
  fastLemma282If : ∀ {@0 x : ℝ} -> @0 NonNegative x -> ∀ (n : ℕ) -> {@0 n≢0 : n ≢0} ->
                        Σ0 ℕ (λ (Nₙ : ℕ) -> Nₙ ≢0 × (∀ (m : ℕ) -> m ℕ.≥ Nₙ -> seq x m ℚ.≥ ℚ.- (+ 1 / n) {n≢0}))
  fastLemma282If = lemma282If

  proj₁fastLemma282If≡proj₁lemma282If' : ∀ (x : ℝ) -> (@0 nonNegx : NonNegative x) -> ∀ (n : ℕ) -> {@0 n≢0 : n ≢0} ->
                                          proj₁ (fastLemma282If {x} nonNegx n {n≢0}) ≡ proj₁ (lemma282If' x nonNegx n {n≢0})
  proj₁fastLemma282If≡proj₁lemma282If' x nonNegx (suc k₁) = refl

lemma-2-8-2-onlyif : ∀ {x : ℝ} -> @0 (∀ (n : ℕ) -> {@0 n≢0 : n ≢0} -> ∃0 λ (Nₙ : ℕ) -> Nₙ ≢0 ×
                     (∀ (m : ℕ) -> m ℕ.≥ Nₙ -> seq x m ℚ.≥ ℚ.- (+ 1 / n) {n≢0})) -> NonNegative x
lemma-2-8-2-onlyif {x} hyp = nonNeg* lem
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
    
    @0 lem : (n : ℕ) {@0 n≢0 : n ≢0} → seq x n ℚ.≥ ℚ.- (+ 1 / n)
    lem (suc k₁) = p-j⁻¹≤q⇒p≤q lem₂
      where
      n : ℕ
      n = suc k₁
      @0 lem₂ : (j : ℕ) {@0 j≢0 : j ≢0} → mkℚᵘ -[1+ 0 ] k₁ ℚ.- + 1 / j ℚ.≤ seq x (suc k₁)
      lem₂ (suc k₂) = let j = suc k₂; N₂ⱼ = suc (proj₁ (hyp (2 ℕ.* j))); m = N₂ⱼ ℕ.⊔ (2 ℕ.* j) in begin
                     ℚ.- (+ 1 / n) ℚ.- (+ 1 / j)                             ≈⟨ ℚP.+-congʳ (ℚ.- (+ 1 / n)) {ℚ.- (+ 1 / j)} {ℚ.- (+ 1 / (2 ℕ.* j) ℚ.+ + 1 / (2 ℕ.* j))}
                                                                                (ℚP.-‿cong (ℚ.*≡* (ℤsolve 1 (λ j ->
                                                                                κ (+ 1) :* (κ (+ 2) :* j :* (κ (+ 2) :* j)) :=
                                                                                (((κ (+ 1) :* (κ (+ 2) :* j) :+ κ (+ 1) :* (κ (+ 2) :* j)) :* j)))
                                                                                refl (+ j)))) ⟩
                     ℚ.- (+ 1 / n) ℚ.- (+ 1 / (2 ℕ.* j) ℚ.+ + 1 / (2 ℕ.* j)) ≤⟨ ℚP.+-monoʳ-≤ (ℚ.- (+ 1 / n))
                                                                                (ℚP.neg-mono-≤ (ℚP.+-monoˡ-≤ (+ 1 / (2 ℕ.* j))
                                                                                (q≤r⇒+p/r≤+p/q 1 (2 ℕ.* j) m (ℕP.m≤n⊔m N₂ⱼ (2 ℕ.* j))))) ⟩
                     ℚ.- (+ 1 / n) ℚ.- (+ 1 / m ℚ.+ + 1 / (2 ℕ.* j))         ≈⟨ solve 3 (λ n⁻¹ m⁻¹ k⁻¹ ->
                                                                                (⊝ n⁻¹ ⊖ (m⁻¹ ⊕ k⁻¹)) ⊜ (⊝ k⁻¹ ⊖ (m⁻¹ ⊕ n⁻¹)))
                                                                                ℚP.≃-refl (+ 1 / n) (+ 1 / m) (+ 1 / (2 ℕ.* j)) ⟩
                     ℚ.- (+ 1 / (2 ℕ.* j)) ℚ.- (+ 1 / m ℚ.+ + 1 / n)         ≤⟨ ℚP.+-mono-≤
                                                                                (proj₂ (proj₂ (hyp (2 ℕ.* j))) m (ℕP.≤-trans (ℕP.n≤1+n (ℕ.pred N₂ⱼ)) (ℕP.m≤m⊔n N₂ⱼ (2 ℕ.* j))))
                                                                                (ℚP.neg-mono-≤ (reg x m n)) ⟩
                     seq x m ℚ.- ℚ.∣ seq x m ℚ.- seq x n ∣                   ≤⟨ ℚP.+-monoʳ-≤ (seq x m) (ℚP.neg-mono-≤ (p≤∣p∣ (seq x m ℚ.- seq x n))) ⟩
                     seq x m ℚ.- (seq x m ℚ.- seq x n)                       ≈⟨ solve 2 (λ xₘ xₙ -> (xₘ ⊖ (xₘ ⊖ xₙ)) ⊜ xₙ) ℚP.≃-refl (seq x m) (seq x n) ⟩
                     seq x n                                                  ∎

posCong : ∀ (x y : ℝ) -> @0 (x ≃ y) -> Positive x -> Positive y
posCong x y x≃y posx = lemma281OnlyIf y (ℕ.pred (2 ℕ.* l) :&: lem)
  where
    open ℚP.≤-Reasoning
    open ℚ-Solver
    open ℤ-Solver using ()
      renaming
        ( solve to ℤsolve
        ; _⊕_   to _:+_
        ; _⊗_   to _:*_
        ; ⊝_    to :-_
        ; _⊜_   to _:=_
        ; Κ     to κ
        )
    fromPosx : Σ0 ℕ λ (l₁-1 : ℕ) -> ∀ (m : ℕ) -> m ℕ.≥ suc l₁-1 -> seq x m ℚ.≥ + 1 / (suc l₁-1)
    fromPosx = fastLemma281If x posx
    l₁ : ℕ
    l₁ = suc (proj₁ fromPosx)
    fromxeqy : Σ0 ℕ λ (l : ℕ) -> ∀ (n : ℕ) -> n ℕ.≥ l ->
                         ℚ.∣ seq x n ℚ.- seq y n ∣ ℚ.≤ (+ 1 / (2 ℕ.* l₁))
    fromxeqy = fastEqualityLemmaIf x y x≃y (2 ℕ.* l₁)
    l₂ l : ℕ
    l₂ = suc (proj₁ fromxeqy)
    l = l₁ ℕ.⊔ l₂

    @0 lem : (m : ℕ) → m ℕ.≥ suc (ℕ.pred (2 ℕ.* l)) → seq y m ℚ.≥ + 1 / suc (ℕ.pred (2 ℕ.* l))
    lem (suc k₁) m≥2l = let m = suc k₁ in begin
          + 1 / (2 ℕ.* l)                       ≤⟨ q≤r⇒+p/r≤+p/q 1 (2 ℕ.* l₁) (2 ℕ.* l) (ℕP.*-monoʳ-≤ 2 (ℕP.m≤m⊔n l₁ l₂)) ⟩
          + 1 / (2 ℕ.* l₁)                      ≈⟨ ℚ.*≡* (ℤsolve 1 (λ l₁ ->
                                                   κ (+ 1) :* (l₁ :* (κ (+ 2) :* l₁)) :=
                                                   (κ (+ 1) :* (κ (+ 2) :* l₁) :+ (:- κ (+ 1)) :* l₁) :* (κ (+ 2) :* l₁))
                                                   refl (+ l₁)) ⟩
          + 1 / l₁ ℚ.- + 1 / (2 ℕ.* l₁)         ≤⟨ ℚP.+-mono-≤
                                                   (proj₂ fromPosx m (ℕP.≤-trans (ℕP.m≤m⊔n l₁ l₂) (ℕP.≤-trans (ℕP.m≤n*m l {2} ℕP.0<1+n) m≥2l)))
                                                   (ℚP.neg-mono-≤ (proj₂ fromxeqy m
                                                   (ℕP.≤-trans (ℕP.n≤1+n (ℕ.pred l₂)) (ℕP.≤-trans (ℕP.m≤n⊔m l₁ l₂) (ℕP.≤-trans (ℕP.m≤n*m l {2} ℕP.0<1+n) m≥2l))))) ⟩
          seq x m ℚ.- ℚ.∣ seq x m ℚ.- seq y m ∣ ≤⟨ ℚP.+-monoʳ-≤ (seq x m) (ℚP.neg-mono-≤ (p≤∣p∣ (seq x m ℚ.- seq y m))) ⟩
          seq x m ℚ.- (seq x m ℚ.- seq y m)     ≈⟨ solve 2 (λ xₘ yₘ -> (xₘ ⊖ (xₘ ⊖ yₘ)) ⊜ yₘ) ℚP.≃-refl (seq x m) (seq y m) ⟩
          seq y m                                ∎
{-# COMPILE AGDA2HS posCong #-}

pos⇒nonNeg : ∀ {x} -> Positive x -> NonNegative x
pos⇒nonNeg {x} posx = lemma-2-8-2-onlyif (λ @0 { (suc k₁) -> let n = suc k₁ in N :&: _ , λ @0 { (suc k₂) m≥N -> let m = suc k₂ in
                      begin
  ℚ.- (+ 1 / n) <⟨ ℚP.negative⁻¹ _ ⟩
  (+ 0 / 1)           ≤⟨ ℚP.nonNegative⁻¹ _ ⟩
  + 1 / N       ≤⟨ proj₂ fromPosx m m≥N ⟩
  seq x m        ∎}})
  where
    open ℚP.≤-Reasoning
    @0 fromPosx : ∃0 λ (N-1 : ℕ) -> ∀ (m : ℕ) -> m ℕ.≥ suc N-1 -> seq x m ℚ.≥ + 1 / (suc N-1)
    fromPosx = fastLemma281If x posx
    @0 N : ℕ
    N = suc (proj₁ fromPosx)

@0 posx,y⇒posx+y : ∀ {x y} -> Positive x -> Positive y -> Positive (x + y)
posx,y⇒posx+y {x} {y} posx posy = let fromPosx = fastLemma281If x posx; fromPosy = fastLemma281If y posy
                                               ; N₁ = suc (proj₁ fromPosx); N₂ = suc (proj₁ fromPosy); N = N₁ ℕ.⊔ N₂ in
                                  lemma281OnlyIf (x + y) (ℕ.pred N :&: λ @0 { (suc k₁) m≥N -> let m = suc k₁ in begin
  + 1 / N                             ≤⟨ ℚP.p≤p+q {+ 1 / N} {+ 1 / N} _ ⟩
  + 1 / N ℚ.+ + 1 / N                 ≤⟨ ℚP.+-mono-≤
                                         (q≤r⇒+p/r≤+p/q 1 N₁ N (ℕP.m≤m⊔n N₁ N₂))
                                         (q≤r⇒+p/r≤+p/q 1 N₂ N (ℕP.m≤n⊔m N₁ N₂)) ⟩
  + 1 / N₁ ℚ.+ + 1 / N₂               ≤⟨ ℚP.+-mono-≤
                                         (proj₂ fromPosx (2 ℕ.* m) (ℕP.≤-trans (ℕP.≤-trans (ℕP.m≤m⊔n N₁ N₂) m≥N) (ℕP.m≤n*m m {2} ℕP.0<1+n)))
                                         (proj₂ fromPosy (2 ℕ.* m) (ℕP.≤-trans (ℕP.≤-trans (ℕP.m≤n⊔m N₁ N₂) m≥N) (ℕP.m≤n*m m {2} ℕP.0<1+n))) ⟩
  seq x (2 ℕ.* m) ℚ.+ seq y (2 ℕ.* m)  ∎})
  where open ℚP.≤-Reasoning

@0 nonNegx,y⇒nonNegx+y : ∀ {x y} -> NonNegative x -> NonNegative y -> NonNegative (x + y)
nonNegx,y⇒nonNegx+y {x} {y} nonx nony = lemma-2-8-2-onlyif (λ @0 { (suc k₁) ->
                                        let n = suc k₁; fromNonx = fastLemma282If nonx (2 ℕ.* n); fromNony = fastLemma282If nony (2 ℕ.* n)
                                              ; Nx = proj₁ fromNonx; Ny = proj₁ fromNony; N = suc (Nx ℕ.⊔ Ny)
                                              ; Nx≤N = ℕP.≤-trans (ℕP.m≤m⊔n Nx Ny) (ℕP.n≤1+n (ℕ.pred N))
                                              ; Ny≤N = ℕP.≤-trans (ℕP.m≤n⊔m Nx Ny) (ℕP.n≤1+n (ℕ.pred N)) in
                                        N :&: _ , λ @0 { (suc k₂) m≥N -> let m = suc k₂; m≤2m = ℕP.m≤n*m m {2} ℕP.0<1+n in begin
  ℚ.- (+ 1 / n)                               ≈⟨ ℚ.*≡* (solve 1 (λ n ->
                                                 (⊝ Κ (+ 1)) ⊗ (Κ (+ 2) ⊗ n ⊗ (Κ (+ 2) ⊗ n)) ⊜
                                                 (((⊝ Κ (+ 1)) ⊗ (Κ (+ 2) ⊗ n) ⊕ ((⊝ Κ (+ 1)) ⊗ (Κ (+ 2) ⊗ n))) ⊗ n))
                                                 refl (+ n)) ⟩
  ℚ.- (+ 1 / (2 ℕ.* n)) ℚ.- (+ 1 / (2 ℕ.* n)) ≤⟨ ℚP.+-mono-≤
                                                 (proj₂ (proj₂ fromNonx) (2 ℕ.* m) (ℕP.≤-trans (ℕP.≤-trans Nx≤N m≥N) m≤2m))
                                                 (proj₂ (proj₂ fromNony) (2 ℕ.* m) (ℕP.≤-trans (ℕP.≤-trans Ny≤N m≥N) m≤2m)) ⟩
  seq x (2 ℕ.* m) ℚ.+ seq y (2 ℕ.* m)          ∎}})
  where
    open ℚP.≤-Reasoning
    open ℤ-Solver

nonNeg-cong : ∀ {x y} -> @0 x ≃ y -> @0 NonNegative x -> NonNegative y
nonNeg-cong {x} {y} x≃y nonx = lemma-2-8-2-onlyif λ @0 { (suc k₁) ->
                               let n = suc k₁; fromNonx = fastLemma282If nonx (2 ℕ.* n); fromx≃y = fastEqualityLemmaIf x y x≃y (2 ℕ.* n)
                                      ; N₁ = proj₁ fromNonx; N₂ = proj₁ fromx≃y; N = suc (N₁ ℕ.⊔ N₂)
                                      ; N₁≤N = ℕP.≤-trans (ℕP.m≤m⊔n N₁ N₂) (ℕP.n≤1+n (ℕ.pred N))
                                       ; N₂≤N = ℕP.≤-trans (ℕP.m≤n⊔m N₁ N₂) (ℕP.n≤1+n (ℕ.pred N)) in
                               N :&: _ , λ @0 { (suc k₂) m≥N -> let m = suc k₂ in begin
  ℚ.- (+ 1 / n)                               ≈⟨ ℚ.*≡* (ℤsolve 1 (λ n ->
                                                 (:- κ (+ 1)) :* (κ (+ 2) :* n :* (κ (+ 2) :* n)) :=
                                                 (((:- κ (+ 1)) :* (κ (+ 2) :* n) :+ ((:- κ (+ 1)) :* (κ (+ 2) :* n))) :* n))
                                                 refl (+ n)) ⟩
  ℚ.- (+ 1 / (2 ℕ.* n)) ℚ.- (+ 1 / (2 ℕ.* n)) ≤⟨ ℚP.+-mono-≤
                                                 (proj₂ (proj₂ fromNonx) m (ℕP.≤-trans N₁≤N m≥N))
                                                 (ℚP.neg-mono-≤ (proj₂ fromx≃y m (ℕP.≤-trans N₂≤N m≥N))) ⟩
  seq x m ℚ.- ℚ.∣ seq x m ℚ.- seq y m ∣       ≤⟨ ℚP.+-monoʳ-≤ (seq x m) (ℚP.neg-mono-≤ (p≤∣p∣ (seq x m ℚ.- seq y m))) ⟩
  seq x m ℚ.- (seq x m ℚ.- seq y m)           ≈⟨ solve 2 (λ x y -> (x ⊖ (x ⊖ y)) ⊜ y) ℚP.≃-refl (seq x m) (seq y m) ⟩
  seq y m                                      ∎}}
  where
    open ℚP.≤-Reasoning
    open ℚ-Solver
    open ℤ-Solver using ()
      renaming
        ( solve to ℤsolve
        ; _⊕_   to _:+_
        ; _⊗_   to _:*_
        ; ⊝_    to :-_
        ; _⊜_   to _:=_
        ; Κ     to κ
        )

posxAndNonNegyThenPosxPlusy : ∀ (x y : ℝ) -> Positive x -> @0 NonNegative y -> Positive (x + y)
posxAndNonNegyThenPosxPlusy x y posx nony = let fromPosx = fastLemma281If x posx; N₁ = suc (proj₁ fromPosx)
                                                     ; fromNony = fastLemma282If nony (2 ℕ.* N₁)
                                                     ; N₂ = suc (proj₁ fromNony); N = 2 ℕ.* (N₁ ℕ.⊔ N₂)
                                                     ; N₁≤N = ℕP.≤-trans (ℕP.m≤m⊔n N₁ N₂) (ℕP.m≤n*m (N₁ ℕ.⊔ N₂) {2} ℕP.0<1+n)
                                                     ; N₂-1≤N = ℕP.≤-trans (ℕP.≤-trans (ℕP.n≤1+n (ℕ.pred N₂)) (ℕP.m≤n⊔m N₁ N₂))
                                                                (ℕP.m≤n*m (N₁ ℕ.⊔ N₂) {2} ℕP.0<1+n) in
                                                     
                                        lemma281OnlyIf (x + y) (ℕ.pred N :&: (λ @0 { (suc k₁) m≥N -> let m = suc k₁ in begin
  + 1 / N                             ≤⟨ q≤r⇒+p/r≤+p/q 1 (2 ℕ.* N₁) N (ℕP.*-monoʳ-≤ 2 (ℕP.m≤m⊔n N₁ N₂)) ⟩
  + 1 / (2 ℕ.* N₁)                    ≈⟨ ℚ.*≡* (solve 1 (λ N₁ ->
                                         Κ (+ 1) ⊗ (N₁ ⊗ (Κ (+ 2) ⊗ N₁)) ⊜
                                         (Κ (+ 1) ⊗ (Κ (+ 2) ⊗ N₁) ⊕ (⊝ Κ (+ 1)) ⊗ N₁) ⊗ (Κ (+ 2) ⊗ N₁))
                                         refl (+ N₁)) ⟩
  + 1 / N₁ ℚ.- + 1 / (2 ℕ.* N₁)       ≤⟨ ℚP.+-mono-≤
                                         (proj₂ fromPosx (2 ℕ.* m) (ℕP.≤-trans (ℕP.≤-trans N₁≤N m≥N) (ℕP.m≤n*m m {2} ℕP.0<1+n)))
                                         (proj₂ (proj₂ fromNony) (2 ℕ.* m) (ℕP.≤-trans (ℕP.≤-trans N₂-1≤N m≥N) (ℕP.m≤n*m m {2} ℕP.0<1+n))) ⟩
  seq x (2 ℕ.* m) ℚ.+ seq y (2 ℕ.* m)  ∎}))
  where
    open ℚP.≤-Reasoning
    open ℤ-Solver
{-# COMPILE AGDA2HS posxAndNonNegyThenPosxPlusy #-}

@0 nonNeg∣x∣ : ∀ x -> NonNegative ∣ x ∣
nonNeg∣x∣ x = nonNeg* (λ @0 { (suc k₁) -> let n = suc k₁ in ℚP.≤-trans (ℚP.nonPositive⁻¹ _) (ℚP.0≤∣p∣ (seq x n))})

@0 nonNegx⇒∣x∣≃x : ∀ {x} -> NonNegative x -> ∣ x ∣ ≃ x
nonNegx⇒∣x∣≃x {x} nonx = equality-lemma-onlyif ∣ x ∣ x partA
  where
    open ℚP.≤-Reasoning
    open ℤ-Solver
    partA : ∀ (j : ℕ) -> {j≢0 : j ≢0} -> ∃ λ (N : ℕ) -> ∀ (n : ℕ) -> n ℕ.≥ N ->
            ℚ.∣ ℚ.∣ seq x n ∣ ℚ.- seq x n ∣ ℚ.≤ (+ 1 / j) {j≢0}
    partA (suc k₁) = N , partB
      where
        j = suc k₁
        fromNonx = fastLemma282If nonx (2 ℕ.* j)
        N = suc (proj₁ fromNonx)

        partB : ∀ (n : ℕ) -> n ℕ.≥ N -> ℚ.∣ ℚ.∣ seq x n ∣ ℚ.- seq x n ∣ ℚ.≤ + 1 / j
        partB (suc k₂) n≥N = [ left , right ]′ (ℚP.≤-total (seq x n) (+ 0 / 1))
          where
            n = suc k₂

            -xₙ≤1/2j = begin
              ℚ.- seq x n                 ≤⟨ ℚP.neg-mono-≤ (proj₂ (proj₂ fromNonx) n (ℕP.≤-trans (ℕP.n≤1+n (ℕ.pred N)) n≥N)) ⟩
              ℚ.- (ℚ.- (+ 1 / (2 ℕ.* j))) ≈⟨ ℚP.neg-involutive (+ 1 / (2 ℕ.* j)) ⟩
              + 1 / (2 ℕ.* j)              ∎

            left : seq x n ℚ.≤ (+ 0 / 1) -> ℚ.∣ ℚ.∣ seq x n ∣ ℚ.- seq x n ∣ ℚ.≤ + 1 / j
            left hyp = begin
              ℚ.∣ ℚ.∣ seq x n ∣ ℚ.- seq x n ∣         ≈⟨ ℚP.0≤p⇒∣p∣≃p (ℚP.p≤q⇒0≤q-p (p≤∣p∣ (seq x n))) ⟩
              ℚ.∣ seq x n ∣ ℚ.- seq x n               ≈⟨ ℚP.+-congˡ (ℚ.- seq x n) (ℚP.≃-sym (ℚP.∣-p∣≃∣p∣ (seq x n))) ⟩
              ℚ.∣ ℚ.- seq x n ∣ ℚ.- seq x n           ≈⟨ ℚP.+-congˡ (ℚ.- seq x n) (ℚP.0≤p⇒∣p∣≃p (ℚP.neg-mono-≤ hyp)) ⟩
              ℚ.- seq x n ℚ.- seq x n                 ≤⟨ ℚP.+-mono-≤ -xₙ≤1/2j -xₙ≤1/2j ⟩
              (+ 1 / (2 ℕ.* j)) ℚ.+ (+ 1 / (2 ℕ.* j)) ≈⟨ ℚ.*≡* (solve 1 (λ j ->
                                                         (Κ (+ 1) ⊗ (Κ (+ 2) ⊗ j) ⊕ Κ (+ 1) ⊗ (Κ (+ 2) ⊗ j)) ⊗ j ⊜
                                                         (Κ (+ 1) ⊗ (Κ (+ 2) ⊗ j ⊗ (Κ (+ 2) ⊗ j))))
                                                         refl (+ j)) ⟩
              + 1 / j                                  ∎

            right : (+ 0 / 1) ℚ.≤ seq x n -> ℚ.∣ ℚ.∣ seq x n ∣ ℚ.- seq x n ∣ ℚ.≤ + 1 / j
            right hyp = begin
              ℚ.∣ ℚ.∣ seq x n ∣ ℚ.- seq x n ∣  ≈⟨ ℚP.0≤p⇒∣p∣≃p (ℚP.p≤q⇒0≤q-p (p≤∣p∣ (seq x n))) ⟩
              ℚ.∣ seq x n ∣ ℚ.- seq x n       ≈⟨ ℚP.+-congˡ (ℚ.- seq x n) (ℚP.0≤p⇒∣p∣≃p hyp) ⟩
              seq x n ℚ.- seq x n             ≈⟨ ℚP.+-inverseʳ (seq x n) ⟩
              (+ 0 / 1)                             ≤⟨ ℚP.nonNegative⁻¹ _ ⟩
              + 1 / j                          ∎

@0 nonNegx,y⇒nonNegx*y : ∀ {x y} -> NonNegative x -> NonNegative y -> NonNegative (x * y)
nonNegx,y⇒nonNegx*y {x} {y} nonx nony = nonNeg-cong lem (nonNeg∣x∣ (x * y))
  where
    open ≃-Reasoning
    lem : ∣ x * y ∣ ≃ x * y
    lem = begin
      ∣ x * y ∣     ≈⟨ ∣x*y∣≃∣x∣*∣y∣ x y ⟩
      ∣ x ∣ * ∣ y ∣ ≈⟨ *-cong (nonNegx⇒∣x∣≃x nonx) (nonNegx⇒∣x∣≃x nony) ⟩
      x * y          ∎

posxAndyThenPosxTimesy : ∀ (x y : ℝ) -> Positive x -> Positive y -> Positive (x * y)
posxAndyThenPosxTimesy x y posx posy = let k = fK x ℕ.⊔ fK y; fromPosx = fastLemma281If x posx; fromPosy = fastLemma281If y posy; N₁ = suc (proj₁ fromPosx); N₂ = suc (proj₁ fromPosy); N = N₁ ℕ.⊔ N₂; N₁≤N² = ℕP.≤-trans (ℕP.m≤m⊔n N₁ N₂) (ℕP.m≤n*m N {N} ℕP.0<1+n); N₂≤N² = ℕP.≤-trans (ℕP.m≤n⊔m N₁ N₂) (ℕP.m≤n*m N {N} ℕP.0<1+n) in
                                  lemma281OnlyIf (x * y) (ℕ.pred (N ℕ.* N) :&: λ @0 {(suc k₁) m≥N² ->
                                  let m = suc k₁; N²≤2km = ℕP.≤-trans m≥N² (ℕP.m≤n*m m {2 ℕ.* k} ℕP.0<1+n) in begin
  + 1 / N ℚ.* (+ 1 / N)                           ≤⟨ q≤r⇒+p/r≤+p/q 1 (N₁ ℕ.* N₂) (N ℕ.* N) (ℕP.*-mono-≤ (ℕP.m≤m⊔n N₁ N₂) (ℕP.m≤n⊔m N₁ N₂)) ⟩
  + 1 / N₁ ℚ.* (+ 1 / N₂)                         ≤⟨ ℚ-*-mono-≤ _ _
                                                     (proj₂ fromPosx (2 ℕ.* k ℕ.* m) (ℕP.≤-trans N₁≤N² N²≤2km))
                                                     (proj₂ fromPosy (2 ℕ.* k ℕ.* m) (ℕP.≤-trans N₂≤N² N²≤2km)) ⟩
  seq x (2 ℕ.* k ℕ.* m) ℚ.* seq y (2 ℕ.* k ℕ.* m)  ∎})
  where open ℚP.≤-Reasoning
{-# COMPILE AGDA2HS posxAndyThenPosxTimesy #-}

@0 posx⇒posx⊔y : ∀ {x y} -> Positive x -> Positive (x ⊔ y)
posx⇒posx⊔y {x} {y} posx = let fromPosx = fastLemma281If x posx; N = suc (proj₁ fromPosx) in
                           lemma281OnlyIf (x ⊔ y) (ℕ.pred N :&: λ @0 {(suc k₁) m≥N -> let m = suc k₁ in begin
  + 1 / N             ≤⟨ proj₂ fromPosx m m≥N ⟩
  seq x m             ≤⟨ ℚP.p≤p⊔q (seq x m) (seq y m) ⟩
  seq x m ℚ.⊔ seq y m  ∎})
  where open ℚP.≤-Reasoning

@0 nonNegx⇒nonNegx⊔y : ∀ {x y} -> NonNegative x -> NonNegative (x ⊔ y)
nonNegx⇒nonNegx⊔y {x} {y} nonx = lemma-2-8-2-onlyif (λ @0 {(suc k₁) ->
                                 let n = suc k₁; fromNonx = fastLemma282If nonx n
                                       ; N = proj₁ fromNonx in
                                 N :&: proj₁ (proj₂ fromNonx) , λ m m≥N -> begin
  ℚ.- (+ 1 / n)       ≤⟨ proj₂ (proj₂ fromNonx) m m≥N ⟩
  seq x m             ≤⟨ ℚP.p≤p⊔q (seq x m) (seq y m) ⟩
  seq x m ℚ.⊔ seq y m  ∎})
  where open ℚP.≤-Reasoning

@0 nonNegx,y⇒nonNegx⊓y : ∀ {x y} -> NonNegative x -> NonNegative y -> NonNegative (x ⊓ y)
nonNegx,y⇒nonNegx⊓y {x} {y} nonx nony = lemma-2-8-2-onlyif partA
  where
    open ℚP.≤-Reasoning
    partA : (n : ℕ) {@0 n≢0 : n ≢0} → ∃0 (λ Nₙ → Nₙ ≢0 × ((m : ℕ) → m ℕ.≥ Nₙ → seq (x ⊓ y) m ℚ.≥ ℚ.- (+ 1 / n)))
    partA (suc k₁) = N :&: _ , partB
      where
        n = suc k₁
        fromNonx = fastLemma282If nonx n
        Nx = proj₁ fromNonx
        fromNony = fastLemma282If nony n
        Ny = proj₁ fromNony
        N = suc (Nx ℕ.⊔ Ny)
        Nx≤N = ℕP.≤-trans (ℕP.m≤m⊔n Nx Ny) (ℕP.n≤1+n (ℕ.pred N))
        Ny≤N = ℕP.≤-trans (ℕP.m≤n⊔m Nx Ny) (ℕP.n≤1+n (ℕ.pred N))

        partB : ∀ (m : ℕ) -> m ℕ.≥ N -> seq (x ⊓ y) m ℚ.≥ ℚ.- (+ 1 / n)
        partB m m≥N = [ left , right ]′ (ℚP.≤-total (seq x m) (seq y m))
          where
            left : seq x m ℚ.≤ seq y m -> seq (x ⊓ y) m ℚ.≥ ℚ.- (+ 1 / n)
            left hyp = begin
              ℚ.- (+ 1 / n)       ≤⟨ proj₂ (proj₂ fromNonx) m (ℕP.≤-trans Nx≤N m≥N) ⟩
              seq x m             ≈⟨ ℚP.≃-sym (ℚP.p≤q⇒p⊓q≃p hyp) ⟩
              seq x m ℚ.⊓ seq y m   ∎

            right : seq y m ℚ.≤ seq x m -> seq (x ⊓ y) m ℚ.≥ ℚ.- (+ 1 / n)
            right hyp = begin
              ℚ.- (+ 1 / n)       ≤⟨ proj₂ (proj₂ fromNony) m (ℕP.≤-trans Ny≤N m≥N) ⟩
                  seq y m             ≈⟨ ℚP.≃-sym (ℚP.p≥q⇒p⊓q≃q hyp) ⟩
              seq x m ℚ.⊓ seq y m  ∎

@0 posx,y⇒posx⊓y : ∀ x y -> Positive x -> Positive y -> Positive (x ⊓ y)
posx,y⇒posx⊓y x y posx posy = lemma281OnlyIf (x ⊓ y) (ℕ.pred N :&: lem)
  where
    open ℚP.≤-Reasoning
    fromPosx = fastLemma281If x posx
    Nx = suc (proj₁ fromPosx)
    fromPosy = fastLemma281If y posy
    Ny = suc (proj₁ fromPosy)
    N = Nx ℕ.⊔ Ny
    Nx≤N = ℕP.m≤m⊔n Nx Ny
    Ny≤N = ℕP.m≤n⊔m Nx Ny

    lem : ∀ (m : ℕ) -> m ℕ.≥ N -> seq (x ⊓ y) m ℚ.≥ + 1 / N
    lem m m≥N = [ left , right ]′ (ℚP.≤-total (seq x m) (seq y m))
      where
        left : seq x m ℚ.≤ seq y m -> seq (x ⊓ y) m ℚ.≥ + 1 / N
        left hyp = begin
          + 1 / N             ≤⟨ q≤r⇒+p/r≤+p/q 1 Nx N Nx≤N ⟩
          + 1 / Nx            ≤⟨ proj₂ fromPosx m (ℕP.≤-trans Nx≤N m≥N) ⟩
          seq x m             ≈⟨ ℚP.≃-sym (ℚP.p≤q⇒p⊓q≃p hyp) ⟩
          seq x m ℚ.⊓ seq y m   ∎

        right : seq y m ℚ.≤ seq x m -> seq (x ⊓ y) m ℚ.≥ + 1 / N
        right hyp = begin
          + 1 / N             ≤⟨ q≤r⇒+p/r≤+p/q 1 Ny N Ny≤N ⟩
          + 1 / Ny            ≤⟨ proj₂ fromPosy m (ℕP.≤-trans Ny≤N m≥N) ⟩
          seq y m             ≈⟨ ℚP.≃-sym (ℚP.p≥q⇒p⊓q≃q hyp) ⟩
          seq x m ℚ.⊓ seq y m   ∎

@0 neg-cong : ∀ {x y} -> x ≃ y -> Negative x -> Negative y
neg-cong {x} {y} x≃y negx = posCong (negate x) (negate y) (-‿cong x≃y) negx

@0 nonNeg0 : NonNegative zeroℝ
nonNeg0 = nonNeg* (λ {(suc k₁) -> ℚP.<⇒≤ (ℚP.negative⁻¹ _)})

@0 nonNeg-refl : ∀ {x} -> NonNegative (x - x)
nonNeg-refl {x} = nonNeg-cong (≃-sym (+-inverseʳ x)) nonNeg0

-- The ℝ Solver
-- Use this to solve real number ring equations

module ℝ-Solver where
  open import Data.Bool.Base
  open import Tactic.RingSolver.Core.Polynomial.Parameters
  open import Tactic.RingSolver.Core.AlmostCommutativeRing
  open import Data.Maybe.Base using (nothing)

  ℚ-isZero : ℚᵘ -> Bool
  ℚ-isZero p with p ℚP.≃? (+ 0 / 1)
  ... | .true because ofʸ p₁ = true
  ... | .false because ofⁿ ¬p = false

  ℚ-coeff : RawCoeff _ _
  ℚ-coeff = record
    { rawRing = ℚP.+-*-rawRing
    ; isZero  = ℚ-isZero
    }

  abstract
    ⋆-distrib-+₂ : ∀ (p r : ℚᵘ) -> toReal (p ℚ.+ r) ≃ toReal p + toReal r
    ⋆-distrib-+₂   = ⋆-distrib-+
    ⋆-distrib-*₂ : ∀ p q -> toReal (p ℚ.* q) ≃ toReal p * toReal q
    ⋆-distrib-*₂   = ⋆-distrib-*
    ⋆-distrib-neg₂ : ∀ (p : ℚᵘ) -> toReal (ℚ.- p) ≃ - (toReal p)
    ⋆-distrib-neg₂ = ⋆-distrib-neg

  getMorphism : _-Raw-AlmostCommutative⟶_ ℚP.+-*-rawRing (fromCommutativeRing +-*-commutativeRing (λ x -> nothing))
  getMorphism = record
    { ⟦_⟧    = λ p -> toReal p
    ; +-homo = ⋆-distrib-+₂
    ; *-homo = ⋆-distrib-*₂
    ; -‿homo = ⋆-distrib-neg₂
    ; 0-homo = ≃-refl
    ; 1-homo = ≃-refl
    }

  zero-checker : ∀ p -> T (ℚ-isZero p) -> zeroℝ ≃ toReal p
  zero-checker p hyp with p ℚP.≃? (+ 0 / 1)
  ... | .true because ofʸ p₁ = ⋆-cong (ℚP.≃-sym p₁)

  homo : Homomorphism _ _ _ _
  homo = record
    { from = ℚ-coeff
    ; to   = fromCommutativeRing +-*-commutativeRing (λ x -> nothing)
    ; morphism = getMorphism
    ; Zero-C⟶Zero-R = zero-checker
    }

  open import NonReflective homo public
  open import Tactic.RingSolver.Core.Expression public

-- Properties of pow, the exponentiation function for natural powers
@0 pow-cong : ∀ {x y} -> ∀ n -> x ≃ y -> pow x n ≃ pow y n
pow-cong {x} {y} zero x≃y = ≃-refl
pow-cong {x} {y} (suc n) x≃y = *-cong (pow-cong n x≃y) x≃y

@0 xⁿxᵐ≃xⁿ⁺ᵐ : ∀ x -> ∀ n m -> (pow x n) * (pow x m) ≃ pow x (n ℕ.+ m)
xⁿxᵐ≃xⁿ⁺ᵐ x zero m = *-identityˡ (pow x m)
xⁿxᵐ≃xⁿ⁺ᵐ x (suc n) m = begin
  pow x n * x * pow x m   ≈⟨ solve 3 (λ xⁿ x xᵐ -> xⁿ ⊗ x ⊗ xᵐ ⊜ xⁿ ⊗ xᵐ ⊗ x)
                             ≃-refl (pow x n) x (pow x m) ⟩
  pow x n * pow x m * x   ≈⟨ *-congʳ (xⁿxᵐ≃xⁿ⁺ᵐ x n m) ⟩
  pow x (n ℕ.+ m) * x     ≈⟨ ≃-refl ⟩
  pow x (1 ℕ.+ (n ℕ.+ m)) ≡⟨ cong (λ k -> pow x k) (sym (ℕP.+-assoc 1 n m)) ⟩
  pow x ((1 ℕ.+ n) ℕ.+ m)  ∎
  where
    open ≃-Reasoning
    open ℝ-Solver

-- Properties of _<_, _≤_, etc

@0 <⇒≤ : {x y : ℝ} → x < y → x ≤ y
<⇒≤ {x} {y} x<y = pos⇒nonNeg x<y

-- Helper lemmas often used in the next few order property proofs
private
  z-y+y-x≃z-x : ∀ {x y z} -> (z - y) + (y - x) ≃ z - x
  z-y+y-x≃z-x {x} {y} {z} = solve 3 (λ x y z -> ((z ⊖ y) ⊕ (y ⊖ x)) ⊜ (z ⊖ x)) ≃-refl x y z
    where open ℝ-Solver

  @0 z-x+t-y≃z+t-x+y : ∀ {x y z t} -> (z - x) + (t - y) ≃ (z + t) - (x + y)
  z-x+t-y≃z+t-x+y {x} {y} {z} {t} = solve 4 (λ x y z t -> ((z ⊖ x) ⊕ (t ⊖ y)) ⊜ ((z ⊕ t) ⊖ (x ⊕ y))) ≃-refl x y z t
    where open ℝ-Solver

-- When ≤ is erased but < is not, and we have to create a non-erased <:
ltLe0Trans : (x y z : ℝ) → x < y → @0 y ≤ z → x < z
ltLe0Trans x y z xLty y≤z = posCong ((y - x) + (z - y)) (z - x) (≃-trans (+-comm (y - x) (z - y)) z-y+y-x≃z-x) (posxAndNonNegyThenPosxPlusy (y - x) (z - y) xLty y≤z)
{-# COMPILE AGDA2HS ltLe0Trans #-}

-- Similarly.
le0LtTrans : (x y z : ℝ) → @0 x ≤ y → y < z → x < z
le0LtTrans x y z x≤y yLtz = posCong ((z - y) + (y - x)) (z - x)
                                   z-y+y-x≃z-x (posxAndNonNegyThenPosxPlusy (z - y) (y - x) yLtz x≤y)
{-# COMPILE AGDA2HS le0LtTrans #-}

{-
<-≤-trans : Trans _<_ _≤_ _<_
<-≤-trans x<y y≤z = <-≤0-trans x<y y≤z

≤-<-trans : Trans _≤_ _<_ _<_
≤-<-trans x≤y y<z = ≤0-<-trans x≤y y<z
-}

-- Has to be compilable.
ltTrans : (x y z : ℝ) → @0 (x < y) → y < z → x < z
ltTrans x y z xLty yLtz = posCong ((z - y) + (y - x)) (z - x)
                           z-y+y-x≃z-x (posxAndNonNegyThenPosxPlusy (z - y) (y - x) yLtz (<⇒≤ xLty))
{-# COMPILE AGDA2HS ltTrans #-}

≤-trans : Transitive _≤_
≤-trans {x} {y} {z} x≤y y≤z = nonNeg-cong z-y+y-x≃z-x (nonNegx,y⇒nonNegx+y y≤z x≤y)

@0 +-mono-≤ : _+_ Preserves₂ _≤_ ⟶ _≤_ ⟶ _≤_
+-mono-≤ x≤z y≤t = nonNeg-cong z-x+t-y≃z+t-x+y (nonNegx,y⇒nonNegx+y x≤z y≤t)

@0 +-monoʳ-≤ : ∀ (x : ℝ) -> (_+_ x) Preserves _≤_ ⟶ _≤_
+-monoʳ-≤ x y≤z = +-mono-≤ nonNeg-refl y≤z

@0 +-monoˡ-≤ : ∀ (x : ℝ) -> (_+ x) Preserves _≤_ ⟶ _≤_
+-monoˡ-≤ x y≤z = +-mono-≤ y≤z nonNeg-refl

@0 +-mono-< : ∀ {x z y t : ℝ} → x < z → y < t → x + y < z + t -- _+_ Preserves₂ _<_ ⟶ _<_ ⟶ _<_
+-mono-< {x} {z} {y} {t} x<z y<t = posCong ((z - x) + (t - y)) ((z + t) - (x + y))
                    z-x+t-y≃z+t-x+y (posx,y⇒posx+y x<z y<t)

@0 +-monoʳ-< : ∀ (x : ℝ) {y z : ℝ} → y < z → x + y < x + z -- ∀ x → (_+_ x) Preserves _<_ ⟶ _<_
+-monoʳ-< x {y} {z} y<z = posCong (z - y) (x + z - (x + y))
                           (solve 3 (λ x y z -> (z ⊖ y) ⊜ (x ⊕ z ⊖ (x ⊕ y))) ≃-refl x y z) y<z
  where open ℝ-Solver

@0 +-monoˡ-< : ∀ (x : ℝ) {y z : ℝ} → y < z → y + x < z + x -- ∀ x → (_+ x) Preserves _<_ ⟶ _<_
+-monoˡ-< x {y} {z} y<z = posCong ((x + z) - (x + y)) (z + x - (y + x))
                           (+-cong (+-comm x z) (-‿cong (+-comm x y))) (+-monoʳ-< x y<z)

≤-reflexive : _≃_ ⇒ _≤_
≤-reflexive {x} x≃y = nonNeg-cong (+-congˡ (- x) x≃y) nonNeg-refl

@0 ≤-refl : Reflexive _≤_
≤-refl = ≤-reflexive ≃-refl

≤-isPreorder : IsPreorder _≃_ _≤_
≤-isPreorder = record
  { isEquivalence = ≃-isEquivalence
  ; reflexive     = ≤-reflexive
  ; trans         = ≤-trans
  }

@0 ≤-respʳ-≃ : _≤_ Respectsʳ _≃_
≤-respʳ-≃ {x} {y} {z} y≃z x≤y = nonNeg-cong (+-congˡ (- x) y≃z) x≤y

@0 ≤-respˡ-≃ : _≤_ Respectsˡ _≃_
≤-respˡ-≃ {x} {y} {z} y≃z y≤x = nonNeg-cong (+-congʳ x (-‿cong y≃z)) y≤x

-- when we work with erased ≃ and would like a non-erased <:
-- again a compilable version
ltRespREq : (x y z : ℝ) → @0 y ≃ z → x < y → x < z
ltRespREq x y z y≃z xLty = ltLe0Trans x y z xLty (≤-reflexive y≃z)
{-# COMPILE AGDA2HS ltRespREq #-}

ltRespLEq : (x y z : ℝ) → @0 y ≃ z → x > y → x > z
ltRespLEq x y z y≃z xGty = le0LtTrans z y x (≤-reflexive (≃-sym y≃z)) xGty
{-# COMPILE AGDA2HS ltRespLEq #-}

-- Erased aliases for the old ones
@0 <-respʳ-≃ : {x y z : ℝ} → @0 y ≃ z → x < y → x < z
<-respʳ-≃ {x} {y} {z} y≃z x<y = ltRespREq x y z y≃z x<y

@0 <-respˡ-≃ : {x y z : ℝ} → @0 y ≃ z → x > y → x > z
<-respˡ-≃ {x} {y} {z} y≃z x>y = ltRespLEq x y z y≃z x>y

-- @0 <-resp-≃ : _<_ Respects₂ _≃_
-- <-resp-≃ = <-respʳ-≃ , <-respˡ-≃

-- sadly, we cannot put versions with erased arguments here;
-- so we cannot use ≤-Reasoning if we work with erased ≃ or ≤ and want a non-erased <

module ≤-Reasoning where
  open import TripleReasoning {Level.zero} {Level.zero} {Level.zero} {Level.zero} {ℝ}
    {_≃_}
    {_≤_}
    {_<_}
    ≃-refl
    ≃-sym
    ≃-trans
    ≤-reflexive
    ≤-trans 
    ltTrans
    ltRespREq
    ltRespLEq
    <⇒≤
    ltLe0Trans
    le0LtTrans
    public

@0 *-monoʳ-≤-nonNeg : ∀ {x y z} -> x ≤ z -> NonNegative y -> x * y ≤ z * y
*-monoʳ-≤-nonNeg {x} {y} {z} x≤z nony = nonNeg-cong
                                        (solve 3 (λ x y z -> ((z ⊖ x) ⊗ y) ⊜ (z ⊗ y ⊖ x ⊗ y)) ≃-refl x y z)
                                        (nonNegx,y⇒nonNegx*y x≤z nony)
  where open ℝ-Solver

@0 *-monoˡ-≤-nonNeg : ∀ {x y z} -> x ≤ z -> NonNegative y -> y * x ≤ y * z
*-monoˡ-≤-nonNeg {x} {y} {z} x≤z nony = begin
  y * x ≈⟨ *-comm y x ⟩
  x * y ≤⟨ *-monoʳ-≤-nonNeg x≤z nony ⟩
  z * y ≈⟨ *-comm z y ⟩
  y * z  ∎
  where open ≤-Reasoning

multiMonoRLtPos : ∀ (y : ℝ) → Positive y → (x z : ℝ) → x < z → y * x < y * z -- ∀ {y} -> Positive y -> (_*_ y) Preserves _<_ ⟶ _<_
multiMonoRLtPos y posy x z xLtz = posCong (y * (z - x)) (y * z - y * x)
                                     (solve 3 (λ x y z -> (y ⊗ (z ⊖ x)) ⊜ (y ⊗ z ⊖ y ⊗ x)) ≃-refl x y z)
                                     (posxAndyThenPosxTimesy y (z - x) posy xLtz)
  where open ℝ-Solver
{-# COMPILE AGDA2HS multiMonoRLtPos #-}

multiMonoLLtPos : ∀ (y : ℝ) → Positive y → (x z : ℝ) → x < z → x * y < z * y  -- ∀ {y} -> Positive y -> (_* y) Preserves _<_ ⟶ _<_
multiMonoLLtPos y posy x z xLtz = ltRespLEq (z * y) (y * x) (x * y) (*-comm y x)
                                    (ltRespREq (y * x) (y * z) (z * y) (*-comm y z)
                                      (multiMonoRLtPos y posy x z xLtz))
 {-begin-strict
  x * y ≈⟨ *-comm x y ⟩
  y * x <⟨ multiMonoRLtPos y posy x z xLtz ⟩
  y * z ≈⟨ *-comm y z ⟩
  z * y  ∎
  where
    open ≤-Reasoning-}
{-# COMPILE AGDA2HS multiMonoLLtPos #-}

negMonoLt : (x y : ℝ) → x < y → negate x > negate y
negMonoLt x y xLty = posCong (y - x) (negate x - negate y)
                         (solve 2 (λ x y -> (y ⊖ x) ⊜ (⊝ x ⊖ (⊝ y))) ≃-refl x y)
                         xLty
  where open ℝ-Solver
{-# COMPILE AGDA2HS negMonoLt #-}

@0 neg-mono-≤ : -_ Preserves _≤_ ⟶ _≥_
neg-mono-≤ {x} {y} x≤y = nonNeg-cong
                         (solve 2 (λ x y -> (y ⊖ x) ⊜ (⊝ x ⊖ (⊝ y))) ≃-refl x y)
                         x≤y
  where open ℝ-Solver

@0 x≤x⊔y : ∀ x y -> x ≤ x ⊔ y
x≤x⊔y x y = nonNeg* (λ {(suc k₁) -> let n = suc k₁ in begin (
  ℚ.- (+ 1 / n)                                           ≤⟨ ℚP.nonPositive⁻¹ _ ⟩
  (+ 0 / 1)                                                     ≈⟨ ℚP.≃-sym (ℚP.+-inverseʳ (seq x (2 ℕ.* n))) ⟩
  seq x (2 ℕ.* n) ℚ.- seq x (2 ℕ.* n)                     ≤⟨ ℚP.+-monoˡ-≤ (ℚ.- seq x (2 ℕ.* n)) (ℚP.p≤p⊔q (seq x (2 ℕ.* n)) (seq y (2 ℕ.* n))) ⟩
  seq x (2 ℕ.* n) ℚ.⊔ seq y (2 ℕ.* n) ℚ.- seq x (2 ℕ.* n)  ∎)})
  where open ℚP.≤-Reasoning

@0 x≤y⊔x : ∀ x y -> x ≤ y ⊔ x
x≤y⊔x x y = begin
  x     ≤⟨ x≤x⊔y x y ⟩
  x ⊔ y ≈⟨ ⊔-comm x y ⟩
  y ⊔ x  ∎
  where
    open ≤-Reasoning

@0 x⊓y≤x : ∀ x y -> x ⊓ y ≤ x
x⊓y≤x x y = nonNeg* λ {(suc k₁) -> let n = suc k₁ in begin 
      ℚ.- (+ 1 / n)                             ≤⟨ ℚP.nonPositive⁻¹ _ ⟩
      (+ 0 / 1)                                       ≈⟨ ℚP.≃-sym (ℚP.+-inverseʳ (seq x (2 ℕ.* n))) ⟩ 
      seq x (2 ℕ.* n) ℚ.- seq x (2 ℕ.* n)       ≤⟨ ℚP.+-monoʳ-≤ (seq x (2 ℕ.* n)) (ℚP.neg-mono-≤ (ℚP.p⊓q≤p (seq x (2 ℕ.* n)) (seq y (2 ℕ.* n)))) ⟩
      seq x (2 ℕ.* n) ℚ.- seq (x ⊓ y) (2 ℕ.* n) ∎}
  where open ℚP.≤-Reasoning

@0 x⊓y≤y : ∀ x y -> x ⊓ y ≤ y
x⊓y≤y x y = begin
  x ⊓ y ≈⟨ ⊓-comm x y ⟩
  y ⊓ x ≤⟨ x⊓y≤x y x ⟩
  y      ∎
  where
    open ≤-Reasoning

@0 ≤-antisym : Antisymmetric _≃_ _≤_
≤-antisym {x} {y} (nonNeg* x≤y) (nonNeg* y≤x) = ≃-sym partB
  where
    partA : ∀ (n : ℕ) -> {n≢0 : n ≢0} -> ℚ.∣ seq (x - y) n ℚ.- (+ 0 / 1) ∣ ℚ.≤ (+ 2 / n) {n≢0}
    partA (suc k₁) = begin
      ℚ.∣ seq x (2 ℕ.* n) ℚ.- seq y (2 ℕ.* n) ℚ.- (+ 0 / 1) ∣ ≈⟨ ℚP.∣-∣-cong (ℚP.+-identityʳ (seq x (2 ℕ.* n) ℚ.- seq y (2 ℕ.* n))) ⟩
      ℚ.∣ seq x (2 ℕ.* n) ℚ.- seq y (2 ℕ.* n) ∣         ≤⟨ [ left , right ]′ (ℚP.≤-total (seq x (2 ℕ.* n)) (seq y (2 ℕ.* n))) ⟩
      + 2 / n                                            ∎
      where
        open ℚP.≤-Reasoning
        open ℚ-Solver
        n = suc k₁

        left : seq x (2 ℕ.* n) ℚ.≤ seq y (2 ℕ.* n) -> ℚ.∣ seq x (2 ℕ.* n) ℚ.- seq y (2 ℕ.* n) ∣ ℚ.≤ + 2 / n
        left hyp = begin
          ℚ.∣ seq x (2 ℕ.* n) ℚ.- seq y (2 ℕ.* n) ∣ ≈⟨ ℚP.≃-trans (ℚP.≃-sym (ℚP.∣-p∣≃∣p∣ (seq x (2 ℕ.* n) ℚ.- seq y (2 ℕ.* n))))
                                                       (ℚP.0≤p⇒∣p∣≃p (ℚP.neg-mono-≤ (ℚP.p≤q⇒p-q≤0 hyp))) ⟩
          ℚ.- (seq x (2 ℕ.* n) ℚ.- seq y (2 ℕ.* n)) ≤⟨ ℚP.≤-respʳ-≃ (ℚP.neg-involutive (+ 1 / n)) (ℚP.neg-mono-≤ (y≤x n)) ⟩
          + 1 / n                                   ≤⟨ p≤q⇒p/r≤q/r (+ 1) (+ 2) n (ℤ.+≤+ (ℕ.s≤s ℕ.z≤n)) ⟩
          + 2 / n                                    ∎

        right : seq y (2 ℕ.* n) ℚ.≤ seq x (2 ℕ.* n) -> ℚ.∣ seq x (2 ℕ.* n) ℚ.- seq y (2 ℕ.* n) ∣ ℚ.≤ + 2 / n
        right hyp = begin
          ℚ.∣ seq x (2 ℕ.* n) ℚ.- seq y (2 ℕ.* n) ∣ ≈⟨ ℚP.0≤p⇒∣p∣≃p (ℚP.p≤q⇒0≤q-p hyp) ⟩
          seq x (2 ℕ.* n) ℚ.- seq y (2 ℕ.* n)       ≈⟨ solve 2 (λ x y -> (x ⊖ y) ⊜ (⊝ (y ⊖ x))) ℚP.≃-refl (seq x (2 ℕ.* n)) (seq y (2 ℕ.* n)) ⟩
          ℚ.- (seq y (2 ℕ.* n) ℚ.- seq x (2 ℕ.* n)) ≤⟨ ℚP.≤-respʳ-≃ (ℚP.neg-involutive (+ 1 / n)) (ℚP.neg-mono-≤ (x≤y n)) ⟩
          + 1 / n                                   ≤⟨ p≤q⇒p/r≤q/r (+ 1) (+ 2) n (ℤ.+≤+ (ℕ.s≤s ℕ.z≤n)) ⟩
          + 2 / n                                    ∎

    partB : y ≃ x
    partB = begin
      y             ≈⟨ ≃-sym (+-identityʳ y) ⟩
      y + zeroℝ        ≈⟨ +-congʳ y (≃-sym (*≃* partA)) ⟩
      y + (x - y)   ≈⟨ +-congʳ y (+-comm x (- y)) ⟩
      y + (- y + x) ≈⟨ ≃-sym (+-assoc y (- y) x) ⟩
      y - y + x     ≈⟨ +-congˡ x (+-inverseʳ y) ⟩
      zeroℝ + x        ≈⟨ +-identityˡ x ⟩
      x              ∎
      where open ≃-Reasoning

@0 0≃-0 : zeroℝ ≃ - zeroℝ
0≃-0 = ⋆-distrib-neg (+ 0 / 1)

private
  -- Helper for the next few proofs
  @0 x-0≃x : ∀ {x} -> x - zeroℝ ≃ x
  x-0≃x {x} = ≃-trans (+-congʳ x (≃-sym 0≃-0)) (+-identityʳ x)

zeroLtxThenPosx : ∀ (x : ℝ) -> zeroℝ < x -> Positive x
zeroLtxThenPosx x zeroLtx = posCong (x - zeroℝ) x x-0≃x zeroLtx
{-# COMPILE AGDA2HS zeroLtxThenPosx #-}

posxThenZeroLtx : ∀ (x : ℝ) -> Positive x -> zeroℝ < x
posxThenZeroLtx x posx = posCong x (x - zeroℝ) (≃-sym x-0≃x) posx
{-# COMPILE AGDA2HS posxThenZeroLtx #-}

@0 0≤x⇒nonNegx : ∀ {x} -> zeroℝ ≤ x -> NonNegative x
0≤x⇒nonNegx {x} 0≤x = nonNeg-cong x-0≃x 0≤x

@0 nonNegx⇒0≤x : ∀ {x} -> NonNegative x -> zeroℝ ≤ x
nonNegx⇒0≤x {x} nonx = nonNeg-cong (≃-sym x-0≃x) nonx

xLtZeroThenNegx : ∀ (x : ℝ) -> x < zeroℝ -> Negative x
xLtZeroThenNegx x xLt0 = posCong (zeroℝ + negate x) (negate x) (+-identityˡ (- x)) xLt0
{-# COMPILE AGDA2HS xLtZeroThenNegx #-}

negxThenxLtZero : ∀ (x : ℝ) -> Negative x -> x < zeroℝ
negxThenxLtZero x negx = posCong (negate x) (zeroℝ + negate x) (≃-sym (+-identityˡ (- x))) negx
{-# COMPILE AGDA2HS negxThenxLtZero #-}

zeroLtxMinusxThenxLty : ∀ x y -> zeroℝ < y - x -> x < y
zeroLtxMinusxThenxLty x y zeroLtyMx = posCong (y - x - zeroℝ) (y - x) (≃-trans (+-congʳ (y - x) (≃-sym 0≃-0)) (+-identityʳ (y - x))) zeroLtyMx
{-# COMPILE AGDA2HS zeroLtxMinusxThenxLty #-}

xLtyThenZeroLtyMinusx : ∀ x y -> x < y -> zeroℝ < y - x
xLtyThenZeroLtyMinusx x y xLty = posCong (y - x) (y - x - zeroℝ) (≃-trans (≃-sym (+-identityʳ (y - x))) (+-congʳ (y - x) 0≃-0)) xLty
{-# COMPILE AGDA2HS xLtyThenZeroLtyMinusx #-}

@0 ⋆-distrib-to-p⋆-q⋆ : ∀ p q -> (p ℚ.- q) ⋆ ≃ p ⋆ - (q ⋆)
⋆-distrib-to-p⋆-q⋆ p q = solve 0 (Κ (p ℚ.- q) ⊜ (Κ p ⊖ Κ q)) ≃-refl
  where open ℝ-Solver

-- For unpacking the sigma from a Positive proof.
@0 unpackSigmaFromPos : ∀ {x} → Positive x → Σ0 ℕ (λ (n-1 : ℕ) -> seq x (suc n-1) ℚ.> + 1 / (suc n-1))
unpackSigmaFromPos (MkPos s) = s

-- this pattern matching won't end well...
zeroLtpThenZeroLtToRealp : ∀ p -> @0 ℚ.Positive p -> Positive (toReal p)
zeroLtpThenZeroLtToRealp (mkℚᵘ +[1+ p ] q-1) _ = let q = suc q-1 in MkPos (q :&: ℚ.*<* (begin-strict
  + 1 ℤ.* + q          ≡⟨ ℤP.*-identityˡ (+ q) ⟩
  + q                  <⟨ ℤ.+<+ (ℕP.n<1+n q) ⟩
  + suc q              ≤⟨ ℤ.+≤+ (ℕP.m≤n*m (suc q) {suc p} ℕP.0<1+n) ⟩
  +[1+ p ] ℤ.* + suc q  ∎))
  where open ℤP.≤-Reasoning

-- therefore:
zeroLtpThenZeroLtToRealp' : ∀ p -> @0 ℚ.Positive p -> Positive (toReal p)
zeroLtpThenZeroLtToRealp' a posa = MkPos (q :&: finalProof)
  where
  q : ℕ
  q = suc (denominator-1 a)

  -- we use the proof from the previous one
  @0 posa⋆ : Positive (toReal a)
  posa⋆ = zeroLtpThenZeroLtToRealp a posa
  @0 qIsTheOne : ∀ p -> (@0 posp : ℚ.Positive p) -> proj₁ (unpackSigmaFromPos (zeroLtpThenZeroLtToRealp p posp)) ≡ suc (denominator-1 p)
  qIsTheOne (mkℚᵘ +[1+ p ] q-1) _ = refl
  @0 finalProof : seq (toReal a) (suc q) ℚ.> + 1 / (suc q)
  finalProof = subst (λ (n-1 : ℕ) -> seq (toReal a) (suc n-1) ℚ.> + 1 / (suc n-1)) (qIsTheOne a posa) (proj₂ (unpackSigmaFromPos posa⋆))
{-# COMPILE AGDA2HS zeroLtpThenZeroLtToRealp' #-}

proj₁zeroLtpThenZeroLtToRealp≡proj₁zeroLtpThenZeroLtToRealp' : ∀ p -> (@0 posp : ℚ.Positive p) ->
                                            proj₁ (unpackSigmaFromPos (zeroLtpThenZeroLtToRealp p posp)) ≡ proj₁ (unpackSigmaFromPos (zeroLtpThenZeroLtToRealp' p posp))
proj₁zeroLtpThenZeroLtToRealp≡proj₁zeroLtpThenZeroLtToRealp' (mkℚᵘ +[1+ p ] q-1) _ = refl

pLtqThenToRealpLtToRealq : ∀ (p q : ℚᵘ) -> @0 p ℚ.< q -> toReal p < toReal q
pLtqThenToRealpLtToRealq p q pLtq = posCong (toReal (q ℚ.- p)) (toReal q - toReal p)
                                      (⋆-distrib-to-p⋆-q⋆ q p) (zeroLtpThenZeroLtToRealp (q ℚ.- p) (ℚ.positive (p<q⇒0<q-p p q pLtq)))
{-# COMPILE AGDA2HS pLtqThenToRealpLtToRealq #-}

@0 ∣-x∣≃∣x∣ : ∀ {x} -> ∣ - x ∣ ≃ ∣ x ∣
∣-x∣≃∣x∣ {x} = *≃* λ @0 {(suc k₁) -> let n = suc k₁ in begin
  ℚ.∣ ℚ.∣ ℚ.- seq x n ∣ ℚ.- ℚ.∣ seq x n ∣ ∣ ≈⟨ ℚP.∣-∣-cong (ℚP.+-congˡ (ℚ.- ℚ.∣ seq x n ∣) (ℚP.∣-p∣≃∣p∣ (seq x n))) ⟩
  ℚ.∣ ℚ.∣ seq x n ∣ ℚ.- ℚ.∣ seq x n ∣ ∣     ≈⟨ ℚP.∣-∣-cong (ℚP.+-inverseʳ ℚ.∣ seq x n ∣) ⟩
  (+ 0 / 1)                                      ≤⟨ ℚP.nonNegative⁻¹ _ ⟩
  + 2 / n                                   ∎}
  where open ℚP.≤-Reasoning

@0 ∣x-y∣≃∣y-x∣ : ∀ x y -> ∣ x - y ∣ ≃ ∣ y - x ∣
∣x-y∣≃∣y-x∣ x y = begin
  ∣ x - y ∣     ≈⟨ ≃-sym ∣-x∣≃∣x∣ ⟩
  ∣ - (x - y) ∣ ≈⟨ ∣-∣-cong (solve 2 (λ x y -> (⊝ (x ⊖ y)) ⊜ (y ⊖ x)) ≃-refl x y) ⟩
  ∣ y - x ∣      ∎
  where
    open ℝ-Solver
    open ≃-Reasoning

@0 ≮⇒≥ : _≮_ ⇒ _≥_
≮⇒≥ {x} {y} x≮y = nonNeg* (λ {(suc k₁) -> let n = suc k₁ in
                  ℚP.≤-respʳ-≃ (solve 2 (λ x y -> (⊝ (y ⊖ x)) ⊜ (x ⊖ y)) ℚP.≃-refl (seq x (2 ℕ.* n)) (seq y (2 ℕ.* n)))
                  (ℚP.neg-mono-≤ ([ (λ hyp -> hyp) , (λ hyp -> ⊥-elim (x≮y (MkPos (k₁ :&: hyp)))) ]′ (≤∨> (seq (y - x) n) (+ 1 / n))))})
  where open ℚ-Solver

-- Properties of _negate and _*_

@0 neg-distribˡ-* : ∀ x y -> - (x * y) ≃ - x * y
neg-distribˡ-* = solve 2 (λ x y -> (⊝ (x ⊗ y)) ⊜ ((⊝ x) ⊗ y)) ≃-refl
  where open ℝ-Solver

@0 neg-distribʳ-* : ∀ x y -> - (x * y) ≃ x * (- y)
neg-distribʳ-* = solve 2 (λ x y -> (⊝ (x ⊗ y)) ⊜ (x ⊗ (⊝ y))) ≃-refl
  where open ℝ-Solver

-- Properties of ∣_∣ and ordering

@0 0≤∣x∣ : ∀ x -> zeroℝ ≤ ∣ x ∣
0≤∣x∣ x = nonNegx⇒0≤x (nonNeg∣x∣ x)

@0 ∣x+y∣≤∣x∣+∣y∣ : ∀ x y -> ∣ x + y ∣ ≤ ∣ x ∣ + ∣ y ∣
∣x+y∣≤∣x∣+∣y∣ x y = nonNeg* (λ @0 {(suc k₁) ->
                  let n = suc k₁; ∣x₄ₙ∣ = ℚ.∣ seq x (2 ℕ.* (2 ℕ.* n)) ∣
                         ; ∣y₄ₙ∣ = ℚ.∣ seq y (2 ℕ.* (2 ℕ.* n)) ∣
                         ; ∣x₄ₙ+y₄ₙ∣ = ℚ.∣ seq x (2 ℕ.* (2 ℕ.* n)) ℚ.+ seq y (2 ℕ.* (2 ℕ.* n)) ∣ in begin
  ℚ.- (+ 1 / n)                        ≤⟨ ℚP.nonPositive⁻¹ _ ⟩
  (+ 0 / 1)                                  ≈⟨ ℚP.≃-sym (ℚP.+-inverseʳ (∣x₄ₙ∣ ℚ.+ ∣y₄ₙ∣)) ⟩
  ∣x₄ₙ∣ ℚ.+ ∣y₄ₙ∣ ℚ.- (∣x₄ₙ∣ ℚ.+ ∣y₄ₙ∣) ≤⟨ ℚP.+-monoʳ-≤ (∣x₄ₙ∣ ℚ.+ ∣y₄ₙ∣)
                                          (ℚP.neg-mono-≤ (ℚP.∣p+q∣≤∣p∣+∣q∣ (seq x (2 ℕ.* (2 ℕ.* n))) (seq y (2 ℕ.* (2 ℕ.* n))))) ⟩
  ∣x₄ₙ∣ ℚ.+ ∣y₄ₙ∣ ℚ.- ∣x₄ₙ+y₄ₙ∣          ∎})
  where open ℚP.≤-Reasoning

@0 x≤∣x∣ : ∀ {x} -> x ≤ ∣ x ∣
x≤∣x∣ {x} = nonNeg* (λ @0 {(suc k₁) -> let n = suc k₁ in begin
  ℚ.- (+ 1 / n)                             ≤⟨ ℚP.nonPositive⁻¹ _ ⟩
  (+ 0 / 1)                                       ≤⟨ ℚP.p≤q⇒0≤q-p (p≤∣p∣ (seq x (2 ℕ.* n))) ⟩
  ℚ.∣ seq x (2 ℕ.* n) ∣ ℚ.- seq x (2 ℕ.* n)  ∎})
  where open ℚP.≤-Reasoning

xNonZeroThenZeroLtAbsx : ∀ (x : ℝ) -> x ≄ zeroℝ -> zeroℝ < abs x
xNonZeroThenZeroLtAbsx x (Left xLtZero) = ltRespLEq (abs x) (negate zeroℝ) (zeroℝ) (≃-sym 0≃-0)
                                            (ltRespREq (negate zeroℝ) (abs (negate x)) (abs x) ∣-x∣≃∣x∣
                                              (ltLe0Trans (negate zeroℝ) (negate x) (abs (negate x)) (negMonoLt x zeroℝ xLtZero)
                                                                                                      x≤∣x∣))
  {-begin-strict
  zeroℝ       ≈⟨ 0≃-0 ⟩
  - zeroℝ     <⟨ negMonoLt x<0 ⟩
  - x      ≤⟨ x≤∣x∣ ⟩
  ∣ - x ∣  ≈⟨ ∣-x∣≃∣x∣ ⟩
  ∣ x ∣     ∎
  where open ≤-Reasoning-}
xNonZeroThenZeroLtAbsx x (Right zeroLtx) = ltLe0Trans zeroℝ x (abs x) zeroLtx x≤∣x∣
{-# COMPILE AGDA2HS xNonZeroThenZeroLtAbsx #-}

xNonZeroThenPosAbsx : ∀ (x : ℝ) -> x ≄ zeroℝ -> Positive (abs x)
xNonZeroThenPosAbsx x xNonZero = zeroLtxThenPosx (abs x) (xNonZeroThenZeroLtAbsx x xNonZero)
{-# COMPILE AGDA2HS xNonZeroThenPosAbsx #-}

absxLtyThenNegyLtxLty : ∀ x y -> abs x < y -> (negate y < x) Tuple.× (x < y)
absxLtyThenNegyLtxLty x y absxLty = (ltLe0Trans (negate y) (negate (abs x)) x (negMonoLt (abs x) y absxLty) (begin
    negate (abs x)          ≈⟨ -‿cong (≃-sym ∣-x∣≃∣x∣) ⟩
    negate (abs (negate x)) ≤⟨ neg-mono-≤ x≤∣x∣ ⟩
    negate (negate x)       ≈⟨ neg-involutive x ⟩
    x                       ∎)) Tuple.,
  (le0LtTrans x (abs x) y x≤∣x∣ absxLty)
  where open ≤-Reasoning
{-# COMPILE AGDA2HS absxLtyThenNegyLtxLty #-}

xLtzAndyLtzThenMaxxyLtz : ∀ (x y z : ℝ) -> x < z -> y < z -> x ⊔ y < z
xLtzAndyLtzThenMaxxyLtz x y z xLtz yLtz = lemma281OnlyIf (z - (x ⊔ y)) (ℕ.pred k :&: lem)
  where
    open ℚP.≤-Reasoning
    fromxLtz = fastLemma281If (z - x) xLtz
    k₁ = suc (proj₁ fromxLtz)
    fromyLtz = fastLemma281If (z - y) yLtz
    k₂ = suc (proj₁ fromyLtz)
    k = k₁ ℕ.⊔ k₂

    @0 lem : ∀ (m : ℕ) -> m ℕ.≥ k -> seq (z - (x ⊔ y)) m ℚ.≥ + 1 / k
    lem m m≥k = [ left , right ]′ (ℚP.≤-total (seq y (2 ℕ.* m)) (seq x (2 ℕ.* m)))
      where
        @0 left : seq x (2 ℕ.* m) ℚ.≥ seq y (2 ℕ.* m) -> seq (z - (x ⊔ y)) m ℚ.≥ + 1 / k
        left x₂ₘ≥y₂ₘ = begin
          + 1 / k                                                   ≤⟨ q≤r⇒+p/r≤+p/q 1 k₁ k (ℕP.m≤m⊔n k₁ k₂) ⟩
          + 1 / k₁                                                  ≤⟨ proj₂ fromxLtz m
                                                                       (ℕP.≤-trans (ℕP.m≤m⊔n k₁ k₂) m≥k) ⟩
          seq z (2 ℕ.* m) ℚ.- seq x (2 ℕ.* m)                       ≈⟨ ℚP.+-congʳ (seq z (2 ℕ.* m))
                                                                       (ℚP.-‿cong (ℚP.≃-sym (ℚP.p≥q⇒p⊔q≃p x₂ₘ≥y₂ₘ))) ⟩
          seq z (2 ℕ.* m) ℚ.- (seq x (2 ℕ.* m) ℚ.⊔ seq y (2 ℕ.* m))  ∎

        right : seq y (2 ℕ.* m) ℚ.≥ seq x (2 ℕ.* m) -> seq (z - (x ⊔ y)) m ℚ.≥ + 1 / k
        right y₂ₘ≥x₂ₘ = begin 
          + 1 / k                                                   ≤⟨ q≤r⇒+p/r≤+p/q 1 k₂ k (ℕP.m≤n⊔m k₁ k₂) ⟩
          + 1 / k₂                                                  ≤⟨ proj₂ fromyLtz m
                                                                       (ℕP.≤-trans (ℕP.m≤n⊔m k₁ k₂) m≥k) ⟩
          seq z (2 ℕ.* m) ℚ.- seq y (2 ℕ.* m)                       ≈⟨ ℚP.+-congʳ (seq z (2 ℕ.* m))
                                                                       (ℚP.-‿cong (ℚP.≃-sym (ℚP.p≤q⇒p⊔q≃q y₂ₘ≥x₂ₘ))) ⟩
          seq z (2 ℕ.* m) ℚ.- (seq x (2 ℕ.* m) ℚ.⊔ seq y (2 ℕ.* m))  ∎
{-# COMPILE AGDA2HS xLtzAndyLtzThenMaxxyLtz #-}

@0 p⋆<q⋆⇒p<q : ∀ p q -> p ⋆ < q ⋆ -> p ℚ.< q
p⋆<q⋆⇒p<q p q (MkPos (n :&: p⋆<q⋆)) = 0<q-p⇒p<q p q (begin-strict
  (+ 0 / 1)           ≤⟨ ℚP.nonNegative⁻¹ _ ⟩
  + 1 / (suc n) <⟨ p⋆<q⋆ ⟩
  q ℚ.- p        ∎)
  where open ℚP.≤-Reasoning

pospThenPosToRealp : ∀ p -> @0 ℚ.Positive p -> Positive (toReal p)
pospThenPosToRealp p posp = zeroLtxThenPosx (toReal p) (pLtqThenToRealpLtToRealq (+ 0 / 1) p (ℚP.positive⁻¹ posp))
{-# COMPILE AGDA2HS pospThenPosToRealp #-}

@0 x<y∧x<z⇒x<y⊓z : ∀ x y z -> x < y -> x < z -> x < y ⊓ z
x<y∧x<z⇒x<y⊓z x y z x<y x<z = lemma281OnlyIf ((y ⊓ z) - x) (ℕ.pred N :&: lem)
  where
    open ℚP.≤-Reasoning
    fromx<y = fastLemma281If (y - x) x<y
    N₁ = suc (proj₁ fromx<y)
    fromx<z = fastLemma281If (z - x) x<z
    N₂ = suc (proj₁ fromx<z)
    N = N₁ ℕ.⊔ N₂

    lem : ∀ (m : ℕ) -> m ℕ.≥ N -> seq (y ⊓ z - x) m ℚ.≥ + 1 / N
    lem m m≥N = [ left , right ]′ (ℚP.≤-total (seq y (2 ℕ.* m)) (seq z (2 ℕ.* m)))
      where
        N₁≤N = ℕP.m≤m⊔n N₁ N₂
        N₂≤N = ℕP.m≤n⊔m N₁ N₂

        left : seq y (2 ℕ.* m) ℚ.≤ seq z (2 ℕ.* m) ->
               seq (y ⊓ z - x) m ℚ.≥ + 1 / N
        left y₂ₘ≤z₂ₘ = begin
          + 1 / N                                   ≤⟨ q≤r⇒+p/r≤+p/q 1 N₁ N N₁≤N ⟩
          + 1 / N₁                                  ≤⟨ proj₂ fromx<y m (ℕP.≤-trans N₁≤N m≥N) ⟩
          seq y (2 ℕ.* m) ℚ.- seq x (2 ℕ.* m)       ≈⟨ ℚP.+-congˡ (ℚ.- seq x (2 ℕ.* m))
                                                       (ℚP.≃-sym (ℚP.p≤q⇒p⊓q≃p y₂ₘ≤z₂ₘ)) ⟩
          seq (y ⊓ z) (2 ℕ.* m) ℚ.- seq x (2 ℕ.* m)  ∎
          where
            test : seq (y - x) m ℚ.≃ seq y (2 ℕ.* m) ℚ.- seq x (2 ℕ.* m)
            test = ℚP.≃-refl

        right : seq z (2 ℕ.* m) ℚ.≤ seq y (2 ℕ.* m) ->
                seq (y ⊓ z - x) m ℚ.≥ + 1 / N
        right z₂ₘ≤y₂ₘ = begin
          + 1 / N                                   ≤⟨ q≤r⇒+p/r≤+p/q 1 N₂ N N₂≤N ⟩
          + 1 / N₂                                  ≤⟨ proj₂ fromx<z m (ℕP.≤-trans N₂≤N m≥N) ⟩
          seq z (2 ℕ.* m) ℚ.- seq x (2 ℕ.* m)       ≈⟨ ℚP.+-congˡ (ℚ.- seq x (2 ℕ.* m))
                                                       (ℚP.≃-sym (ℚP.p≥q⇒p⊓q≃q z₂ₘ≤y₂ₘ)) ⟩
          seq (y ⊓ z) (2 ℕ.* m) ℚ.- seq x (2 ℕ.* m)  ∎

-- Extra properties

@0 x≄0⇒-x≄0 : ∀ x -> x ≄0 -> (- x) ≄0
x≄0⇒-x≄0 x (Left x<0) = Right (posCong (zeroℝ - x) (negate x - zeroℝ) (≃-trans (+-comm zeroℝ (- x)) (+-congʳ (- x) 0≃-0)) x<0)
x≄0⇒-x≄0 x (Right 0<x) = Left (posCong (x - zeroℝ) (zeroℝ - negate x) (≃-trans (≃-trans (+-comm x (- zeroℝ)) (+-congˡ x (≃-sym 0≃-0))) (+-congʳ zeroℝ (≃-sym (neg-involutive x)))) 0<x)

@0 lemma-2-14 : ∀ x -> ∀ (n : ℕ) -> {n≢0 : n ≢0} -> ∣ x - (seq x n) ⋆ ∣ ≤ ((+ 1 / n) {n≢0}) ⋆
lemma-2-14 x (suc k₁) = nonNeg* (λ @0 {(suc k₂) -> let n = suc k₁; m = suc k₂; x₄ₘ = seq x (2 ℕ.* (2 ℕ.* m)); xₙ = seq x n in begin
  ℚ.- (+ 1 / m)                                     <⟨ ℚP.neg-mono-< (q<r⇒+p/r<+p/q 1 m (2 ℕ.* (2 ℕ.* m))
                                                                     (ℕP.<-trans (m<n*m ℕP.0<1+n ℕP.≤-refl)
                                                                                 (m<n*m ℕP.0<1+n ℕP.≤-refl))) ⟩
  ℚ.- (+ 1 / (2 ℕ.* (2 ℕ.* m)))                     ≈⟨ solve 2 (λ 4m n -> (⊝ 4m) ⊜ (n ⊖ (4m ⊕ n))) ℚP.≃-refl (+ 1 / (2 ℕ.* (2 ℕ.* m))) (+ 1 / n) ⟩
  + 1 / n ℚ.- (+ 1 / (2 ℕ.* (2 ℕ.* m)) ℚ.+ + 1 / n) ≤⟨ ℚP.+-monoʳ-≤ (+ 1 / n) (ℚP.neg-mono-≤ (reg x (2 ℕ.* (2 ℕ.* m)) n)) ⟩
  + 1 / n ℚ.- ℚ.∣ x₄ₘ ℚ.- xₙ ∣                       ∎})
  where
    open ℚP.≤-Reasoning
    open ℚ-Solver

@0 ∣x∣≃x⊔-x : ∀ x -> ∣ x ∣ ≃ x ⊔ (- x)
∣x∣≃x⊔-x x = *≃* λ {(suc k₁) -> let n = suc k₁ in begin
  ℚ.∣ ℚ.∣ seq x n ∣ ℚ.- (seq x n ℚ.⊔ ℚ.- seq x n) ∣ ≈⟨ ℚP.∣-∣-cong (ℚP.+-congʳ ℚ.∣ seq x n ∣
                                                       (ℚP.-‿cong (ℚP.≃-sym (∣p∣≃p⊔-p (seq x n))))) ⟩
  ℚ.∣ ℚ.∣ seq x n ∣ ℚ.- ℚ.∣ seq x n ∣ ∣             ≈⟨ ℚP.∣-∣-cong (ℚP.+-inverseʳ ℚ.∣ seq x n ∣) ⟩
  (+ 0 / 1)                                              ≤⟨ ℚP.nonNegative⁻¹ _ ⟩
  + 2 / n                                           ∎}
  where
    open ℚP.≤-Reasoning

negyLtxLtyThenAbsxLty : ∀ x y -> (negate y < x) Tuple.× (x < y) -> abs x < y
negyLtxLtyThenAbsxLty x y negyLtxLty = ltRespLEq y (x ⊔ negate x) (abs x) (≃-sym (∣x∣≃x⊔-x x))
                              (xLtzAndyLtzThenMaxxyLtz x (negate x) y
                                 (Tuple.snd negyLtxLty)
                                 (ltRespREq (negate x) (negate (negate y)) y (neg-involutive y) (negMonoLt (negate y) x (Tuple.fst negyLtxLty))))
  {-∣ x ∣     ≈⟨ ∣x∣≃x⊔-x x ⟩
  x ⊔ (- x) <⟨ xLtzAndyLtzThenMaxxyLtz x (- x) y
               (proj₂ -y<x<y)
               (<-respʳ-≃0 (neg-involutive y) (negMonoLt (proj₁ -y<x<y))) ⟩
  y          ∎-}
{-# COMPILE AGDA2HS negyLtxLtyThenAbsxLty #-}

@0 regular-n≤m : (x : ℕ -> ℚᵘ) ->
                   (∀ (m n : ℕ) -> {m≢0 : m ≢0} -> {n≢0 : n ≢0} -> m ℕ.≥ n -> ℚ.∣ x m ℚ.- x n ∣ ℚ.≤ (+ 1 / m) {m≢0} ℚ.+ (+ 1 / n) {n≢0}) ->
                   ∀ (m n : ℕ) -> {m≢0 : m ≢0} -> {n≢0 : n ≢0} -> ℚ.∣ x m ℚ.- x n ∣ ℚ.≤ (+ 1 / m) {m≢0} ℚ.+ (+ 1 / n) {n≢0}
regular-n≤m x hyp (suc m-1) (suc n-1) = [ left , right ]′ (ℕP.≤-total m n)
  where
    open ℚP.≤-Reasoning
    m = suc m-1
    n = suc n-1

    left : m ℕ.≤ n -> ℚ.∣ x m ℚ.- x n ∣ ℚ.≤ (+ 1 / m) ℚ.+ (+ 1 / n)
    left m≤n = begin
      ℚ.∣ x m ℚ.- x n ∣   ≈⟨ ∣p-q∣≃∣q-p∣ (x m) (x n) ⟩
      ℚ.∣ x n ℚ.- x m ∣   ≤⟨ hyp n m m≤n ⟩
      + 1 / n ℚ.+ + 1 / m ≈⟨ ℚP.+-comm (+ 1 / n) (+ 1 / m) ⟩
      + 1 / m ℚ.+ + 1 / n  ∎

    right : n ℕ.≤ m -> ℚ.∣ x m ℚ.- x n ∣ ℚ.≤ (+ 1 / m) ℚ.+ (+ 1 / n)
    right n≤m = hyp m n n≤m

@0 p⋆≤q⋆⇒p≤q : ∀ p q -> p ⋆ ≤ q ⋆ -> p ℚ.≤ q
p⋆≤q⋆⇒p≤q p q (nonNeg* hyp) = p-q≤j⁻¹⇒p≤q (λ @0 {(suc j-1) -> let j = suc j-1 in
                      ℚP.≤-respˡ-≃ (solve 2 (λ p q -> (⊝ (q ⊖ p)) ⊜ (p ⊖ q)) ℚP.≃-refl p q)
                      (ℚP.≤-respʳ-≃ (ℚP.neg-involutive (+ 1 / j)) (ℚP.neg-mono-≤ (hyp j)))})
  where open ℚ-Solver

@0 p≤q⇒p⋆≤q⋆ : ∀ p q -> p ℚ.≤ q -> p ⋆ ≤ q ⋆
p≤q⇒p⋆≤q⋆ p q p≤q = nonNeg* (λ @0 {(suc n-1) -> let n = suc n-1 in begin
  ℚ.- (+ 1 / n) <⟨ ℚP.negative⁻¹ _ ⟩
  (+ 0 / 1)           ≤⟨ ℚP.p≤q⇒0≤q-p p≤q ⟩
  q ℚ.- p        ∎})
  where open ℚP.≤-Reasoning

@0 x≤Kx : ∀ x -> x ≤ (+ fK x / 1) ⋆
x≤Kx x = nonNeg* (λ @0 {(suc n-1) -> let n = suc n-1 in begin
  ℚ.- (+ 1 / n)                       <⟨ ℚP.negative⁻¹ _ ⟩
  (+ 0 / 1)                                 <⟨ p<q⇒0<q-p ℚ.∣ seq x (2 ℕ.* n) ∣ (+ fK x / 1)
                                         (canonical-strict-upper-bound x (2 ℕ.* n)) ⟩
  + fK x / 1 ℚ.- ℚ.∣ seq x (2 ℕ.* n) ∣ ≤⟨ ℚP.+-monoʳ-≤ (+ fK x / 1) (
                                         ℚP.neg-mono-≤ (p≤∣p∣ (seq x (2 ℕ.* n)))) ⟩
  + fK x / 1 ℚ.- seq x (2 ℕ.* n)        ∎})
  where open ℚP.≤-Reasoning

@0 *-mono-≤ : ∀ {x y z w} -> NonNegative x -> NonNegative z -> x ≤ y -> z ≤ w -> x * z ≤ y * w
*-mono-≤ {x} {y} {z} {w} nonx nonz x≤y z≤w = begin
  x * z ≤⟨ *-monoˡ-≤-nonNeg z≤w nonx ⟩
  x * w ≤⟨ *-monoʳ-≤-nonNeg x≤y (0≤x⇒nonNegx (≤-trans (nonNegx⇒0≤x nonz) z≤w)) ⟩
  y * w  ∎
  where open ≤-Reasoning

-- The Archimedean property
archimedeanℝ : ∀ (x : ℝ) -> Σ0 ℕ λ (n-1 : ℕ) -> (+ (suc n-1) / 1) ⋆ > x
archimedeanℝ x = fK x :&: (begin-strict
    x                     <⟨ ltRespLEq (oneℝ + x) _ x (+-identityˡ x)
                             (+-monoˡ-< x (pLtqThenToRealpLtToRealq (+ 0 / 1) (+ 1 / 1) (ℚ.*<* (ℤ.+<+ ℕP.0<1+n)))) ⟩
    oneℝ + x                ≤⟨ +-monoʳ-≤ oneℝ (x≤Kx x) ⟩
    oneℝ + (+ fK x / 1) ⋆    ≈⟨ ≃-trans
                             (≃-sym (⋆-distrib-+ (+ 1 / 1) (+ fK x / 1)))
                             (⋆-cong (ℚP.≃-reflexive (ℚP./-cong (cong (λ r -> + 1 ℤ.+ r)
                             (ℤP.*-identityʳ (+ fK x))) refl _ _))) ⟩
    (+ (suc (fK x)) / 1) ⋆  ∎)
  where open ≤-Reasoning
{-# COMPILE AGDA2HS archimedeanℝ #-}

abstract
  fastArchimedeanℝ : ∀ x -> Σ0 ℕ λ (n-1 : ℕ) -> (+ (suc n-1) / 1) ⋆ > x
  fastArchimedeanℝ = archimedeanℝ
  {-# COMPILE AGDA2HS fastArchimedeanℝ #-}

-- Density of ℚ in ℝ and corollaries

densityOfℚ : ∀ x y -> x < y -> Σ' ℚᵘ (λ (@0 α : ℚᵘ) -> (x < toReal α) Tuple.× (toReal α < y))
densityOfℚ x y (MkPos (nM1 :&: y₂ₙ-x₂ₙ>n⁻¹)) = α :^: (zeroLtxMinusxThenxLty x (toReal α)
                                                   (ltLe0Trans zeroℝ ((toReal (+ 1 / 2 ℚ.* (y₂ₙ ℚ.- x₂ₙ))) - (toReal (+ 1 / (2 ℕ.* n)))) (toReal α - x) lemA (begin
             (+ 1 / 2 ℚ.* (y₂ₙ ℚ.- x₂ₙ)) ⋆ - ((+ 1 / (2 ℕ.* n)) ⋆)       ≤⟨ +-monoʳ-≤ ((+ 1 / 2 ℚ.* (y₂ₙ ℚ.- x₂ₙ)) ⋆) (neg-mono-≤ (lemma-2-14 x (2 ℕ.* n))) ⟩
             (+ 1 / 2 ℚ.* (y₂ₙ ℚ.- x₂ₙ)) ⋆ - ∣ x - (x₂ₙ ⋆) ∣             ≈⟨ +-congˡ (- ∣ x - x₂ₙ ⋆ ∣) (⋆-cong (lemB y₂ₙ x₂ₙ)) ⟩
             (((+ 1 / 2) ℚ.* (x₂ₙ ℚ.+ y₂ₙ) ℚ.- x₂ₙ) ⋆) - ∣ x - (x₂ₙ ⋆) ∣ ≈⟨ +-congˡ (- ∣ x - x₂ₙ ⋆ ∣) (⋆-distrib-to-p⋆-q⋆ α x₂ₙ) ⟩
             (α ⋆) - (x₂ₙ ⋆) - ∣ x - (x₂ₙ ⋆) ∣                           ≤⟨ +-monoʳ-≤ (α ⋆ - (x₂ₙ ⋆)) (neg-mono-≤ x≤∣x∣) ⟩
             (α ⋆) - (x₂ₙ ⋆) - (x - (x₂ₙ ⋆))                             ≈⟨ +-assoc (α ⋆) (- (x₂ₙ ⋆)) (- (x - (x₂ₙ ⋆))) ⟩
             α ⋆ + (- (x₂ₙ ⋆) - (x - x₂ₙ ⋆))                             ≈⟨ +-congʳ (α ⋆) (≃-trans (≃-sym (neg-distrib-+ (x₂ₙ ⋆) (x - x₂ₙ ⋆)))
                                                                                                   (-‿cong (helper x (x₂ₙ ⋆)))) ⟩
             (α ⋆) - x                                                    ∎))  Tuple.,
  zeroLtxMinusxThenxLty (toReal α) y (ltLe0Trans zeroℝ (toReal (+ 1 / 2 ℚ.* (y₂ₙ ℚ.- x₂ₙ)) - (toReal (+ 1 / (2 ℕ.* n)))) (y - toReal α) lemA (begin
            (+ 1 / 2 ℚ.* (y₂ₙ ℚ.- x₂ₙ)) ⋆ - ((+ 1 / (2 ℕ.* n)) ⋆)       ≤⟨ +-monoʳ-≤ ((+ 1 / 2 ℚ.* (y₂ₙ ℚ.- x₂ₙ)) ⋆) (neg-mono-≤ (lemma-2-14 y (2 ℕ.* n))) ⟩
            (+ 1 / 2 ℚ.* (y₂ₙ ℚ.- x₂ₙ)) ⋆ - ∣ y - y₂ₙ ⋆ ∣               ≤⟨ +-monoʳ-≤ ((+ 1 / 2 ℚ.* (y₂ₙ ℚ.- x₂ₙ)) ⋆)
                                                                           (neg-mono-≤ (≤-respʳ-≃ (∣x-y∣≃∣y-x∣ (y₂ₙ ⋆) y) x≤∣x∣)) ⟩
            (+ 1 / 2 ℚ.* (y₂ₙ ℚ.- x₂ₙ)) ⋆ - (y₂ₙ ⋆ - y)                 ≈⟨ +-congʳ ((+ 1 / 2 ℚ.* (y₂ₙ ℚ.- x₂ₙ)) ⋆) (neg-distrib-+ (y₂ₙ ⋆) (- y)) ⟩
            (+ 1 / 2 ℚ.* (y₂ₙ ℚ.- x₂ₙ)) ⋆ + (- (y₂ₙ ⋆) - (- y))         ≈⟨ ≃-trans
                                                                           (≃-sym (+-assoc ((+ 1 / 2 ℚ.* (y₂ₙ ℚ.- x₂ₙ)) ⋆) (- (y₂ₙ ⋆)) (- (- y))))
                                                                           (+-congˡ (- (- y)) (≃-sym (⋆-distrib-to-p⋆-q⋆ (+ 1 / 2 ℚ.* (y₂ₙ ℚ.- x₂ₙ)) y₂ₙ))) ⟩
            (+ 1 / 2 ℚ.* (y₂ₙ ℚ.- x₂ₙ) ℚ.- y₂ₙ) ⋆ - (- y)               ≈⟨ +-cong (⋆-cong (lemC y₂ₙ x₂ₙ)) (neg-involutive y) ⟩
            (ℚ.- α) ⋆ + y                                               ≈⟨ ≃-trans (+-comm ((ℚ.- α) ⋆) y) (+-congʳ y (⋆-distrib-neg α)) ⟩
            y - α ⋆                                                      ∎

  )))
  where
    open ≤-Reasoning
    open ℤ-Solver
    n = suc nM1
    x₂ₙ = seq x (2 ℕ.* n)
    y₂ₙ = seq y (2 ℕ.* n)
    α = (+ 1 / 2) ℚ.* (x₂ₙ ℚ.+ y₂ₙ)
    
    lemA : zeroℝ < toReal (+ 1 / 2 ℚ.* (y₂ₙ ℚ.- x₂ₙ)) - toReal (+ 1 / (2 ℕ.* n))
    lemA = ltRespLEq
             (toReal (+ 1 / 2 ℚ.* (y₂ₙ ℚ.- x₂ₙ)) - toReal (+ 1 / (2 ℕ.* n)))
             (toReal (+ 1 / (2 ℕ.* n) ℚ.- (+ 1 / (2 ℕ.* n))))
             zeroℝ
             (≃-sym (⋆-cong (ℚP.≃-sym (ℚP.+-inverseʳ (+ 1 / (2 ℕ.* n))))))
             (ltRespREq
                (toReal (+ 1 / (2 ℕ.* n) ℚ.- (+ 1 / (2 ℕ.* n))))
                (toReal (+ 1 / 2 ℚ.* (y₂ₙ ℚ.- x₂ₙ) ℚ.- (+ 1 / (2 ℕ.* n))))
                (toReal (+ 1 / 2 ℚ.* (y₂ₙ ℚ.- x₂ₙ)) - toReal (+ 1 / (2 ℕ.* n)))
                (⋆-distrib-to-p⋆-q⋆ (+ 1 / 2 ℚ.* (y₂ₙ ℚ.- x₂ₙ)) (+ 1 / (2 ℕ.* n)))
                (pLtqThenToRealpLtToRealq
                      (+ 1 / (2 ℕ.* n) ℚ.- (+ 1 / (2 ℕ.* n)))
                      (+ 1 / 2 ℚ.* (y₂ₙ ℚ.- x₂ₙ) ℚ.- (+ 1 / (2 ℕ.* n)))
                      (ℚP.+-monoˡ-< (ℚ.- (+ 1 / (2 ℕ.* n)))
                    (ℚP.*-monoʳ-<-pos {+ 1 / 2} _ y₂ₙ-x₂ₙ>n⁻¹))))
      {- -- Reasoning cannot be used yet for <; at least not for code we want to compile
      begin-strict
      zeroℝ                                                          ≈⟨ ⋆-cong (ℚP.≃-sym (ℚP.+-inverseʳ (+ 1 / (2 ℕ.* n)))) ⟩
      toReal (+ 1 / (2 ℕ.* n) ℚ.- (+ 1 / (2 ℕ.* n)))                <⟨ pLtqThenToRealpLtToRealq
                                                                     (+ 1 / (2 ℕ.* n) ℚ.- (+ 1 / (2 ℕ.* n)))
                                                                     (+ 1 / 2 ℚ.* (y₂ₙ ℚ.- x₂ₙ) ℚ.- (+ 1 / (2 ℕ.* n)))
                                                                     (ℚP.+-monoˡ-< (ℚ.- (+ 1 / (2 ℕ.* n)))
                                                                   (ℚP.*-monoʳ-<-pos {+ 1 / 2} _ y₂ₙ-x₂ₙ>n⁻¹)) ⟩
      toReal (+ 1 / 2 ℚ.* (y₂ₙ ℚ.- x₂ₙ) ℚ.- (+ 1 / (2 ℕ.* n)))      ≈⟨ ⋆-distrib-to-p⋆-q⋆ (+ 1 / 2 ℚ.* (y₂ₙ ℚ.- x₂ₙ)) (+ 1 / (2 ℕ.* n)) ⟩
      toReal (+ 1 / 2 ℚ.* (y₂ₙ ℚ.- x₂ₙ)) - toReal (+ 1 / (2 ℕ.* n)) ∎
      -}

    @0 helper : ∀ x y -> y + (x - y) ≃ x
    helper x y = begin-equality
      y + (x - y)   ≈⟨ +-congʳ y (+-comm x (- y)) ⟩
      y + (- y + x) ≈⟨ ≃-sym (+-assoc y (- y) x) ⟩
      (y - y) + x   ≈⟨ +-congˡ x (+-inverseʳ y) ⟩
      zeroℝ + x        ≈⟨ +-identityˡ x ⟩
      x              ∎

    @0 lemB : ∀ p q -> + 1 / 2 ℚ.* (p ℚ.- q) ℚ.≃ + 1 / 2 ℚ.* (q ℚ.+ p) ℚ.- q
    lemB p/q u/v = let p = ↥ p/q; q = ↧ p/q; u = ↥ u/v; v = ↧ u/v in
                   ℚ.*≡* (solve 4 (λ p q u v ->
                   (Κ (+ 1) ⊗ (p ⊗ v ⊕ (⊝ u) ⊗ q)) ⊗ (Κ (+ 2) ⊗ (v ⊗ q) ⊗ v) ⊜
                   ((Κ (+ 1) ⊗ (u ⊗ q ⊕ p ⊗ v)) ⊗ v ⊕ (⊝ u) ⊗ (Κ (+ 2) ⊗ (v ⊗ q))) ⊗ (Κ (+ 2) ⊗ (q ⊗ v)))
                   refl p q u v)

    @0 lemC : ∀ p q -> + 1 / 2 ℚ.* (p ℚ.- q) ℚ.- p ℚ.≃ ℚ.- (+ 1 / 2 ℚ.* (q ℚ.+ p))
    lemC p/q u/v = let p = ↥ p/q; q = ↧ p/q; u = ↥ u/v; v = ↧ u/v in
                   ℚ.*≡* (solve 4 (λ p q u v ->
                   ((Κ (+ 1) ⊗ (p ⊗ v ⊕ (⊝ u) ⊗ q)) ⊗ q ⊕ (⊝ p) ⊗ (Κ (+ 2) ⊗ (q ⊗ v))) ⊗ (Κ (+ 2) ⊗ (v ⊗ q)) ⊜
                   (⊝ (Κ (+ 1) ⊗ (u ⊗ q ⊕ p ⊗ v))) ⊗ ((Κ (+ 2) ⊗ (q ⊗ v)) ⊗ q))
                   refl p q u v)
{-# COMPILE AGDA2HS densityOfℚ #-}

abstract
  fastDensityOfℚ : ∀ x y -> x < y -> Σ' ℚᵘ (λ (@0 α : ℚᵘ) -> (x < toReal α) Tuple.× (toReal α < y))
  fastDensityOfℚ = densityOfℚ
{-# COMPILE AGDA2HS fastDensityOfℚ  #-}

@0 corollary-2-15 : ∀ (x r : ℝ) -> Positive r -> ∃0 λ (α : ℚᵘ) -> ∣ x - α ⋆ ∣ < r
corollary-2-15 x r posr = α :&: <-respˡ-≃ (∣x-y∣≃∣y-x∣ (α ⋆) x) (negyLtxLtyThenAbsxLty (α ⋆ - x) r (-r<α-x Tuple., α-x<r))
  where
    open ℝ-Solver
    open ≤-Reasoning
    -r+x<r+x : - r + x < r + x
    -r+x<r+x = +-monoˡ-< x (begin-strict
      - r   <⟨ negMonoLt zeroℝ r (posxThenZeroLtx r posr) ⟩
      - zeroℝ  ≈⟨ ≃-sym 0≃-0 ⟩
      zeroℝ    <⟨ posxThenZeroLtx r posr ⟩
      r      ∎)

    αp : Σ' ℚᵘ (λ (@0 α : ℚᵘ) -> ((- r + x) < toReal α) Tuple.× (toReal α < (r + x)))
    αp = fastDensityOfℚ (- r + x) (r + x) -r+x<r+x
    α = proj₁ αp

    -r<α-x : - r < α ⋆ - x
    -r<α-x = begin-strict
      - r           ≈⟨ solve 2 (λ r x -> (⊝ r) ⊜ (⊝ r ⊕ x ⊖ x)) ≃-refl r x ⟩
      - r + x - x   <⟨ +-monoˡ-< (- x) (Tuple.fst (proj₂ αp)) ⟩
      α ⋆ - x        ∎

    α-x<r : α ⋆ - x < r
    α-x<r = begin-strict
      α ⋆ - x     <⟨ +-monoˡ-< (- x) (Tuple.snd (proj₂ αp)) ⟩
      r + x - x   ≈⟨ solve 2 (λ r x -> (r ⊕ x ⊖ x) ⊜ r) ≃-refl r x ⟩
      r            ∎

abstract
  @0 fast-corollary-2-15 : ∀ (x r : ℝ) -> Positive r -> ∃0 λ (α : ℚᵘ) -> ∣ x - α ⋆ ∣ < r
  fast-corollary-2-15 = corollary-2-15

-- Properties of summations

@0 sum-distrib-+ : ∀ (xs ys : ℕ -> ℝ) -> ∀ i n ->
              sum (λ k -> xs k + ys k) i n ≃ sum xs i n + sum ys i n
sum-distrib-+ xs ys 0 n = lem n
  where
    open ≃-Reasoning
    open ℝ-Solver
    {-
      If you just case split on n in sum-distrib-+ and don't use this lemma, Agda's termination checker gives an error
      for the (suc i) n case when the induction hypothesis is used.
    -}
    lem : ∀ n -> sum0 (λ k -> xs k + ys k) n ≃ sum0 xs n + sum0 ys n
    lem 0 = ≃-reflexive (λ @0 {(suc n-1) -> ℚP.≃-refl})
    lem (suc n) = begin
      sum0 (λ k -> xs k + ys k) n + (xs n + ys n) ≈⟨ +-congˡ (xs n + ys n) (lem n) ⟩
      sum0 xs n + sum0 ys n + (xs n + ys n)         ≈⟨ solve 4 (λ a b c d -> (a ⊕ c ⊕ (b ⊕ d)) ⊜ (a ⊕ b ⊕ (c ⊕ d)))
                                                   ≃-refl (sum0 xs n) (xs n) (sum0 ys n) (ys n) ⟩
      sum0 xs n + xs n + (sum0 ys n + ys n)          ∎
sum-distrib-+ xs ys (suc i) n = begin
  sum0 (λ k -> xs k + ys k) n -
  (sum0 (λ k -> xs k + ys k) i + (xs i + ys i))                 ≈⟨ +-cong
                                                                 (sum-distrib-+ xs ys 0 n)
                                                                 (-‿cong (+-congˡ (xs i + ys i) (sum-distrib-+ xs ys 0 i))) ⟩
  sum0 xs n + sum0 ys n - (sum0 xs i + sum0 ys i + (xs i + ys i))     ≈⟨ solve 6 (λ a b c d e f ->
                                                                 (a ⊕ b ⊖ (c ⊕ d ⊕ (e ⊕ f))) ⊜ (a ⊖ (c ⊕ e) ⊕ (b ⊖ (d ⊕ f))))
                                                                 ≃-refl (sum0 xs n) (sum0 ys n) (sum0 xs i) (sum0 ys i) (xs i) (ys i) ⟩
  sum0 xs n - (sum0 xs i + xs i) + (sum0 ys n - (sum0 ys i + ys i))    ∎
  where
    open ≃-Reasoning
    open ℝ-Solver

@0 neg-distrib-sum : ∀ xs -> ∀ i n -> - sum xs i n ≃ sum (λ j -> - xs j) i n
neg-distrib-sum xs 0 n = lem n
  where
    open ≃-Reasoning
    lem : ∀ n -> - sum0 xs n ≃ sum0 (λ j -> - xs j) n
    lem 0 = ≃-sym 0≃-0
    lem (suc n) = begin
      - (sum0 xs n + xs n)          ≈⟨ neg-distrib-+ (sum0 xs n) (xs n) ⟩
      - sum0 xs n - xs n            ≈⟨ +-congˡ (- xs n) (lem n) ⟩
      sum0 (λ j -> - xs j) n - xs n  ∎
neg-distrib-sum xs (suc i) n = begin
  - (sum0 xs n - (sum0 xs i + xs i))                       ≈⟨ neg-distrib-+ (sum0 xs n) (- (sum0 xs i + xs i)) ⟩
  - sum0 xs n - (- (sum0 xs i + xs i))                     ≈⟨ +-cong
                                                          (neg-distrib-sum xs 0 n)
                                                          (-‿cong (≃-trans
                                                                  (neg-distrib-+ (sum0 xs i) (xs i))
                                                                  (+-congˡ (- xs i) (neg-distrib-sum xs 0 i)))) ⟩
  sum0 (λ j -> - xs j) n - (sum0 (λ j -> - xs j) i - xs i)  ∎
  where open ≃-Reasoning
 
@0 x+y>0⇒x>0∨y>0 : ∀ x y -> x + y > zeroℝ -> Either (x > zeroℝ) (y > zeroℝ)
x+y>0⇒x>0∨y>0 x y x+y>0 = [ (λ hyp -> Left (lem x X (proj₂ X-generator) (ℚP.<-respˡ-≃ 2⁻¹*2⁻¹α≃4⁻¹α hyp))) ,
                            (λ hyp -> Right (lem y Y (proj₂ Y-generator) (ℚP.<-respˡ-≃ 2⁻¹*2⁻¹α≃4⁻¹α hyp))) ]′
                            (p+q>r⇒p>2⁻¹r∨q>2⁻¹r X Y ((+ 1 / 2) ℚ.* α) ax+ay>α/4)
  where
    open ℝ-Solver
    open ℤ-Solver using ()
      renaming
        ( solve to ℤsolve
        ; _⊕_   to _:+_
        ; _⊗_   to _:*_
        ; ⊝_    to :-_
        ; _⊜_   to _:=_
        ; Κ     to κ
        )
    α-generator = fastDensityOfℚ zeroℝ (x + y) x+y>0
    α = proj₁ α-generator

    pos4⁻¹α : Positive (((+ 1 / 4) ℚ.* α) ⋆)
    pos4⁻¹α = pospThenPosToRealp ((+ 1 / 4) ℚ.* α) (ℚ.positive (begin-strict
      (+ 0 / 1)               ≈⟨ ℚP.≃-sym (ℚP.*-zeroʳ (+ 1 / 4)) ⟩
      (+ 1 / 4) ℚ.* (+ 0 / 1) <⟨ ℚP.*-monoʳ-<-pos {+ 1 / 4} _ (p⋆<q⋆⇒p<q (+ 0 / 1) α (Tuple.fst (proj₂ α-generator))) ⟩
      (+ 1 / 4) ℚ.* α    ∎))
      where open ℚP.≤-Reasoning

    X-generator = fast-corollary-2-15 x (((+ 1 / 4) ℚ.* α) ⋆) pos4⁻¹α
    X = proj₁ X-generator
    Y-generator = fast-corollary-2-15 y (((+ 1 / 4) ℚ.* α) ⋆) pos4⁻¹α
    Y = proj₁ Y-generator

    2⁻¹*2⁻¹α≃4⁻¹α : (+ 1 / 2) ℚ.* ((+ 1 / 2) ℚ.* α) ℚ.≃ (+ 1 / 4) ℚ.* α
    2⁻¹*2⁻¹α≃4⁻¹α = ℚ.*≡* (ℤsolve 2 (λ p q ->
                    κ (+ 1) :* (κ (+ 1) :* p) :* (κ (+ 4) :* q) := (κ (+ 1) :* p :* (κ (+ 2) :* (κ (+ 2) :* q))))
                    refl (↥ α) (↧ α))

    ax+ay>α/4 : X ℚ.+ Y ℚ.> (+ 1 / 2) ℚ.* α
    ax+ay>α/4 = p⋆<q⋆⇒p<q ((+ 1 / 2) ℚ.* α) (X ℚ.+ Y) (begin-strict
      ((+ 1 / 2) ℚ.* α) ⋆                             ≈⟨ ⋆-cong (ℚ.*≡* (ℤsolve 2 (λ p q ->
                                                         (κ (+ 1) :* p) :* ((q :* (κ (+ 4) :* q)) :* (κ (+ 4) :* q)) :=
                                                         ((p :* (κ (+ 4) :* q) :+ (:- (κ (+ 1) :* p)) :* q) :* (κ (+ 4) :* q) :+ (:- (κ (+ 1) :* p)) :*
                                                         (q :* (κ (+ 4) :* q))) :* (κ (+ 2) :* q))
                                                         refl (↥ α) (↧ α))) ⟩
      (α ℚ.- (+ 1 / 4) ℚ.* α ℚ.- (+ 1 / 4) ℚ.* α) ⋆   ≈⟨ ≃-trans
                                                         (⋆-distrib-to-p⋆-q⋆ (α ℚ.- (+ 1 / 4) ℚ.* α) ((+ 1 / 4) ℚ.* α))
                                                         (+-congˡ (- ((+ 1 / 4 ℚ.* α) ⋆)) (⋆-distrib-to-p⋆-q⋆ α ((+ 1 / 4) ℚ.* α))) ⟩
      α ⋆ - ((+ 1 / 4) ℚ.* α) ⋆ - ((+ 1 / 4) ℚ.* α) ⋆ <⟨ +-mono-<
                                                         (+-mono-< (Tuple.snd (proj₂ α-generator)) (negMonoLt _ _ (proj₂ X-generator)))
                                                         (negMonoLt _ _ (proj₂ Y-generator)) ⟩
      (x + y) - ∣ x - X ⋆ ∣ - ∣ y - Y ⋆ ∣              ≤⟨ +-mono-≤ (+-monoʳ-≤ (x + y) (neg-mono-≤ x≤∣x∣)) (neg-mono-≤ x≤∣x∣) ⟩
      (x + y) - (x - X ⋆) - (y - Y ⋆)                 ≈⟨ +-cong (+-congʳ (x + y) (neg-distrib-+ x (- (X ⋆)))) (neg-distrib-+ y (- (Y ⋆))) ⟩
      (x + y) + (- x - (- (X ⋆))) + (- y - (- (Y ⋆))) ≈⟨ solve 4 (λ x y X Y ->
                                                         ((x ⊕ y) ⊕ (⊝ x ⊖ (⊝ X)) ⊕ (⊝ y ⊖ (⊝ Y))) ⊜ (X ⊕ Y))
                                                         ≃-refl x y (X ⋆) (Y ⋆) ⟩
      X ⋆ + Y ⋆                                       ≈⟨ ≃-sym (⋆-distrib-+ X Y) ⟩
      (X ℚ.+ Y) ⋆                                      ∎)
      where open ≤-Reasoning

    lem : ∀ (z : ℝ) -> (Z : ℚᵘ) -> ∣ z - Z ⋆ ∣ < ((+ 1 / 4) ℚ.* α) ⋆ -> Z ℚ.> (+ 1 / 4) ℚ.* α -> z > zeroℝ
    lem z Z ∣z-Z∣<4⁻¹α Z>4⁻¹α = begin-strict
      zeroℝ                                        ≈⟨ ≃-sym (+-inverseʳ (((+ 1 / 4) ℚ.* α) ⋆)) ⟩
      ((+ 1 / 4) ℚ.* α) ⋆ - ((+ 1 / 4) ℚ.* α) ⋆ <⟨ +-mono-< (pLtqThenToRealpLtToRealq ((+ 1 / 4) ℚ.* α) Z Z>4⁻¹α) (negMonoLt (∣ z - Z ⋆ ∣) (((+ 1 / 4) ℚ.* α) ⋆) ∣z-Z∣<4⁻¹α) ⟩
      Z ⋆ - ∣ z - Z ⋆ ∣                         ≈⟨ +-congʳ (Z ⋆) (-‿cong (∣x-y∣≃∣y-x∣ z (Z ⋆))) ⟩
      Z ⋆ - ∣ Z ⋆ - z ∣                         ≤⟨ +-monoʳ-≤ (Z ⋆) (neg-mono-≤ x≤∣x∣) ⟩
      Z ⋆ - (Z ⋆ - z)                           ≈⟨ solve 2 (λ z Z -> (Z ⊖ (Z ⊖ z)) ⊜ z) ≃-refl z (Z ⋆) ⟩
      z                        ∎
      where open ≤-Reasoning

@0 proposition-2-16 : ∀ xs -> ∀ n -> @0 {n ≢0} -> sum0 xs n > zeroℝ -> ∃ λ j -> j ℕ.< n × xs j > zeroℝ
proposition-2-16 xs 1 sumxs>0 = 0 , ℕP.0<1+n , <-respʳ-≃ (+-identityˡ (xs 0)) sumxs>0
proposition-2-16 xs (suc (suc n-2)) sumxs>0 = either
                                                (λ hyp -> let fromhyp = proposition-2-16 xs (suc n-2) hyp ; n-1 = suc n-2 in
                                                      proj₁ fromhyp , ℕP.<-trans (proj₁ (proj₂ fromhyp)) (ℕP.n<1+n n-1) , proj₂ (proj₂ fromhyp))
                                                (λ hyp -> let n-1 = suc n-2 in n-1 , ℕP.n<1+n n-1 , hyp)
                                                (x+y>0⇒x>0∨y>0 (sum0 xs (suc n-2)) (xs (suc n-2)) sumxs>0)

@0 corollary-2-17 : ∀ x y z -> y < z -> Either (x < z) (x > y)
corollary-2-17 x y z y<z = either
                             (λ z-x>0 -> Left (zeroLtxMinusxThenxLty x z z-x>0))
                             (λ x-y>0 -> Right (zeroLtxMinusxThenxLty y x x-y>0))
                             (x+y>0⇒x>0∨y>0 (z - x) (x - y) (<-respʳ-≃ lem (xLtyThenZeroLtyMinusx y z y<z)))
  where
    open ℝ-Solver
    lem : z - y ≃ (z - x) + (x - y)
    lem = solve 3 (λ x y z -> (z ⊖ y) ⊜ ((z ⊖ x) ⊕ (x ⊖ y))) ≃-refl x y z

abstract
  @0 fast-corollary-2-17 : ∀ x y z -> y < z -> Either (x < z) (x > y)
  fast-corollary-2-17 = corollary-2-17

-- Properties of max, the maximum over a sequence function
@0 m≤n⇒maxfm≤maxfn : ∀ (f : ℕ -> ℝ) -> ∀ m n -> m ℕ.≤ n -> max f m ≤ max f n
m≤n⇒maxfm≤maxfn f m n m≤n with ≤⇒≡∨< m n m≤n
... | inj₁ refl = ≤-refl
m≤n⇒maxfm≤maxfn f m .(suc n) m≤1+n | inj₂ (ℕ.s≤s {n = n} m≤n) = ≤-trans (m≤n⇒maxfm≤maxfn f m n m≤n) (x≤x⊔y (max f n) (f (suc n)))

@0 m≤n⇒fm≤maxfn : ∀ (f : ℕ -> ℝ) -> ∀ m n -> m ℕ.≤ n -> f m ≤ max f n
m≤n⇒fm≤maxfn f zero n m≤n    = m≤n⇒maxfm≤maxfn f 0 n ℕ.z≤n
m≤n⇒fm≤maxfn f (suc m) n 1+m≤n = ≤-trans (lem (suc m)) (m≤n⇒maxfm≤maxfn f (suc m) n 1+m≤n)
  where
    lem : (k : ℕ) → f k ≤ max f k
    lem zero    = ≤-refl
    lem (suc k) = x≤y⊔x (f (suc k)) (max f k)

@0 <-irrefl : ∀ {x y : ℝ} -> x ≃ y → ¬ (x < y)
<-irrefl {x} {y} (*≃* x≃y) (MkPos (n-1 :&: x<y)) = let n = suc n-1 in ℚP.<-irrefl ℚP.≃-refl (begin-strict
  + 1 / n                                   <⟨ x<y ⟩
  seq y (2 ℕ.* n) ℚ.- seq x (2 ℕ.* n)       ≤⟨ p≤∣p∣ (seq y (2 ℕ.* n) ℚ.- seq x (2 ℕ.* n)) ⟩
  ℚ.∣ seq y (2 ℕ.* n) ℚ.- seq x (2 ℕ.* n) ∣ ≈⟨ ∣p-q∣≃∣q-p∣ (seq y (2 ℕ.* n)) (seq x (2 ℕ.* n)) ⟩
  ℚ.∣ seq x (2 ℕ.* n) ℚ.- seq y (2 ℕ.* n) ∣ ≤⟨ x≃y (2 ℕ.* n) ⟩
  + 2 / (2 ℕ.* n)                           ≈⟨ ℚ.*≡* (sym (ℤP.*-identityˡ (+ 2 ℤ.* + n))) ⟩
  + 1 / n                                    ∎)
  where open ℚP.≤-Reasoning

@0 p⋆≄0⇒∣↥p∣≢0 : ∀ p -> (p ⋆) ≄0 -> ℤ.∣ ↥ p ∣ ≢0
p⋆≄0⇒∣↥p∣≢0 (mkℚᵘ (+_ zero) d-1) (Left p⋆<0) = let d = suc d-1 in <-irrefl (≃-reflexive (λ {(suc n-1) -> ℚ.*≡* (sym (ℤP.*-zeroˡ (+ d)))})) p⋆<0
p⋆≄0⇒∣↥p∣≢0 (mkℚᵘ +[1+ n ] denominator-2) (Left p⋆<0) = _
p⋆≄0⇒∣↥p∣≢0 (mkℚᵘ (-[1+_] n) denominator-2) (Left p⋆<0) = _
p⋆≄0⇒∣↥p∣≢0 (mkℚᵘ (+_ zero) d-1) (Right 0<p⋆) = let d = suc d-1 in <-irrefl (≃-reflexive (λ {(suc n-1) -> ℚ.*≡* (ℤP.*-zeroˡ (+ d))})) 0<p⋆
p⋆≄0⇒∣↥p∣≢0 (mkℚᵘ +[1+ n ] denominator-2) (Right 0<p⋆) = _
p⋆≄0⇒∣↥p∣≢0 (mkℚᵘ (-[1+_] n) denominator-2) (Right 0<p⋆) = _

@0 ∣↥p∣≢0⇒p⋆≄0 : ∀ p -> ℤ.∣ ↥ p ∣ ≢0 -> (p ⋆) ≄0
∣↥p∣≢0⇒p⋆≄0 (mkℚᵘ +[1+ n ] d-1) ∣↥p∣≢0 = Right (pLtqThenToRealpLtToRealq (+ 0 / 1) (+[1+ n ] / (suc d-1)) (ℚP.positive⁻¹ _))
∣↥p∣≢0⇒p⋆≄0 (mkℚᵘ (-[1+_] n) d-1) ∣↥p∣≢0 = Left (pLtqThenToRealpLtToRealq (-[1+_] n / (suc d-1)) (+ 0 / 1) (ℚP.negative⁻¹ _))

@0 0≤y-x⇒x≤y : ∀ {x y} -> zeroℝ ≤ y - x -> x ≤ y
0≤y-x⇒x≤y {x} {y} 0≤y-x = nonNeg-cong (≃-trans (+-congʳ (y - x) (≃-sym 0≃-0)) (+-identityʳ (y - x))) 0≤y-x

@0 x≤z∧y≤z⇒x⊔y≤z : ∀ {x y z} -> x ≤ z -> y ≤ z -> x ⊔ y ≤ z
x≤z∧y≤z⇒x⊔y≤z {x} {y} {z} x≤z y≤z = lemma-2-8-2-onlyif lem
  where
    open ℚP.≤-Reasoning
    lem : ∀ n -> {@0 n≢0 : n ≢0} -> ∃0 λ Nₙ -> Nₙ ≢0 × (∀ m -> m ℕ.≥ Nₙ -> seq (z - (x ⊔ y)) m ℚ.≥ ℚ.- (+ 1 / n) {n≢0})
    lem (suc n-1) = N :&: _ , λ @0 {(suc m-1) m≥N -> let m = suc m-1 in
                  [ left m m≥N , right m m≥N ]′ (ℚP.≤-total (seq y (2 ℕ.* m)) (seq x (2 ℕ.* m)))}
      where
        n = suc n-1
        fromx≤z = fastLemma282If x≤z n
        fromy≤z = fastLemma282If y≤z n
        N₁ = proj₁ fromx≤z
        N₂ = proj₁ fromy≤z
        N = suc (N₁ ℕ.⊔ N₂)

        left : ∀ m -> m ℕ.≥ N -> seq y (2 ℕ.* m) ℚ.≤ seq x (2 ℕ.* m) ->
               seq (z - (x ⊔ y)) m ℚ.≥ ℚ.- (+ 1 / n)
        left (suc m-1) m≥N y₂ₘ≤x₂ₘ = let m = suc m-1 in begin
          ℚ.- (+ 1 / n)                             ≤⟨ proj₂ (proj₂ fromx≤z) m
                                                       (ℕP.≤-trans (ℕP.≤-trans (ℕP.m≤m⊔n N₁ N₂) (ℕP.n≤1+n (N₁ ℕ.⊔ N₂))) m≥N) ⟩
          seq z (2 ℕ.* m) ℚ.- seq x (2 ℕ.* m)       ≈⟨ ℚP.+-congʳ (seq z (2 ℕ.* m))
                                                       (ℚP.-‿cong (ℚP.≃-sym (ℚP.p≥q⇒p⊔q≃p y₂ₘ≤x₂ₘ))) ⟩
          seq z (2 ℕ.* m) ℚ.- seq (x ⊔ y) (2 ℕ.* m)  ∎

        right : ∀ m -> m ℕ.≥ N -> seq x (2 ℕ.* m) ℚ.≤ seq y (2 ℕ.* m) ->
               seq (z - (x ⊔ y)) m ℚ.≥ ℚ.- (+ 1 / n)
        right (suc m-1) m≥N x₂ₘ≤y₂ₘ = let m = suc m-1 in begin
          ℚ.- (+ 1 / n)                             ≤⟨ proj₂ (proj₂ fromy≤z) m
                                                       (ℕP.≤-trans (ℕP.≤-trans (ℕP.m≤n⊔m N₁ N₂) (ℕP.n≤1+n (N₁ ℕ.⊔ N₂))) m≥N) ⟩
          seq z (2 ℕ.* m) ℚ.- seq y (2 ℕ.* m)       ≈⟨ ℚP.+-congʳ (seq z (2 ℕ.* m))
                                                       (ℚP.-‿cong (ℚP.≃-sym (ℚP.p≤q⇒p⊔q≃q x₂ₘ≤y₂ₘ))) ⟩
          seq z (2 ℕ.* m) ℚ.- seq (x ⊔ y) (2 ℕ.* m)  ∎
