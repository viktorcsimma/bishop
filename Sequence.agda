-- Definitions regarding sequences and series

-- {-# OPTIONS --without-K --safe #-}

module Sequence where

{-# FOREIGN AGDA2HS {-# LANGUAGE TypeOperators #-} #-}

open import Agda.Builtin.Unit using (tt)
open import Algebra
open import Data.Bool.Base using (Bool; if_then_else_)
open import Function.Base using (_∘_)
open import Data.Integer.Base as ℤ
  using (ℤ; +_; +0; +[1+_]; -[1+_])
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
open import Data.List hiding (sum)
open import Function.Structures {_} {_} {_} {_} {ℕ} _≡_ {ℕ} _≡_

open import Agda.Builtin.Unit
open import Haskell.Prim.Num
import Haskell.Prim.Either as Either
import Haskell.Prim.Tuple as Tuple

open import ErasureProduct
open import ExtraProperties
open import Real
open import RealProperties
open import Inverse

{-
The solvers are used and renamed often enough to warrant them being opened up here
for the sake of consistency and cleanliness.
-}
open ℝ-Solver
open import NonReflectiveZ as ℤ-Solver using ()
  renaming
    ( solve to ℤsolve
    ; _⊕_   to _:+_
    ; _⊗_   to _:*_
    ; _⊖_   to _:-_
    ; ⊝_    to :-_
    ; _⊜_   to _:=_
    ; Κ     to ℤΚ
    )
open import NonReflectiveQ as ℚ-Solver using ()
  renaming
    ( solve to ℚsolve
    ; _⊕_   to _+:_
    ; _⊗_   to _*:_
    ; _⊖_   to _-:_
    ; ⊝_    to -:_
    ; _⊜_   to _=:_
    ; Κ     to ℚΚ
    )

-- We have to define it in a prefix way (I didn't want an operator for it).
data ConvergesTo : @0 (ℕ → ℝ) → @0 ℝ → Set where
  MkCon : {@0 f : ℕ -> ℝ} -> {@0 x₀ : ℝ} ->
              (∀ k -> {@0 k≢0 : k ≢0} -> Σ0 ℕ λ Nₖ-1 -> (∀ n -> n ℕ.≥ suc (Nₖ-1) -> abs (f n - x₀) ≤ toReal ((+ 1 / k) {k≢0}))) ->
          ConvergesTo f x₀
{-# COMPILE AGDA2HS ConvergesTo newtype #-}

IsConvergent : @0 (ℕ -> ℝ) -> Set
IsConvergent f = Σ' ℝ λ (@0 x₀) -> ConvergesTo f x₀ --in cauchyConvergenceTestIf, we need the existence proof too that is wrapped in MkCon
{-# COMPILE AGDA2HS IsConvergent #-}

{-
Useful for escaping the "metal" of the reals.
-}
@0 ∣x-y∣≤k⁻¹⇒x≃y : ∀ x y -> (∀ (k : ℕ) -> {k≢0 : k ≢0} -> ∣ x - y ∣ ≤ ((+ 1 / k) {k≢0}) ⋆) -> x ≃ y
∣x-y∣≤k⁻¹⇒x≃y x y hyp = *≃* λ @0 {(suc n-1) -> p≤q+j⁻¹⇒p≤q (λ @0 {(suc j-1) ->
                        let n = suc n-1; j = suc j-1; xₙ = seq x n; yₙ = seq y n in
                        p⋆≤q⋆⇒p≤q ℚ.∣ xₙ ℚ.- yₙ ∣ (+ 2 / n ℚ.+ + 1 / j) (begin
  ℚ.∣ xₙ ℚ.- yₙ ∣ ⋆                       ≈⟨ ≃-trans (∣p∣⋆≃∣p⋆∣ (xₙ ℚ.- yₙ)) (∣-∣-cong (⋆-distrib-to-p⋆-q⋆ xₙ yₙ)) ⟩
  ∣ xₙ ⋆ - yₙ ⋆ ∣                         ≈⟨ ∣-∣-cong (solve 4 (λ x y xₙ yₙ ->
                                             (xₙ ⊖ yₙ) ⊜ ((xₙ ⊖ x) ⊕ (y ⊖ yₙ) ⊕ (x ⊖ y)))
                                             ≃-refl x y (xₙ ⋆) (yₙ ⋆)) ⟩
  ∣ (xₙ ⋆ - x) + (y - yₙ ⋆) + (x - y) ∣   ≤⟨ ≤-trans
                                             (∣x+y∣≤∣x∣+∣y∣ ((xₙ ⋆ - x) + (y - yₙ ⋆)) (x - y))
                                             (+-monoˡ-≤ ∣ x - y ∣ (∣x+y∣≤∣x∣+∣y∣ (xₙ ⋆ - x) (y - yₙ ⋆))) ⟩
  ∣ xₙ ⋆ - x ∣ + ∣ y - yₙ ⋆ ∣ + ∣ x - y ∣  ≤⟨ +-mono-≤
                                              (+-mono-≤ (≤-respˡ-≃ (∣x-y∣≃∣y-x∣ x (xₙ ⋆)) (lemma-2-14 x n))
                                              (lemma-2-14 y n)) (hyp j) ⟩
  (+ 1 / n) ⋆ + (+ 1 / n) ⋆ + (+ 1 / j) ⋆ ≈⟨ solve 0
                                             ((Κ (+ 1 / n) ⊕ Κ (+ 1 / n) ⊕ Κ (+ 1 / j)) ⊜
                                             Κ (+ 1 / n ℚ.+ + 1 / n ℚ.+ + 1 / j))
                                             ≃-refl ⟩
  (+ 1 / n ℚ.+ + 1 / n ℚ.+ + 1 / j) ⋆     ≈⟨ ⋆-cong (ℚP.+-congˡ (+ 1 / j) {+ 1 / n ℚ.+ + 1 / n} {+ 2 / n}
                                             (ℚ.*≡* (ℤsolve 1 (λ n ->
                                             (ℤΚ (+ 1) :* n :+ ℤΚ (+ 1) :* n) :* n := ℤΚ (+ 2) :* (n :* n))
                                             refl (+ n)))) ⟩
  (+ 2 / n ℚ.+ + 1 / j) ⋆                  ∎)})}
  where open ≤-Reasoning

equalMembersEqualLimits : ∀ {@0 xs : ℕ -> ℝ} {@0 ys : ℕ -> ℝ} -> @0 (∀ n -> @0 {n ≢0} -> xs n ≃ ys n) -> (x→x₀ : IsConvergent xs) -> ConvergesTo ys (proj₁' x→x₀)
equalMembersEqualLimits {xs} {ys} xₙ≃yₙ (x₀ :^: MkCon xₙConTox₀) = MkCon (λ k {k≢0} ->
                                                     proj₁ (xₙConTox₀ k {k≢0}) :&: λ @0 {(suc n-1) n≥N -> let n = suc n-1 in begin
  ∣ ys n - x₀ ∣ ≈⟨ ∣-∣-cong (+-congˡ (- x₀) (≃-sym (xₙ≃yₙ n))) ⟩
  ∣ xs n - x₀ ∣ ≤⟨ proj₂ (xₙConTox₀ k) n n≥N ⟩
  ((+ 1 / k) {k≢0}) ⋆    ∎})
  where open ≤-Reasoning
{-# COMPILE AGDA2HS equalMembersEqualLimits #-}

abstract
  fastEqualMembersEqualLimits : ∀ {@0 xs : ℕ -> ℝ} {@0 ys : ℕ -> ℝ} -> @0 (∀ n -> @0 {n ≢0} -> xs n ≃ ys n) -> (x→x₀ : IsConvergent xs) -> ConvergesTo ys (proj₁' x→x₀)
  fastEqualMembersEqualLimits = equalMembersEqualLimits
  {-# COMPILE AGDA2HS fastEqualMembersEqualLimits #-}

convergenceToEqual : ∀ {@0 xs : ℕ -> ℝ} -> ∀ {@0 x : ℝ} {@0 y : ℝ} -> ConvergesTo xs x -> @0 x ≃ y -> ConvergesTo xs y
convergenceToEqual {xs} {x} {y} (MkCon xₙConTox) x≃y = MkCon (λ k {k≢0} -> let Nₖ-1 = proj₁ (xₙConTox k {k≢0}) ; Nₖ = suc Nₖ-1 in
                                             Nₖ-1 :&: λ n n≥Nₖ -> begin
  ∣ xs n - y ∣ ≈⟨ ∣-∣-cong (+-congʳ (xs n) (-‿cong (≃-sym x≃y))) ⟩
  ∣ xs n - x ∣ ≤⟨ proj₂ (xₙConTox k) n n≥Nₖ ⟩
  ((+ 1 / k) {k≢0}) ⋆   ∎)
  where open ≤-Reasoning
{-# COMPILE AGDA2HS convergenceToEqual #-}

@0 uniqueness-of-limits : ∀ {f : ℕ -> ℝ} -> ∀ {x y : ℝ} -> ConvergesTo f x -> ConvergesTo f y -> x ≃ y
uniqueness-of-limits {f} {x} {y} (MkCon f→x) (MkCon f→y) = ∣x-y∣≤k⁻¹⇒x≃y x y (λ @0 {(suc k-1) ->
                                                         let k = suc k-1; N₁ = suc (proj₁ (f→x (2 ℕ.* k))); N₂ = suc (proj₁ ((f→y (2 ℕ.* k))))
                                                               ; N = N₁ ℕ.⊔ N₂ in begin
  ∣ x - y ∣                                 ≈⟨ ∣-∣-cong (solve 3 (λ x y fN ->
                                               (x ⊖ y) ⊜ ((x ⊖ fN) ⊕ (fN ⊖ y)))
                                               ≃-refl x y (f N)) ⟩
  ∣ (x - f N) + (f N - y) ∣                 ≤⟨ ∣x+y∣≤∣x∣+∣y∣ (x - f N) (f N - y) ⟩
  ∣ x - f N ∣ + ∣ f N - y ∣                 ≤⟨ +-mono-≤
                                              (≤-respˡ-≃ (∣x-y∣≃∣y-x∣ (f N) x) (proj₂ (f→x (2 ℕ.* k)) N (ℕP.m≤m⊔n N₁ N₂)))
                                              (proj₂ (f→y (2 ℕ.* k)) N (ℕP.m≤n⊔m N₁ N₂)) ⟩
  (+ 1 / (2 ℕ.* k)) ⋆ + (+ 1 / (2 ℕ.* k)) ⋆ ≈⟨ ≃-trans
                                               (≃-sym (⋆-distrib-+ (+ 1 / (2 ℕ.* k)) (+ 1 / (2 ℕ.* k))))
                                               (⋆-cong (ℚ.*≡* (ℤsolve 1 (λ k ->
                                               (ℤΚ (+ 1) :* (ℤΚ (+ 2) :* k) :+ ℤΚ (+ 1) :* (ℤΚ (+ 2) :* k)) :* k :=
                                               ℤΚ (+ 1) :* (ℤΚ (+ 2) :* k :* (ℤΚ (+ 2) :* k)))
                                               refl (+ k)))) ⟩
  (+ 1 / k) ⋆                                ∎})
  where open ≤-Reasoning

-- Actually, this can be erased altogether.
data _hasBound_ : @0 (ℕ -> ℝ) -> ℝ -> Set where
  bound* : {f : ℕ -> ℝ} -> {r : ℝ} -> @0 (∀ n -> {n ≢0} -> ∣ f n ∣ ≤ r) -> f hasBound r 

-- This is going to be used; so:
IsBounded : @0 (ℕ -> ℝ) -> Set
IsBounded f = Σ0 ℝ λ r -> f hasBound r
{-# COMPILE AGDA2HS IsBounded #-}

-- This is the first one which really uses the series itself; so it cannot be erased.
convergentThenBounded : ∀ (f : ℕ -> ℝ) -> IsConvergent f -> IsBounded f
convergentThenBounded f (x₀ :^: MkCon fConTox₀) = l₂ :&: bound* (λ @0 {(suc n-1) -> let n = suc n-1 in
                                          [ (λ l₁≤n -> ≤-trans (lem n l₁≤n) (x≤y⊔x (oneℝ + ∣ x₀ ∣) (max absf l₁))) ,
                                            (λ n≤l₁ -> ≤-trans (m≤n⇒fm≤maxfn absf n l₁ n≤l₁) (x≤x⊔y (max absf l₁) (oneℝ + ∣ x₀ ∣))) ]′
                                          (ℕP.≤-total l₁ n)})
  where
    open ≤-Reasoning
    absf = λ n -> abs (f n)
    l₁ = suc (proj₁ (fConTox₀ 1))
    l₂ = max absf l₁ ⊔ (oneℝ + abs x₀)
    @0 lem : ∀ n -> l₁ ℕ.≤ n -> ∣ f n ∣ ≤ oneℝ + ∣ x₀ ∣
    lem (suc n-1) l₁≤n = let n = suc n-1 in begin
      ∣ f n ∣               ≈⟨ ∣-∣-cong (solve 2 (λ fn x₀ ->
                               fn ⊜ (fn ⊖ x₀ ⊕ x₀))
                               ≃-refl (f n) x₀) ⟩
      ∣ f n - x₀ + x₀ ∣     ≤⟨ ∣x+y∣≤∣x∣+∣y∣ (f n - x₀) x₀ ⟩
      ∣ f n - x₀ ∣ + ∣ x₀ ∣ ≤⟨ +-monoˡ-≤ ∣ x₀ ∣ (proj₂ (fConTox₀ 1) n l₁≤n) ⟩
      oneℝ + ∣ x₀ ∣ ∎
{-# COMPILE AGDA2HS convergentThenBounded #-}

-- Alias.
@0 convergent⇒bounded : ∀ {f : ℕ -> ℝ} -> IsConvergent f -> IsBounded f
convergent⇒bounded {f} = convergentThenBounded f

data IsCauchy : (@0 f : ℕ -> ℝ) -> Set where
  MkCauchy : {@0 f : ℕ -> ℝ} ->
            (∀ k -> {@0 k≢0 : k ≢0} -> Σ0 ℕ λ Mₖ-1 -> ∀ m n -> m ℕ.≥ suc Mₖ-1 -> n ℕ.≥ suc Mₖ-1 -> -- cauchy⇒convergent's N needs this as non-erased;
                    ∣ f m - f n ∣ ≤ (+ 1 / k) {k≢0} ⋆) -> IsCauchy f                                 -- it will essentially be compiled to a Nat -> Nat function
{-# COMPILE AGDA2HS IsCauchy newtype #-}

@0 convergent⇒cauchy : ∀ {f : ℕ -> ℝ} -> IsConvergent f -> IsCauchy f
convergent⇒cauchy {f} (x₀ :^: MkCon f→x₀) = MkCauchy (λ {(suc k-1) ->
                                         let k = suc k-1; N₂ₖ = suc (proj₁ (f→x₀ (2 ℕ.* k))); Mₖ = suc N₂ₖ in
                                         ℕ.pred Mₖ :&: λ @0 {(suc m-1) (suc n-1) m≥Mₖ n≥Mₖ -> let m = suc m-1 ; n = suc n-1 in
                                         begin
  ∣ f m - f n ∣                             ≈⟨ ∣-∣-cong (solve 3 (λ fm fn x₀ ->
                                               (fm ⊖ fn) ⊜ (fm ⊖ x₀ ⊕ (x₀ ⊖ fn)))
                                               ≃-refl (f m) (f n) x₀) ⟩
  ∣ f m - x₀ + (x₀ - f n) ∣                 ≤⟨ ∣x+y∣≤∣x∣+∣y∣ (f m - x₀) (x₀ - f n) ⟩
  ∣ f m - x₀ ∣ + ∣ x₀ - f n ∣               ≤⟨ +-mono-≤
                                              (proj₂ (f→x₀ (2 ℕ.* k)) m (ℕP.≤-trans (ℕP.n≤1+n N₂ₖ) m≥Mₖ))
                                              (≤-respˡ-≃ (∣x-y∣≃∣y-x∣ (f n) x₀)
                                                         (proj₂ (f→x₀ (2 ℕ.* k)) n (ℕP.≤-trans (ℕP.n≤1+n N₂ₖ) n≥Mₖ))) ⟩
  (+ 1 / (2 ℕ.* k)) ⋆ + (+ 1 / (2 ℕ.* k)) ⋆ ≈⟨ ≃-trans
                                               (≃-sym (⋆-distrib-+ (+ 1 / (2 ℕ.* k)) (+ 1 / (2 ℕ.* k))))
                                               (⋆-cong (ℚ.*≡* (ℤsolve 1 (λ k ->
                                               (ℤΚ (+ 1) :* (ℤΚ (+ 2) :* k) :+ ℤΚ (+ 1) :* (ℤΚ (+ 2) :* k)) :* k :=
                                               ℤΚ (+ 1) :* (ℤΚ (+ 2) :* k :* (ℤΚ (+ 2) :* k)))
                                               refl (+ k)))) ⟩
  (+ 1 / k) ⋆                                ∎}})
  where open ≤-Reasoning

cauchyToConvergent : ∀ (f : ℕ -> ℝ) -> IsCauchy f -> IsConvergent f
cauchyToConvergent f (MkCauchy fCauchy) = y :^: fConToy
  where
    open ≤-Reasoning
    a : ℕ -> ℕ
    a km1 = let k = suc km1; M₂ₖ = suc (proj₁ (fCauchy (2 ℕ.* k))) in
                  suc ((3 ℕ.* k) ℕ.⊔ M₂ₖ)

    @0 aₖ-prop : ∀ k-1 -> ∀ m n -> m ℕ.≥ a k-1 -> n ℕ.≥ a k-1 -> ∣ f m - f n ∣ ≤ (+ 1 / (2 ℕ.* (suc k-1))) ⋆
    aₖ-prop k-1 = λ @0 {(suc m-1) (suc n-1) m≥a n≥a -> let k = suc k-1; m = suc m-1; n = suc n-1; M₂ₖ = suc (proj₁ (fCauchy (2 ℕ.* k))) in
                  proj₂ (fCauchy (2 ℕ.* k)) m n
                  (ℕP.≤-trans (ℕP.≤-trans (ℕP.m≤n⊔m (3 ℕ.* k) M₂ₖ) (ℕP.n≤1+n ((3 ℕ.* k) ℕ.⊔ M₂ₖ))) m≥a)
                  (ℕP.≤-trans (ℕP.≤-trans (ℕP.m≤n⊔m (3 ℕ.* k) M₂ₖ) (ℕP.n≤1+n ((3 ℕ.* k) ℕ.⊔ M₂ₖ))) n≥a)}

    @0 helper : ∀ k-1 -> (+ 1 / (2 ℕ.* (suc k-1))) ⋆ + (+ 1 / (2 ℕ.* (suc k-1))) ⋆ ≃ (+ 1 / (suc k-1)) ⋆
    helper k-1 = let k = suc k-1 in begin-equality
      (+ 1 / (2 ℕ.* k)) ⋆ + (+ 1 / (2 ℕ.* k)) ⋆ ≈⟨ ≃-sym (⋆-distrib-+ (+ 1 / (2 ℕ.* k)) (+ 1 / (2 ℕ.* k))) ⟩
      (+ 1 / (2 ℕ.* k) ℚ.+ + 1 / (2 ℕ.* k)) ⋆   ≈⟨ ⋆-cong (ℚ.*≡* (ℤsolve 1 (λ k ->
                                                   (ℤΚ (+ 1) :* (ℤΚ (+ 2) :* k) :+ (ℤΚ (+ 1) :* (ℤΚ (+ 2) :* k))) :* k :=
                                                   ℤΚ (+ 1) :* (ℤΚ (+ 2) :* k :* (ℤΚ (+ 2) :* k)))
                                                   refl (+ k))) ⟩
      (+ 1 / k) ⋆                                ∎

    @0 helper2 : ∀ m-1 n-1 -> ∣ f (a m-1) - f (a n-1) ∣ ≤ (+ 1 / (2 ℕ.* (suc m-1)) ℚ.+ + 1 / (2 ℕ.* (suc n-1))) ⋆
    helper2 m-1 n-1 = [ left , right ]′ (ℕP.≤-total (a m-1) (a n-1))
      where
        m = suc m-1
        n = suc n-1
        left : a m-1 ℕ.≤ a n-1 -> ∣ f (a m-1) - f (a n-1) ∣ ≤ (+ 1 / (2 ℕ.* m) ℚ.+ + 1 / (2 ℕ.* n)) ⋆
        left aₘ≤aₙ = begin 
          ∣ f (a m-1) - f (a n-1) ∣               ≤⟨ aₖ-prop m-1 (a m-1) (a n-1) ℕP.≤-refl aₘ≤aₙ ⟩
          (+ 1 / (2 ℕ.* m)) ⋆                     ≤⟨ p≤q⇒p⋆≤q⋆ (+ 1 / (2 ℕ.* m)) (+ 1 / (2 ℕ.* m) ℚ.+ + 1 / (2 ℕ.* n))
                                                     (ℚP.≤-respˡ-≃ (ℚP.+-identityʳ (+ 1 / (2 ℕ.* m)))
                                                     (ℚP.+-monoʳ-≤ (+ 1 / (2 ℕ.* m)) {0ℚᵘ} {+ 1 / (2 ℕ.* n)} (ℚP.nonNegative⁻¹ _))) ⟩
          (+ 1 / (2 ℕ.* m) ℚ.+ + 1 / (2 ℕ.* n)) ⋆  ∎

        right : a n-1 ℕ.≤ a m-1 -> ∣ f (a m-1) - f (a n-1) ∣ ≤ (+ 1 / (2 ℕ.* m) ℚ.+ + 1 / (2 ℕ.* n)) ⋆
        right aₙ≤aₘ = begin
          ∣ f (a m-1) - f (a n-1) ∣               ≈⟨ ∣x-y∣≃∣y-x∣ (f (a m-1)) (f (a n-1)) ⟩
          ∣ f (a n-1) - f (a m-1) ∣               ≤⟨ aₖ-prop n-1 (a n-1) (a m-1) ℕP.≤-refl aₙ≤aₘ ⟩
          (+ 1 / (2 ℕ.* n)) ⋆                     ≤⟨ p≤q⇒p⋆≤q⋆ (+ 1 / (2 ℕ.* n)) (+ 1 / (2 ℕ.* m) ℚ.+ + 1 / (2 ℕ.* n))
                                                     (ℚP.≤-respˡ-≃ (ℚP.+-identityˡ (+ 1 / (2 ℕ.* n)))
                                                     (ℚP.+-monoˡ-≤ (+ 1 / (2 ℕ.* n)) {0ℚᵘ} {+ 1 / (2 ℕ.* m)} (ℚP.nonNegative⁻¹ _))) ⟩
          (+ 1 / (2 ℕ.* m) ℚ.+ + 1 / (2 ℕ.* n)) ⋆  ∎

    ys : ℕ -> ℚᵘ
    ys 0 = (+ 0 / 1)
    ys k = let km1 = ℕ.pred k in
        seq (f (a km1)) (2 ℕ.* k)  -- this is ys' definition copied here; this way it need not deduce k≢0

    y : ℝ
    -- seq y 0 = 0ℚᵘ
    -- seq y (suc km1) = ys (suc km1)
    -- reg y
    y = Mkℝ ys (regular-n≤m (ys) (λ @0 {(suc m-1) (suc n-1) n≤m -> let m = suc m-1; n = suc n-1 in
                                p⋆≤q⋆⇒p≤q ℚ.∣ ys m ℚ.- ys n ∣ (+ 1 / m ℚ.+ + 1 / n) (begin
      ℚ.∣ ys m ℚ.- ys n ∣ ⋆                             ≈⟨ ≃-trans
                                                                (∣p∣⋆≃∣p⋆∣ (ys m ℚ.- ys n))
                                                                (∣-∣-cong (⋆-distrib-to-p⋆-q⋆ (ys m) (ys n)))  ⟩
      ∣ ys m ⋆ - ys n ⋆ ∣                                ≈⟨ ∣-∣-cong (solve 4 (λ yₘ yₙ fm-1 fn-1 ->
                                                                yₘ ⊖ yₙ ⊜ yₘ ⊖ fm-1 ⊕ (fm-1 ⊖ fn-1) ⊕ (fn-1 ⊖ yₙ))
                                                                ≃-refl (ys m ⋆) (ys n ⋆) (f (a m-1)) (f (a n-1))) ⟩
      ∣ (ys m ⋆ - f (a m-1)) + (f (a m-1) - f (a n-1)) 
        + (f (a n-1) - ys n ⋆) ∣                        ≤⟨ ≤-trans
                                                                (∣x+y∣≤∣x∣+∣y∣ ((ys m ⋆ - f (a m-1)) + (f (a m-1) - f (a n-1))) (f (a n-1) - ys n ⋆))
                                                                (+-monoˡ-≤ ∣ f (a n-1) - ys n ⋆ ∣ (∣x+y∣≤∣x∣+∣y∣ (ys m ⋆ - f (a m-1)) (f (a m-1) - f (a n-1)))) ⟩
      ∣ ys m ⋆ - f (a m-1) ∣ + ∣ f (a m-1) - f (a n-1) ∣
        + ∣ f (a n-1) - ys n ⋆ ∣                         ≤⟨ +-mono-≤
                                                                (+-mono-≤ (≤-respˡ-≃ (∣x-y∣≃∣y-x∣ (f (a m-1)) (ys m ⋆)) (lemma-2-14 (f (a m-1)) (2 ℕ.* m)))
                                                                (≤-respʳ-≃ (⋆-distrib-+ (+ 1 / (2 ℕ.* m)) (+ 1 / (2 ℕ.* n))) (helper2 m-1 n-1)))
                                                                (lemma-2-14 (f (a n-1)) (2 ℕ.* n)) ⟩
      (+ 1 / (2 ℕ.* m)) ⋆ + ((+ 1 / (2 ℕ.* m)) ⋆
        + (+ 1 / (2 ℕ.* n)) ⋆) + (+ 1 / (2 ℕ.* n)) ⋆  ≈⟨ solve 2 (λ m n -> (m ⊕ (m ⊕ n) ⊕ n) ⊜ ((m ⊕ m) ⊕ (n ⊕ n)))
                                                         ≃-refl ((+ 1 / (2 ℕ.* m)) ⋆) ((+ 1 / (2 ℕ.* n)) ⋆) ⟩
      (+ 1 / (2 ℕ.* m)) ⋆ + (+ 1 / (2 ℕ.* m)) ⋆
        + ((+ 1 / (2 ℕ.* n)) ⋆ + (+ 1 / (2 ℕ.* n)) ⋆) ≈⟨ +-cong (helper m-1) (helper n-1) ⟩
      (+ 1 / m) ⋆ + (+ 1 / n) ⋆                       ≈⟨ ≃-sym (⋆-distrib-+ (+ 1 / m) (+ 1 / n)) ⟩
      (+ 1 / m ℚ.+ + 1 / n) ⋆                          ∎)}))

    fConToy : ConvergesTo f y
    fConToy = MkCon (λ k {k≢0} -> let k-1 = ℕ.pred k in ℕ.pred (a k-1) :&: conProof k {k≢0})
      where
        -- Here we can finally pattern match on k.
        @0 conProof : ∀ (k : ℕ) {@0 k≢0 : k ≢0} -> ∀ n -> n ℕ.≥ suc (ℕ.pred (a (ℕ.pred k))) -> abs (f n - y) ≤ toReal ((+ 1 / k) {k≢0})
        conProof (suc k-1) (suc n-1) n≥aₖ = let k = suc k-1 ; n = suc n-1 ; n≥3k = ℕP.≤-trans (ℕP.≤-trans (ℕP.m≤m⊔n (3 ℕ.* k) (suc (proj₁ (fCauchy (2 ℕ.* k))))) (ℕP.n≤1+n (ℕ.pred (a k-1)))) n≥aₖ in
         begin
          ∣ f n - y ∣                                                  ≈⟨ ∣-∣-cong (solve 4 (λ fn y yₙ fn-1 ->
                                                                        fn ⊖ y ⊜ yₙ ⊖ y ⊕ (fn-1 ⊖ yₙ) ⊕ (fn ⊖ fn-1))
                                                                        ≃-refl (f n) y (ys n ⋆) (f (a n-1))) ⟩
          ∣ (ys n ⋆ - y) + (f (a n-1) - ys n ⋆) + (f n - f (a n-1)) ∣  ≤⟨ ≤-trans
                                                                        (∣x+y∣≤∣x∣+∣y∣ ((ys n ⋆ - y) + (f (a n-1) - ys n ⋆)) (f n - f (a n-1)))
                                                                        (+-monoˡ-≤ ∣ f n - f (a n-1) ∣ (∣x+y∣≤∣x∣+∣y∣ (ys n ⋆ - y) (f (a n-1) - ys n ⋆))) ⟩
          ∣ ys n ⋆ - y ∣ + ∣ f (a n-1) - ys n ⋆ ∣ + ∣ f n - f (a n-1) ∣  ≤⟨ +-mono-≤ (+-mono-≤
                                                                        (≤-respˡ-≃ (∣x-y∣≃∣y-x∣ y (ys n ⋆)) (lemma-2-14 y n))
                                                                        (lemma-2-14 (f (a n-1)) (2 ℕ.* n)))
                                                                        (aₖ-prop k-1 n (a n-1) n≥aₖ
                                                                        (ℕP.≤-trans (ℕP.≤-trans n≥aₖ (ℕP.m≤n*m n {3} ℕP.0<1+n))
                                                                                    (ℕP.≤-trans (ℕP.m≤m⊔n (3 ℕ.* n) (suc (proj₁ (fCauchy (2 ℕ.* n)))))
                                                                                                (ℕP.n≤1+n (ℕ.pred (a n-1)))))) ⟩
          (+ 1 / n) ⋆ + (+ 1 / (2 ℕ.* n)) ⋆ + (+ 1 / (2 ℕ.* k)) ⋆   ≈⟨ solve 0
                                                                       (Κ (+ 1 / n) ⊕ Κ (+ 1 / (2 ℕ.* n)) ⊕ Κ (+ 1 / (2 ℕ.* k)) ⊜
                                                                       Κ (+ 1 / n ℚ.+ + 1 / (2 ℕ.* n) ℚ.+ + 1 / (2 ℕ.* k)))
                                                                       ≃-refl ⟩
          (+ 1 / n ℚ.+ + 1 / (2 ℕ.* n) ℚ.+ + 1 / (2 ℕ.* k)) ⋆     ≤⟨ p≤q⇒p⋆≤q⋆ _ _
                                                                       (ℚP.+-monoˡ-≤ (+ 1 / (2 ℕ.* k)) (ℚP.+-mono-≤
                                                                       (q≤r⇒+p/r≤+p/q 1 (3 ℕ.* k) n n≥3k)
                                                                       (q≤r⇒+p/r≤+p/q 1 (2 ℕ.* (3 ℕ.* k)) (2 ℕ.* n) (ℕP.*-monoʳ-≤ 2 n≥3k)))) ⟩
          (+ 1 / (3 ℕ.* k) ℚ.+ + 1 / (2 ℕ.* (3 ℕ.* k)) ℚ.+ + 1 / (2 ℕ.* k)) ⋆ ≈⟨ ⋆-cong (ℚ.*≡* (ℤsolve 1 (λ k ->
                                                                                 ((ℤΚ (+ 1) :* (ℤΚ (+ 2) :* (ℤΚ (+ 3) :* k)) :+
                                                                                 ℤΚ (+ 1) :* (ℤΚ (+ 3) :* k)) :* (ℤΚ (+ 2) :* k) :+
                                                                                 (ℤΚ (+ 1) :* (ℤΚ (+ 3) :* k :* (ℤΚ (+ 2) :* (ℤΚ (+ 3) :* k))))) :* k :=
                                                                                 ℤΚ (+ 1) :* ((ℤΚ (+ 3) :* k :* (ℤΚ (+ 2) :* (ℤΚ (+ 3) :* k))) :* (ℤΚ (+ 2) :* k)))
                                                                                 refl (+ k))) ⟩
          (+ 1 / k) ⋆                                                          ∎
{-# COMPILE AGDA2HS cauchyToConvergent #-}

abstract
  @0 fast-convergent⇒cauchy : ∀ {f : ℕ -> ℝ} -> IsConvergent f -> IsCauchy f
  fast-convergent⇒cauchy = convergent⇒cauchy

  fastCauchyToConvergent : ∀ (f : ℕ -> ℝ) -> IsCauchy f -> IsConvergent f
  fastCauchyToConvergent = cauchyToConvergent
  {-# COMPILE AGDA2HS fastCauchyToConvergent #-}

limitOfSum : ∀ {@0 xs : ℕ -> ℝ} {@0 ys : ℕ -> ℝ} -> (xₙ→x₀ : IsConvergent xs) -> (yₙ→y₀ : IsConvergent ys) ->
              ConvergesTo (λ n -> xs n + ys n) (proj₁' xₙ→x₀ + proj₁' yₙ→y₀)
limitOfSum {xs} {ys} (x₀ :^: MkCon xₙConTox₀) (y₀ :^: MkCon yₙConToy₀) = MkCon main
  where
    open ≤-Reasoning

    @0 2*k≢0 : ∀ {k : ℕ} -> k ≢0 -> 2 ℕ.* k ≢0
    2*k≢0 {suc _} _ = tt

    @0 conProof : ∀ (k : ℕ) {k≢0 : k ≢0} -> ∀ n ->
      n ℕ.≥ suc (proj₁ (xₙConTox₀ (2 ℕ.* k) {2*k≢0 k≢0})) ℕ.⊔ suc (proj₁ (yₙConToy₀ (2 ℕ.* k) {2*k≢0 k≢0})) ->
      abs ((xs n + ys n) - (x₀ + y₀)) ≤ toReal ((+ 1 / k) {k≢0})
    conProof (suc k-1) (suc n-1) l≤n = let k = suc k-1; n = suc n-1; xₙ = xs n; yₙ = ys n in begin
       ∣ xₙ + yₙ - (x₀ + y₀) ∣                   ≈⟨ ∣-∣-cong (solve 4 (λ xₙ yₙ x₀ y₀ ->
                                                    xₙ ⊕ yₙ ⊖ (x₀ ⊕ y₀) ⊜ xₙ ⊖ x₀ ⊕ (yₙ ⊖ y₀))
                                                    ≃-refl xₙ yₙ x₀ y₀) ⟩
       ∣ xₙ - x₀ + (yₙ - y₀) ∣                   ≤⟨ ∣x+y∣≤∣x∣+∣y∣ (xₙ - x₀) (yₙ - y₀) ⟩
       ∣ xₙ - x₀ ∣ + ∣ yₙ - y₀ ∣                 ≤⟨ +-mono-≤
                                                    (proj₂ (xₙConTox₀ (2 ℕ.* k)) n (ℕP.≤-trans (ℕP.m≤m⊔n l₁ l₂) l≤n))
                                                    (proj₂ (yₙConToy₀ (2 ℕ.* k)) n (ℕP.≤-trans (ℕP.m≤n⊔m l₁ l₂) l≤n)) ⟩
       (+ 1 / (2 ℕ.* k)) ⋆ + (+ 1 / (2 ℕ.* k)) ⋆ ≈⟨ ≃-trans
                                                    (≃-sym (⋆-distrib-+ (+ 1 / (2 ℕ.* k)) (+ 1 / (2 ℕ.* k))))
                                                    (⋆-cong (ℚ.*≡* (ℤsolve 1 (λ k ->
                                                    (ℤΚ (+ 1) :* (ℤΚ (+ 2) :* k) :+ ℤΚ (+ 1) :* (ℤΚ (+ 2) :* k)) :* k :=
                                                    ℤΚ (+ 1) :* (ℤΚ (+ 2) :* k :* (ℤΚ (+ 2) :* k)))
                                                    refl (+ k)))) ⟩
       (+ 1 / k) ⋆                                ∎
      where
            l l₁ l₂ : ℕ
            l₁ = suc (proj₁ (xₙConTox₀ (2 ℕ.* suc k-1)))
            l₂ = suc (proj₁ (yₙConToy₀ (2 ℕ.* suc k-1)))
            l = l₁ ℕ.⊔ l₂

    main : (∀ k -> {@0 k≢0 : k ≢0} -> Σ0 ℕ λ lₖ-1 -> (∀ n -> n ℕ.≥ suc (lₖ-1) -> abs ((xs n + ys n) - (x₀ + y₀)) ≤ toReal ((+ 1 / k) {k≢0})))
    main k {k≢0} = ℕ.pred (suc (proj₁ (xₙConTox₀ (2 ℕ.* k))) ℕ.⊔ suc (proj₁ (yₙConToy₀ (2 ℕ.* k))))
                         :&: conProof k {k≢0}
{-# COMPILE AGDA2HS limitOfSum #-}

boundToBoundℕ : ∀ {@0 f : ℕ -> ℝ} -> IsBounded f ->
               Σ0 ℕ λ (M-1 : ℕ) -> ∀ (n : ℕ) -> {n ≢0} -> ∣ f n ∣ < (+ suc (M-1) / 1) ⋆
boundToBoundℕ {f} (r :&: (bound* ∣f∣≤r)) = let M = suc (proj₁ (archimedeanℝ r)) in
                               ℕ.pred M :&: λ @0 {(suc n-1) -> let n = suc n-1 in begin-strict
  ∣ f n ∣     ≤⟨ ∣f∣≤r n ⟩
  r           <⟨ proj₂ (archimedeanℝ r) ⟩
  (+ M / 1) ⋆  ∎}
  where open ≤-Reasoning
{-# COMPILE AGDA2HS boundToBoundℕ #-}

limitOfNegate : ∀ {@0 xs : ℕ -> ℝ} -> (x→x₀ : IsConvergent xs) -> ConvergesTo (λ n -> - xs n) (- (proj₁' x→x₀))
limitOfNegate {xs} (x₀ :^: MkCon xConTox₀) = MkCon (λ k {k≢0} ->
                                proj₁ (xConTox₀ k {k≢0}) :&: λ @0 {(suc n-1) n≥N -> let n = suc n-1 in begin
  ∣ - xs n - (- x₀) ∣ ≈⟨ ∣-∣-cong (solve 2 (λ xₙ x₀ ->
                         ⊝ xₙ ⊖ (⊝ x₀) ⊜ ⊝ (xₙ ⊖ x₀))
                         ≃-refl (xs n) x₀) ⟩
  ∣ - (xs n - x₀) ∣   ≈⟨ ∣-x∣≃∣x∣ ⟩
  ∣ xs n - x₀ ∣       ≤⟨ proj₂ (xConTox₀ k) n n≥N ⟩
  ((+ 1 / k) {k≢0}) ⋆          ∎})
  where open ≤-Reasoning
{-# COMPILE AGDA2HS limitOfNegate #-}

-- Interestingly, xs needs to be kept, but ys need not.
limitOfProduct : ∀ (xs : ℕ -> ℝ) {@0 ys : ℕ -> ℝ} (xₙ→x₀ : IsConvergent xs) (yₙ→y₀ : IsConvergent ys) ->
            ConvergesTo (λ n -> (xs n * ys n)) (proj₁' xₙ→x₀ * proj₁' yₙ→y₀)
limitOfProduct xs {ys} (x₀ :^: MkCon xₙConTox₀) (y₀ :^: MkCon yₙConToy₀) = MkCon (λ k {k≢0} ->
               let archy₀ = archimedeanℝ (abs y₀); N₁ = suc (proj₁ archy₀)
                     ; N₂ = suc (proj₁ boundxₙ); m = N₁ ℕ.⊔ N₂
                     ; M₁ = suc (proj₁ (xₙConTox₀ (2 ℕ.* m ℕ.* k)
                                          {≢0-helper {m} (m≢0-helper (proj₁ archy₀) (proj₁ boundxₙ)) {k} k≢0}))
                     ; M₂ = suc (proj₁ (yₙConToy₀ (2 ℕ.* m ℕ.* k)
                                          {≢0-helper {m} (m≢0-helper (proj₁ archy₀) (proj₁ boundxₙ)) {k} k≢0}))
                     ; Mₖ = M₁ ℕ.⊔ M₂ in ℕ.pred Mₖ :&: λ @0 {(suc n-1) n≥Mₖ -> let n = suc n-1; xₙ = xs (suc n-1); yₙ = ys (suc n-1) in begin
               ∣ xₙ * yₙ - x₀ * y₀ ∣                               ≈⟨ ∣-∣-cong (solve 4 (λ xₙ yₙ x₀ y₀ ->
                                                         xₙ ⊗ yₙ ⊖ x₀ ⊗ y₀ ⊜ xₙ ⊗ yₙ ⊕ xₙ ⊗ (⊝ y₀) ⊕ (xₙ ⊗ y₀ ⊖ x₀ ⊗ y₀))
                                                         ≃-refl xₙ yₙ x₀ y₀) ⟩ 
  ∣ xₙ * yₙ + xₙ * (- y₀) + (xₙ * y₀ - x₀ * y₀) ∣     ≤⟨ ∣x+y∣≤∣x∣+∣y∣ (xₙ * yₙ + xₙ * (- y₀)) (xₙ * y₀ - x₀ * y₀) ⟩
  ∣ xₙ * yₙ + xₙ * (- y₀) ∣ + ∣ xₙ * y₀ - x₀ * y₀ ∣   ≈⟨ ≃-sym (+-cong
                                                         (∣-∣-cong (*-distribˡ-+ xₙ yₙ (- y₀)))
                                                         (∣-∣-cong (solve 3 (λ xₙ x₀ y₀ ->
                                                                   (xₙ ⊖ x₀) ⊗ y₀ ⊜ xₙ ⊗ y₀ ⊖ x₀ ⊗ y₀)
                                                                   ≃-refl xₙ x₀ y₀))) ⟩
  ∣ xₙ * (yₙ - y₀) ∣ + ∣ (xₙ - x₀) * y₀ ∣             ≈⟨ +-cong
                                                         (∣x*y∣≃∣x∣*∣y∣ xₙ (yₙ - y₀))
                                                         (≃-trans (∣x*y∣≃∣x∣*∣y∣ (xₙ - x₀) y₀) (*-comm ∣ xₙ - x₀ ∣ ∣ y₀ ∣)) ⟩
  ∣ xₙ ∣ * ∣ yₙ - y₀ ∣ + ∣ y₀ ∣ * ∣ xₙ - x₀ ∣          ≤⟨ +-mono-≤ {∣ xₙ ∣ * ∣ yₙ - y₀ ∣} {(+ m / 1) ⋆ * (+ 1 / (2 ℕ.* m ℕ.* k)) ⋆}
                                                                  {∣ y₀ ∣ * ∣ xₙ - x₀ ∣} {(+ m / 1) ⋆ * (+ 1 / (2 ℕ.* m ℕ.* k)) ⋆}
                                                         (*-mono-≤ {∣ xₙ ∣} {(+ m / 1) ⋆} {∣ yₙ - y₀ ∣} {(+ 1 / (2 ℕ.* m ℕ.* k)) ⋆}
                                                                   (nonNeg∣x∣ xₙ) (nonNeg∣x∣ (yₙ - y₀))
                                                                   (<⇒≤ (ltLe0Trans _ _ _ (proj₂ boundxₙ n) (p≤q⇒p⋆≤q⋆ (+ N₂ / 1) (+ m / 1)
                                                                                   (p≤q⇒p/r≤q/r (+ N₂) (+ m) 1 (ℤ.+≤+ (ℕP.m≤n⊔m N₁ N₂))))))
                                                                   (proj₂ (yₙConToy₀ (2 ℕ.* m ℕ.* k)) n (ℕP.≤-trans (ℕP.m≤n⊔m M₁ M₂) n≥Mₖ)))
                                                         (*-mono-≤ {∣ y₀ ∣} {(+ m / 1) ⋆} {∣ xₙ - x₀ ∣} {(+ 1 / (2 ℕ.* m ℕ.* k)) ⋆}
                                                                   (nonNeg∣x∣ y₀) (nonNeg∣x∣ (xₙ - x₀))
                                                                   (<⇒≤ (ltLe0Trans _ _ _ (proj₂ archy₀) (p≤q⇒p⋆≤q⋆ (+ N₁ / 1) (+ m / 1)
                                                                                   (p≤q⇒p/r≤q/r (+ N₁) (+ m) 1 (ℤ.+≤+ (ℕP.m≤m⊔n N₁ N₂))))))
                                                                   (proj₂ (xₙConTox₀ (2 ℕ.* m ℕ.* k)) n (ℕP.≤-trans (ℕP.m≤m⊔n M₁ M₂) n≥Mₖ))) ⟩
  (+ m / 1) ⋆ * (+ 1 / (2 ℕ.* m ℕ.* k)) ⋆ +
  (+ m / 1) ⋆ * (+ 1 / (2 ℕ.* m ℕ.* k)) ⋆             ≈⟨ solve 2 (λ a b ->
                                                         a ⊗ b ⊕ a ⊗ b ⊜ a ⊗ (b ⊕ b))
                                                         ≃-refl ((+ m / 1) ⋆) ((+ 1 / (2 ℕ.* m ℕ.* k)) ⋆) ⟩
  (+ m / 1) ⋆ * ((+ 1 / (2 ℕ.* m ℕ.* k)) ⋆ +
  (+ 1 / (2 ℕ.* m ℕ.* k)) ⋆)                          ≈⟨ solve 0
                                                         (Κ (+ m / 1) ⊗ (Κ (+ 1 / (2 ℕ.* m ℕ.* k)) ⊕ Κ (+ 1 / (2 ℕ.* m ℕ.* k))) ⊜
                                                         Κ (+ m / 1 ℚ.* (+ 1 / (2 ℕ.* m ℕ.* k) ℚ.+ + 1 / (2 ℕ.* m ℕ.* k))))
                                                         ≃-refl ⟩
  (+ m / 1 ℚ.* (+ 1 / (2 ℕ.* m ℕ.* k) ℚ.+
  + 1 / (2 ℕ.* m ℕ.* k))) ⋆                           ≈⟨ ≃-helper m {m≢0-helper (proj₁ archy₀) (proj₁ boundxₙ)} k {k≢0} ⟩
  (+ 1 / k) ⋆                                           ∎})
  where
    open ≤-Reasoning
    boundxₙ : Σ0 ℕ λ (M-1 : ℕ) -> ∀ (n : ℕ) -> {n ≢0} -> ∣ xs n ∣ < (+ suc (M-1) / 1) ⋆
    boundxₙ = boundToBoundℕ (convergentThenBounded xs (x₀ :^: MkCon xₙConTox₀))

    @0 m≢0-helper : ∀ (N₁ N₂ : ℕ) -> suc N₁ ℕ.⊔ suc N₂ ≢0
    m≢0-helper _ _ = tt
    @0 ≢0-helper : ∀ {m : ℕ} -> m ≢0 -> {k : ℕ} -> k ≢0 -> (2 ℕ.* m ℕ.* k) ≢0
    ≢0-helper {suc m-1} _ {suc k-1} _ = tt

    -- For the last equality step:
    @0 ≃-helper : ∀ (m : ℕ) {m≢0 : m ≢0} (k : ℕ) {k≢0 : k ≢0} ->
                    (+ m / 1 ℚ.* ((+ 1 / (2 ℕ.* m ℕ.* k)) {≢0-helper m≢0 k≢0} ℚ.+ (+ 1 / (2 ℕ.* m ℕ.* k)) {≢0-helper m≢0 k≢0})) ⋆
                    ≃ ((+ 1 / k) {k≢0}) ⋆
    ≃-helper (suc m-1) (suc k-1) = let m = suc m-1; k = suc k-1 in
      ⋆-cong (ℚ.*≡* (ℤsolve 2 (λ m k ->
         (m :* (ℤΚ (+ 1) :* (ℤΚ (+ 2) :* m :* k) :+ ℤΚ (+ 1) :* (ℤΚ (+ 2) :* m :* k))) :* k :=
         ℤΚ (+ 1) :* (ℤΚ (+ 1) :* (ℤΚ (+ 2) :* m :* k :* (ℤΚ (+ 2) :* m :* k))))
         refl (+ m) (+ k)))
{-# COMPILE AGDA2HS limitOfProduct #-}

limitOfConst : ∀ {@0 xs : ℕ -> ℝ} -> ∀ {@0 c : ℝ} -> @0 (∀ n -> {n ≢0} -> xs n ≃ c) -> ConvergesTo xs c
limitOfConst {xs} {c} hyp = MkCon (λ k {k≢0} -> 0 :&: thisProof k {k≢0})
  where
  open ≤-Reasoning
  @0 thisProof : ∀ (k : ℕ) {k≢0 : k ≢0} -> (∀ n -> n ℕ.≥ 1 -> abs (xs n - c) ≤ toReal ((+ 1 / k) {k≢0}))
  thisProof (suc k-1) (suc n-1) n≥1 = let k = suc k-1; n = suc n-1 in begin
    ∣ xs n - c ∣ ≈⟨ ∣-∣-cong (+-congˡ (- c) (hyp n)) ⟩
    ∣ c - c ∣    ≈⟨ ≃-trans (∣-∣-cong (+-inverseʳ c)) (≃-reflexive (λ n -> ℚP.≃-refl)) ⟩
    zeroℝ           ≤⟨ p≤q⇒p⋆≤q⋆ 0ℚᵘ (+ 1 / k) (ℚP.nonNegative⁻¹ _) ⟩
    (+ 1 / k) ⋆   ∎
{-# COMPILE AGDA2HS limitOfConst #-}

abstract
  fastLimitOfConst : ∀ {@0 xs : ℕ -> ℝ} -> ∀ {@0 c : ℝ} -> @0 (∀ n -> {n ≢0} -> xs n ≃ c) -> ConvergesTo xs c
  fastLimitOfConst = limitOfConst
  {-# COMPILE AGDA2HS fastLimitOfConst #-}

-- maybe this should be moved to RealProperties some day
@0 <⇒≱ : {x y : ℝ} -> x < y -> x ≱ y
<⇒≱ {x} {y} (MkPos (n-1 :&: x<y)) (nonNeg* x≥y) = let n = suc n-1 in ℚP.<-irrefl-≡ refl (begin-strict
  + 1 / n                                         <⟨ x<y ⟩
  seq y (2 ℕ.* n) ℚ.- seq x (2 ℕ.* n)             ≈⟨ ℚsolve 2 (λ x₂ₙ y₂ₙ ->
                                                     y₂ₙ -: x₂ₙ =: -: (x₂ₙ -: y₂ₙ))
                                                     ℚP.≃-refl (seq x (2 ℕ.* n)) (seq y (2 ℕ.* n)) ⟩
  ℚ.- (seq x (2 ℕ.* n) ℚ.- seq y (2 ℕ.* n))       ≤⟨ ℚP.neg-mono-≤ (x≥y n) ⟩
  ℚ.- (ℚ.- (+ 1 / n))                             ≈⟨ ℚP.neg-involutive (+ 1 / n) ⟩
  + 1 / n                                          ∎)
  where open ℚP.≤-Reasoning

@0 ⋆-distrib-⁻¹ : ∀ p -> (p⋆≄0 : (p ⋆) ≄0) -> ((p ⋆) ⁻¹) p⋆≄0 ≃ ((ℚ.1/ p) {p⋆≄0⇒∣↥p∣≢0 p p⋆≄0}) ⋆
⋆-distrib-⁻¹ p p⋆≄0 = let p⁻¹ = (ℚ.1/ p) {p⋆≄0⇒∣↥p∣≢0 p p⋆≄0}; p⋆⁻¹ = ((p ⋆) ⁻¹) p⋆≄0 in
                      ≃-sym (⁻¹-unique (p⁻¹ ⋆) (p ⋆) p⋆≄0 (begin
  p⁻¹ ⋆ * p ⋆   ≈⟨ ≃-sym (⋆-distrib-* p⁻¹ p) ⟩
  (p⁻¹ ℚ.* p) ⋆ ≈⟨ ⋆-cong (ℚP.*-inverseˡ p {p⋆≄0⇒∣↥p∣≢0 p p⋆≄0}) ⟩
  oneℝ             ∎))
  where open ≃-Reasoning

@0 ∣∣x∣-∣y∣∣≤∣x-y∣ : ∀ x y -> ∣ ∣ x ∣ - ∣ y ∣ ∣ ≤ ∣ x - y ∣
∣∣x∣-∣y∣∣≤∣x-y∣ x y = ≤-respˡ-≃ (≃-sym (∣x∣≃x⊔-x (∣ x ∣ - ∣ y ∣))) (x≤z∧y≤z⇒x⊔y≤z (left x y) right)
  where
    open ≤-Reasoning
    left : ∀ x y -> ∣ x ∣ - ∣ y ∣ ≤ ∣ x - y ∣
    left x y = begin
      ∣ x ∣ - ∣ y ∣             ≈⟨ +-congˡ (- ∣ y ∣) (∣-∣-cong (≃-sym
                                  (≃-trans (+-congʳ x (+-inverseˡ y)) (+-identityʳ x)))) ⟩
      ∣ x + (- y + y) ∣ - ∣ y ∣ ≤⟨ +-monoˡ-≤ (- ∣ y ∣)
                                  (≤-respˡ-≃ (∣-∣-cong (+-assoc x (- y) y)) (∣x+y∣≤∣x∣+∣y∣ (x - y) y)) ⟩
      ∣ x - y ∣ + ∣ y ∣ - ∣ y ∣ ≈⟨ ≃-trans (≃-trans
                                   (+-assoc ∣ x - y ∣ ∣ y ∣ (- ∣ y ∣))
                                   (+-congʳ ∣ x - y ∣ (+-inverseʳ ∣ y ∣)))
                                   (+-identityʳ ∣ x - y ∣) ⟩
      ∣ x - y ∣                  ∎

    right : - (∣ x ∣ - ∣ y ∣) ≤ ∣ x - y ∣
    right = begin
      - (∣ x ∣ - ∣ y ∣) ≈⟨ solve 2 (λ ∣x∣ ∣y∣ ->
                           ⊝ (∣x∣ ⊖ ∣y∣) ⊜ ∣y∣ ⊖ ∣x∣)
                           ≃-refl ∣ x ∣ ∣ y ∣ ⟩
      ∣ y ∣ - ∣ x ∣     ≤⟨ left y x ⟩
      ∣ y - x ∣         ≈⟨ ∣x-y∣≃∣y-x∣ y x ⟩
      ∣ x - y ∣          ∎

archimedeanℝ₂ : ∀ (x : ℝ) -> Positive x -> Σ0 ℕ λ n-1 -> (+ 1 / (suc n-1)) ⋆ < x
archimedeanℝ₂ x posx = nM1 :&: <-respˡ-≃ {x} {n⋆⁻¹} {(+ 1 / (suc nM1)) ⋆} ((⋆-distrib-⁻¹ (+ n / 1) n⋆≄0))
                          ((<-respʳ-≃ {n⋆⁻¹} {(xInv ⁻¹) this-x⁻¹≄0} {x} (⁻¹-involutive {x} xNeqZero this-x⁻¹≄0)
                          ((x<y∧posx,y⇒y⁻¹<x⁻¹ {xInv} {(+ n / 1) ⋆} (proj₂ arch) this-x⁻¹≄0 n⋆≄0 (posxThenPosxInv x xNeqZero posx)
                          (zeroLtxThenPosx (toReal (+ n / 1)) (pLtqThenToRealpLtToRealq (+ 0 / 1) (+ n / 1) (ℚP.positive⁻¹ tt)))))))
  where
    open ≤-Reasoning
    xNeqZero : x ≄ zeroℝ
    xNeqZero = Either.Right (posxThenZeroLtx x posx)
    xInv : ℝ
    xInv = x \< xNeqZero
    @0 this-x⁻¹≄0 : xInv ≄0
    this-x⁻¹≄0 = Either.either (λ x<0 -> Either.Left (x<0⇒x⁻¹<0 {x} xNeqZero x<0)) (λ 0<x -> Either.Right (0<x⇒0<x⁻¹ {x} xNeqZero 0<x)) xNeqZero
    arch : Σ0 ℕ λ (n-1 : ℕ) -> (+ (suc n-1) / 1) ⋆ > xInv
    arch = archimedeanℝ xInv
    nM1 : ℕ
    nM1 = proj₁ arch
    @0 n : ℕ
    n = suc nM1
    @0 n⋆≄0 : ((+ n / 1) ⋆) ≄0
    n⋆≄0 = (∣↥p∣≢0⇒p⋆≄0 (+ n / 1) tt)
    @0 n⋆⁻¹ : ℝ
    n⋆⁻¹ = (((+ n / 1) ⋆) ⁻¹) n⋆≄0
{-# COMPILE AGDA2HS archimedeanℝ₂ #-}

abstract
  fastArchimedeanℝ₂ : ∀ (x : ℝ) -> Positive x -> Σ0 ℕ λ n-1 -> (+ 1 / (suc n-1)) ⋆ < x
  fastArchimedeanℝ₂ = archimedeanℝ₂
  {-# COMPILE AGDA2HS fastArchimedeanℝ₂ #-}

@0 negx,y⇒posx*y : ∀ {x y} -> Negative x -> Negative y -> Positive (x * y)
negx,y⇒posx*y {x} {y} negx negy = posCong (negate x * negate y) (x * y)
                                  (solve 2 (λ x y -> ⊝ x ⊗ ⊝ y ⊜ x ⊗ y) ≃-refl x y)
                                  (posxAndyThenPosxTimesy (negate x) (negate y) negx negy)
  where open ≃-Reasoning

@0 negx∧posy⇒negx*y : ∀ {x y} -> Negative x -> Positive y -> Negative (x * y)
negx∧posy⇒negx*y {x} {y} negx posy = posCong _ (negate (x * y)) (≃-sym (neg-distribˡ-* x y)) (posxAndyThenPosxTimesy (negate x) y negx posy)

@0 x≄0∧y≄0⇒x*y≄0 : ∀ {x y} -> x ≄0 -> y ≄0 -> (x * y) ≄0
x≄0∧y≄0⇒x*y≄0 {x} {y} x≄0 y≄0 = Either.either (Either.either y<0∧x<0 0<y∧x<0 y≄0) (Either.either y<0∧0<x 0<y∧0<x y≄0) x≄0
  where
    y<0∧x<0 : y < zeroℝ -> x < zeroℝ -> (x * y) ≄0
    y<0∧x<0 y<0 x<0 = Either.Right (posxThenZeroLtx (x * y) (negx,y⇒posx*y (xLtZeroThenNegx x x<0) (xLtZeroThenNegx y y<0)))

    0<y∧x<0 : zeroℝ < y -> x < zeroℝ -> (x * y) ≄0
    0<y∧x<0 0<y x<0 = Either.Left (negxThenxLtZero (x * y) (negx∧posy⇒negx*y (xLtZeroThenNegx x x<0) (zeroLtxThenPosx y 0<y)))

    y<0∧0<x : y < zeroℝ -> zeroℝ < x -> (x * y) ≄0
    y<0∧0<x y<0 0<x = Either.Left (<-respˡ-≃ (*-comm y x) (negx⇒x<0 (negx∧posy⇒negx*y (xLtZeroThenNegx y y<0) (zeroLtxThenPosx x 0<x))))

    0<y∧0<x : zeroℝ < y -> zeroℝ < x -> (x * y) ≄0
    0<y∧0<x 0<y 0<x = Either.Right (posxThenZeroLtx (x * y) (posxAndyThenPosxTimesy x y (zeroLtxThenPosx x 0<x) (zeroLtxThenPosx y 0<y)))

@0 nonNegp⇒nonNegp⋆ : ∀ p -> ℚ.NonNegative p -> NonNegative (p ⋆)
nonNegp⇒nonNegp⋆ p nonp = nonNeg* (λ {(suc n-1) -> ℚP.≤-trans (ℚP.nonPositive⁻¹ _) (ℚP.nonNegative⁻¹ nonp)})

{-
{-
Note: We could obviously get ∣x∣ ≄0 from x≄0 (or vice versa). However, taking in the ∣x∣⁻¹≄0 allows the user to use any
proof that ∣x∣⁻¹ ≄0 instead of just the proof given by x≄0. If we have two distinct proofs of x ≄0,
say A and B, then (x ⁻¹) A ≡ (x ⁻¹) B does not hold by reflexivity, and probably doesn't hold in most
cases anyway. So if the user has a different ∣x∣ ≄0 proof they'd have to apply uniqueness of inverses,
which is more labour than supplying the ∣x∣ ≄0 proof since you have to supply a proof that 
((∣ x ∣ ⁻¹) C) * ∣ x ∣ ≃ oneℝ along with all of the *-cong's used to swap out ∣ x ∣ ⁻¹ A for ∣ x ∣ ⁻¹ C.
-}
@0 ∣x∣⁻¹≃∣x⁻¹∣ : ∀ {x} -> (∣x∣≄0 : ∣ x ∣ ≄0) -> (x≄0 : x ≄0) -> (∣ x ∣ ⁻¹) ∣x∣≄0 ≃ ∣ (x ⁻¹) x≄0 ∣
∣x∣⁻¹≃∣x⁻¹∣ {x} ∣x∣≄0 x≄0 = let ∣x∣⁻¹ = (∣ x ∣ ⁻¹) ∣x∣≄0; x⁻¹ = (x ⁻¹) x≄0 in begin
  ∣x∣⁻¹                     ≈⟨ ≃-sym (*-identityʳ ∣x∣⁻¹) ⟩
  ∣x∣⁻¹ * oneℝ                ≈⟨ *-congˡ {∣x∣⁻¹} (≃-sym (≃-trans (∣-∣-cong (*-inverseʳ x x≄0)) (nonNegx⇒∣x∣≃x (nonNegp⇒nonNegp⋆ 1ℚᵘ _)))) ⟩
  ∣x∣⁻¹ * ∣ x * x⁻¹ ∣       ≈⟨ *-congˡ {∣x∣⁻¹} (∣x*y∣≃∣x∣*∣y∣ x x⁻¹) ⟩
  ∣x∣⁻¹ * (∣ x ∣ * ∣ x⁻¹ ∣) ≈⟨ ≃-sym (*-assoc ∣x∣⁻¹ ∣ x ∣ ∣ x⁻¹ ∣) ⟩
  ∣x∣⁻¹ * ∣ x ∣ * ∣ x⁻¹ ∣   ≈⟨ *-congʳ {∣ x⁻¹ ∣} (*-inverseˡ ∣ x ∣ ∣x∣≄0) ⟩
  oneℝ * ∣ x⁻¹ ∣             ≈⟨ *-identityˡ ∣ x⁻¹ ∣ ⟩
  ∣ x⁻¹ ∣                   ∎
  where open ≃-Reasoning
-}

@0 x≄0⇒∣x∣≄0 : ∀ {x} -> x ≄0 -> ∣ x ∣ ≄0
x≄0⇒∣x∣≄0 {x} x≄0 = Either.Right (pos-cong (≃-sym (≃-trans (+-congʳ ∣ x ∣ (≃-sym 0≃-0)) (+-identityʳ ∣ x ∣))) (x≄0⇒pos∣x∣ x≄0))

-- Also gets stuck. So for now:
postulate @0 ⁻¹-distrib-* : ∀ {x y} -> (x≄0 : x ≄0) -> (y≄0 : y ≄0) -> (xy≄0 : (x * y) ≄0) -> 
               ((x * y) ⁻¹) xy≄0 ≃ ((x ⁻¹) x≄0) * ((y ⁻¹) y≄0)
{-
⁻¹-distrib-* {x} {y} x≄0 y≄0 xy≄0 = let x⁻¹ = (x ⁻¹) x≄0; y⁻¹ = (y ⁻¹) y≄0 in
                                    ≃-sym (⁻¹-unique (x⁻¹ * y⁻¹) (x * y) xy≄0 (begin
  x⁻¹ * y⁻¹ * (x * y)   ≈⟨ solve 4 (λ x y x⁻¹ y⁻¹ ->
                           x⁻¹ ⊗ y⁻¹ ⊗ (x ⊗ y) ⊜ x⁻¹ ⊗ (y⁻¹ ⊗ y ⊗ x))
                           ≃-refl x y x⁻¹ y⁻¹ ⟩
  x⁻¹ * (y⁻¹ * y * x)   ≈⟨ *-congˡ {x⁻¹} (*-congʳ {x} (*-inverseˡ y y≄0)) ⟩
  x⁻¹ * (oneℝ * x)        ≈⟨ *-congˡ {x⁻¹} (*-identityˡ x) ⟩
  x⁻¹ * x               ≈⟨ *-inverseˡ x x≄0 ⟩
  oneℝ                     ∎))
  where open ≃-Reasoning
-}

abstract
  @0 fast-⁻¹-distrib-* : ∀ {x y} -> (x≄0 : x ≄0) -> (y≄0 : y ≄0) -> (xy≄0 : (x * y) ≄0) -> 
                      ((x * y) ⁻¹) xy≄0 ≃ ((x ⁻¹) x≄0) * ((y ⁻¹) y≄0)
  fast-⁻¹-distrib-* {x} {y} x≄0 y≄0 xy≄0 = ⁻¹-distrib-* {x} {y} x≄0 y≄0 xy≄0

@0 ε-from-convergence : ∀ {xs : ℕ -> ℝ} -> (xₙ→ℓ : IsConvergent xs) ->
                ∀ ε -> Positive ε -> ∃0 λ (N-1 : ℕ) -> ∀ n -> n ℕ.≥ suc N-1 -> ∣ xs n - proj₁' xₙ→ℓ ∣ < ε
ε-from-convergence {xs} (ℓ :^: MkCon xₙ→ℓ) ε posε = let arch = fastArchimedeanℝ₂ ε posε; k = suc (proj₁ arch); N = suc (proj₁ (xₙ→ℓ k)) in
                                           ℕ.pred N :&: λ @0 {(suc n-1) n≥N -> let n = suc n-1 in begin-strict
  ∣ xs n - ℓ ∣ ≤⟨ proj₂ (xₙ→ℓ k) n n≥N ⟩
  (+ 1 / k) ⋆ <⟨ proj₂ arch ⟩
  ε            ∎}
  where open ≤-Reasoning

abstract
  @0 fast-ε-from-convergence : ∀ {xs : ℕ -> ℝ} -> (xₙ→ℓ : IsConvergent xs) ->
                       ∀ ε -> Positive ε -> ∃0 λ (N-1 : ℕ) -> ∀ n -> n ℕ.≥ suc N-1 -> ∣ xs n - proj₁' xₙ→ℓ ∣ < ε
  fast-ε-from-convergence = ε-from-convergence

@0 ¬negx⇒nonNegx : ∀ {x} -> ¬ (Negative x) -> NonNegative x
¬negx⇒nonNegx {x} hyp = 0≤x⇒nonNegx (≮⇒≥ (λ hyp2 -> hyp (pos-cong (+-identityˡ (- x)) hyp2)))

@0 nonNegx⇒¬negx : ∀ {x} -> NonNegative x -> ¬ (Negative x)
nonNegx⇒¬negx {x} (nonNeg* nonx) (MkPos (n-1 :&: negx)) = let n = suc n-1 in ℚP.<-irrefl (ℚP.≃-refl {ℚ.- (+ 1 / n)}) (begin-strict
  ℚ.- (+ 1 / n)     ≤⟨ nonx n ⟩
  seq x n           ≈⟨ ℚP.≃-sym (ℚP.neg-involutive (seq x n)) ⟩
  ℚ.- (ℚ.- seq x n) <⟨ ℚP.neg-mono-< negx ⟩
  ℚ.- (+ 1 / n)      ∎)
  where open ℚP.≤-Reasoning

@0 nonNegx∧x≄0⇒posx : ∀ {x} -> NonNegative x -> x ≄0 -> Positive x
nonNegx∧x≄0⇒posx {x} nonx x≄0 = zeroLtxThenPosx x (begin-strict
  zeroℝ    <⟨ posx⇒0<x (x≄0⇒pos∣x∣ x≄0) ⟩
  ∣ x ∣ ≈⟨ nonNegx⇒∣x∣≃x nonx ⟩
  x      ∎)
  where open ≤-Reasoning

@0 nonNegx⇒nonNegx⁻¹ : ∀ {x} -> NonNegative x -> (x≄0 : x ≄0) -> NonNegative ((x ⁻¹) x≄0)
nonNegx⇒nonNegx⁻¹ {x} nonx x≄0 = pos⇒nonNeg (posxThenPosxInv x x≄0 (nonNegx∧x≄0⇒posx {x} nonx x≄0))

{-
abstract
  @0 xₙ≄0∧x₀≄0⇒xₙ⁻¹→x₀⁻¹ : ∀ {xs : ℕ -> ℝ} -> ∀ {x₀ : ℝ} -> ConvergesTo xs x₀ -> (xₙ≄0 : ∀ n -> xs n ≄0) -> (x₀≄0 : x₀ ≄0) ->
                        (λ n -> (xs n ⁻¹) (xₙ≄0 n)) ConvergesTo (x₀ ⁻¹) x₀≄0
  xₙ≄0∧x₀≄0⇒xₙ⁻¹→x₀⁻¹ {xs} {x₀} (MkCon xₙ→x₀) xₙ≄0 x₀≄0 = MkCon main
    
    where
      open ≤-Reasoning
      main : ∀ k -> {k≢0 : k ≢0} -> ∃0 λ N-1 -> ∀ n -> n ℕ.≥ suc N-1 ->
             ∣ (xs n ⁻¹) (xₙ≄0 n) - (x₀ ⁻¹) x₀≄0 ∣ ≤ ((+ 1 / k) {k≢0}) ⋆
      main (suc k-1) = ℕ.pred N , sub
      
        where
          arch : ∃0 (λ n-1 → (mkℚᵘ (+ 1) n-1 ⋆ < (+ 1 / 2) ⋆ * ∣ x₀ ∣)) --had to add this
          arch = fastArchimedeanℝ₂ {(+ 1 / 2) ⋆ * ∣ x₀ ∣} (posxAndyThenPosxTimesy (posp⇒posp⋆ (+ 1 / 2) _) (x≄0⇒pos∣x∣ x₀≄0))
          
          r k : ℕ
          r = suc (proj₁ arch)
          k = suc k-1

          m₀-getter : ∃0 (λ N-1 → (n : ℕ) → n ℕ.≥ suc N-1 → ∣ xs n - x₀ ∣ < ((+ 1 / (2 ℕ.* (suc k-1))) ⋆ * (∣ x₀ ∣ * ∣ x₀ ∣))) --had to add this too
          m₀-getter = fast-ε-from-convergence (x₀ :^: MkCon xₙ→x₀) ((+ 1 / (2 ℕ.* k)) ⋆ * (∣ x₀ ∣ * ∣ x₀ ∣))
                      (posxAndyThenPosxTimesy (posp⇒posp⋆ (+ 1 / (2 ℕ.* k)) _)
                      (posxAndyThenPosxTimesy (x≄0⇒pos∣x∣ x₀≄0) (x≄0⇒pos∣x∣ x₀≄0)))
          
          m₀ n₀ N : ℕ
          m₀ = suc (proj₁ m₀-getter)
          n₀ = suc (proj₁ (xₙ→x₀ r))
          N = m₀ ℕ.⊔ n₀

          {-
            [1]
            Incredible optimization note!
            -------------------------------
            If you case split on n here to get n = suc m for some m∈ℕ, the typechecking (seemingly) never completes!
            If you leave it as is, the typechecking completes in reasonable time.
            Agda must be getting stuck on computing lots of extra things when n = suc m. Amazing!
          
            Despite this issue being solved, the addition of all of the implicit arguments below is a notable optimization, and will
            thus be kept.
          -}
          sub : ∀ n -> n ℕ.≥ N -> ∣ (xs n ⁻¹) (xₙ≄0 n) - (x₀ ⁻¹) x₀≄0 ∣ ≤ (+ 1 / suc k-1) ⋆
          sub n n≥N = begin
            ∣ xₙ⁻¹ - x₀⁻¹ ∣                          ≈⟨ ≃-trans {∣ xₙ⁻¹ - x₀⁻¹ ∣} {∣xₙ∣⁻¹ * ∣x₀∣⁻¹ * ∣ x₀ - xₙ ∣} {∣ x₀ - xₙ ∣ * (∣xₙ∣⁻¹ * ∣x₀∣⁻¹)}
                                                        part2 (*-comm (∣xₙ∣⁻¹ * ∣x₀∣⁻¹) ∣ x₀ - xₙ ∣) ⟩
            ∣ x₀ - xₙ ∣ * (∣xₙ∣⁻¹ * ∣x₀∣⁻¹)           ≤⟨ *-mono-≤ {∣ x₀ - xₙ ∣} {(+ 1 / (2 ℕ.* k)) ⋆ * (∣ x₀ ∣ * ∣ x₀ ∣)}
                                                         {∣xₙ∣⁻¹ * ∣x₀∣⁻¹} {2ℚᵘ ⋆ * (∣x₀∣⁻¹ * ∣x₀∣⁻¹)} 
                                                         (nonNeg∣x∣ (x₀ - xₙ)) 
                                                         (nonNegx,y⇒nonNegx*y {∣xₙ∣⁻¹} {∣x₀∣⁻¹} 
                                                         (nonNegx⇒nonNegx⁻¹ {∣ xₙ ∣} (nonNeg∣x∣ xₙ) ∣xₙ∣≄0) 
                                                         (nonNegx⇒nonNegx⁻¹ {∣ x₀ ∣} (nonNeg∣x∣ x₀) ∣x₀∣≄0)) 
                                                         (<⇒≤ {∣ x₀ - xₙ ∣} {(+ 1 / (2 ℕ.* k)) ⋆ * (∣ x₀ ∣ * ∣ x₀ ∣)} part4) 
                                                         (≤-respʳ-≃ {∣xₙ∣⁻¹ * ∣x₀∣⁻¹} {2ℚᵘ ⋆ * ∣x₀∣⁻¹ * ∣x₀∣⁻¹} {2ℚᵘ ⋆ * (∣x₀∣⁻¹ * ∣x₀∣⁻¹)}
                                                         (*-assoc (2ℚᵘ ⋆) ∣x₀∣⁻¹ ∣x₀∣⁻¹) 
                                                         (<⇒≤ {∣xₙ∣⁻¹ * ∣x₀∣⁻¹} {2ℚᵘ ⋆ * ∣x₀∣⁻¹ * ∣x₀∣⁻¹}
                                                         (*-monoˡ-<-pos {∣x₀∣⁻¹} (posxThenPosxInv {∣ x₀ ∣} ∣x₀∣≄0 (x≄0⇒pos∣x∣ {x₀} x₀≄0))
                                                         {∣xₙ∣⁻¹} {2ℚᵘ ⋆ * ∣x₀∣⁻¹} part3))) ⟩
            (+ 1 / (2 ℕ.* k)) ⋆ * (∣ x₀ ∣ * ∣ x₀ ∣) *
            (2ℚᵘ ⋆ * (∣x₀∣⁻¹ * ∣x₀∣⁻¹))                 ≈⟨ solve 4 (λ 1/2k ∣x₀∣ 2ℚ ∣x₀∣⁻¹ ->
                                                           1/2k ⊗ (∣x₀∣ ⊗ ∣x₀∣) ⊗ (2ℚ ⊗ (∣x₀∣⁻¹ ⊗ ∣x₀∣⁻¹)) ⊜
                                                           1/2k ⊗ (∣x₀∣ ⊗ ∣x₀∣ ⊗ (∣x₀∣⁻¹ ⊗ ∣x₀∣⁻¹) ⊗ 2ℚ))
                                                           ≃-refl ((+ 1 / (2 ℕ.* k)) ⋆) ∣ x₀ ∣ (2ℚᵘ ⋆) ∣x₀∣⁻¹ ⟩
            (+ 1 / (2 ℕ.* k)) ⋆ * (∣ x₀ ∣ * ∣ x₀ ∣ *
            (∣x₀∣⁻¹ * ∣x₀∣⁻¹) * 2ℚᵘ ⋆)                  ≈⟨ *-congˡ {(+ 1 / (2 ℕ.* k)) ⋆} {∣ x₀ ∣ * ∣ x₀ ∣ * (∣x₀∣⁻¹ * ∣x₀∣⁻¹) * 2ℚᵘ ⋆}
                                                          {oneℝ * 2ℚᵘ ⋆} (*-congʳ {2ℚᵘ ⋆} {∣ x₀ ∣ * ∣ x₀ ∣ * (∣x₀∣⁻¹ * ∣x₀∣⁻¹)} {oneℝ} part5) ⟩
            (+ 1 / (2 ℕ.* k)) ⋆ * (oneℝ * 2ℚᵘ ⋆)         ≈⟨ ≃-trans {(+ 1 / (2 ℕ.* k)) ⋆ * (oneℝ * 2ℚᵘ ⋆)} {(+ 1 / (2 ℕ.* k)) ⋆ * (2ℚᵘ ⋆)}
                                                          {(+ 1 / (2 ℕ.* k) ℚ.* 2ℚᵘ) ⋆}
                                                          (*-congˡ {(+ 1 / (2 ℕ.* k)) ⋆} {oneℝ * 2ℚᵘ ⋆} {2ℚᵘ ⋆} (*-identityˡ (2ℚᵘ ⋆))) 
                                                          (≃-sym {(+ 1 / (2 ℕ.* k) ℚ.* 2ℚᵘ) ⋆} {(+ 1 / (2 ℕ.* k)) ⋆ * 2ℚᵘ ⋆}
                                                          (⋆-distrib-* (+ 1 / (2 ℕ.* k)) 2ℚᵘ)) ⟩
            (+ 1 / (2 ℕ.* k) ℚ.* 2ℚᵘ) ⋆                ≈⟨ ⋆-cong {+ 1 / (2 ℕ.* k) ℚ.* 2ℚᵘ} {+ 1 / k} (ℚ.*≡* (ℤsolve 1 (λ k ->
                                                          ℤΚ (+ 1) :* ℤΚ (+ 2) :* k := ℤΚ (+ 1) :* (ℤΚ (+ 2) :* k :* ℤΚ (+ 1)))
                                                          refl (+ k))) ⟩
            (+ 1 / k) ⋆                                 ∎
           
            
            where
              --maybe the main problem was here; it hung until the types were added
              xₙ xₙ⁻¹ x₀⁻¹ : ℝ
              xₙ = xs n
              xₙ⁻¹ = (xₙ ⁻¹) (xₙ≄0 n)
              x₀⁻¹ = (x₀ ⁻¹) x₀≄0

              ∣xₙ∣≄0 : ∣ xₙ ∣ ≄0
              ∣xₙ∣≄0 = x≄0⇒∣x∣≄0 (xₙ≄0 n)
              ∣x₀∣≄0 : ∣ x₀ ∣ ≄0
              ∣x₀∣≄0 = x≄0⇒∣x∣≄0 x₀≄0
              
              ∣xₙ∣⁻¹ ∣x₀∣⁻¹ : ℝ
              ∣xₙ∣⁻¹ = (∣ xₙ ∣ ⁻¹) ∣xₙ∣≄0
              ∣x₀∣⁻¹ = (∣ x₀ ∣ ⁻¹) ∣x₀∣≄0

              2⁻¹∣x₀∣<∣xₙ∣ : (+ 1 / 2) ⋆ * ∣ x₀ ∣ < ∣ xₙ ∣
              2⁻¹∣x₀∣<∣xₙ∣ = begin-strict
                (+ 1 / 2) ⋆ * ∣ x₀ ∣            ≈⟨ solve 1 (λ ∣x₀∣ ->
                                                   Κ (1ℚᵘ ℚ.- (+ 1 / 2)) ⊗ ∣x₀∣ ⊜ ∣x₀∣ ⊖ Κ (+ 1 / 2) ⊗ ∣x₀∣)
                                                   ≃-refl ∣ x₀ ∣ ⟩
                ∣ x₀ ∣ - (+ 1 / 2) ⋆ * ∣ x₀ ∣   <⟨ +-monoʳ-< ∣ x₀ ∣ (neg-mono-< (<-respˡ-≃ (∣x-y∣≃∣y-x∣ xₙ x₀)
                                                   (≤-<-trans (proj₂ (xₙ→x₀ r) n (ℕP.≤-trans (ℕP.m≤n⊔m m₀ n₀) n≥N))
                                                   (proj₂ arch)))) ⟩
                ∣ x₀ ∣ - ∣ x₀ - xₙ ∣            ≤⟨ x≤∣x∣ ⟩
                ∣ ∣ x₀ ∣ - ∣ x₀ - xₙ ∣ ∣        ≤⟨ ∣∣x∣-∣y∣∣≤∣x-y∣ x₀ (x₀ - xₙ) ⟩
                ∣ x₀ - (x₀ - xₙ) ∣              ≈⟨ ∣-∣-cong (solve 2 (λ xₙ x₀ ->
                                                   x₀ ⊖ (x₀ ⊖ xₙ) ⊜ xₙ)
                                                   ≃-refl xₙ x₀) ⟩
                ∣ xₙ ∣                          ∎

              part1 : xₙ⁻¹ - x₀⁻¹ ≃ xₙ⁻¹ * x₀⁻¹ * (x₀ - xₙ)
              part1 = ≃-sym (begin-equality
                xₙ⁻¹ * x₀⁻¹ * (x₀ - xₙ)                 ≈⟨ *-distribˡ-+ (xₙ⁻¹ * x₀⁻¹) x₀ (- xₙ) ⟩
                xₙ⁻¹ * x₀⁻¹ * x₀ + xₙ⁻¹ * x₀⁻¹ * (- xₙ) ≈⟨ +-cong
                                                           (≃-trans (≃-trans
                                                                    (*-assoc xₙ⁻¹ x₀⁻¹ x₀)
                                                                    (*-congˡ {xₙ⁻¹} (*-inverseˡ x₀ x₀≄0)))
                                                                    (*-identityʳ xₙ⁻¹))
                                                           (≃-sym (neg-distribʳ-* (xₙ⁻¹ * x₀⁻¹) xₙ)) ⟩
                xₙ⁻¹ - xₙ⁻¹ * x₀⁻¹ * xₙ                 ≈⟨ ≃-trans (≃-trans
                                                           (solve 3 (λ xₙ xₙ⁻¹ x₀⁻¹ ->
                                                            xₙ⁻¹ ⊖ xₙ⁻¹ ⊗ x₀⁻¹ ⊗ xₙ ⊜ xₙ⁻¹ ⊕ (⊝ x₀⁻¹) ⊗ (xₙ⁻¹ ⊗ xₙ))
                                                            ≃-refl xₙ xₙ⁻¹ x₀⁻¹)
                                                           (+-congʳ xₙ⁻¹ (*-congˡ { - x₀⁻¹} (*-inverseˡ xₙ (xₙ≄0 n)))))
                                                           (+-congʳ xₙ⁻¹ (*-identityʳ (- x₀⁻¹))) ⟩
                xₙ⁻¹ - x₀⁻¹                              ∎)

              part2 : ∣ xₙ⁻¹ - x₀⁻¹ ∣ ≃ ∣xₙ∣⁻¹ * ∣x₀∣⁻¹ * ∣ x₀ - xₙ ∣
              part2 = begin-equality
                ∣ xₙ⁻¹ - x₀⁻¹ ∣                   ≈⟨ ∣-∣-cong part1 ⟩
                ∣ xₙ⁻¹ * x₀⁻¹ * (x₀ - xₙ) ∣       ≈⟨ ∣x*y∣≃∣x∣*∣y∣ (xₙ⁻¹ * x₀⁻¹) (x₀ - xₙ) ⟩
                ∣ xₙ⁻¹ * x₀⁻¹ ∣ * ∣ x₀ - xₙ ∣     ≈⟨ *-congʳ {∣ x₀ - xₙ ∣} (∣x*y∣≃∣x∣*∣y∣ xₙ⁻¹ x₀⁻¹) ⟩
                ∣ xₙ⁻¹ ∣ * ∣ x₀⁻¹ ∣ * ∣ x₀ - xₙ ∣ ≈⟨ *-congʳ {∣ x₀ - xₙ ∣} (≃-sym (*-cong
                                                    (∣x∣⁻¹≃∣x⁻¹∣ {xₙ} ∣xₙ∣≄0 (xₙ≄0 n))
                                                    (∣x∣⁻¹≃∣x⁻¹∣ {x₀} ∣x₀∣≄0 x₀≄0))) ⟩
                ∣xₙ∣⁻¹ * ∣x₀∣⁻¹ * ∣ x₀ - xₙ ∣      ∎

              part3 : ∣xₙ∣⁻¹ < 2ℚᵘ ⋆ * ∣x₀∣⁻¹
              part3 = let 2⁻¹≄0 = ∣↥p∣≢0⇒p⋆≄0 (+ 1 / 2) _
                                ; 2⁻¹∣x₀∣≄0 = x≄0∧y≄0⇒x*y≄0 {(+ 1 / 2) ⋆} {∣ x₀ ∣} 2⁻¹≄0 ∣x₀∣≄0 in begin-strict
                    ∣xₙ∣⁻¹                                           <⟨ x<y∧posx,y⇒y⁻¹<x⁻¹ {(+ 1 / 2) ⋆ * ∣ x₀ ∣} {∣ xₙ ∣}
                                                                        2⁻¹∣x₀∣<∣xₙ∣ 2⁻¹∣x₀∣≄0 ∣xₙ∣≄0
                                                                        (posxAndyThenPosxTimesy {(+ 1 / 2) ⋆} {∣ x₀ ∣}
                                                                        (posp⇒posp⋆ (+ 1 / 2) _) (x≄0⇒pos∣x∣ {x₀} x₀≄0))
                                                                        (x≄0⇒pos∣x∣ {xₙ} (xₙ≄0 n)) ⟩
                    (((+ 1 / 2) ⋆ * ∣ x₀ ∣) ⁻¹) 2⁻¹∣x₀∣≄0            ≈⟨ ⁻¹-distrib-* {(+ 1 / 2) ⋆} {∣ x₀ ∣} 2⁻¹≄0 ∣x₀∣≄0 2⁻¹∣x₀∣≄0 ⟩
                    (((+ 1 / 2) ⋆) ⁻¹) 2⁻¹≄0 * ∣x₀∣⁻¹                ≈⟨ *-congʳ {∣x₀∣⁻¹} (⋆-distrib-⁻¹ (+ 1 / 2) 2⁻¹≄0) ⟩
                    2ℚᵘ ⋆ * ∣x₀∣⁻¹                                    ∎

              part4 : ∣ x₀ - xₙ ∣ < (+ 1 / (2 ℕ.* (suc k-1))) ⋆ * (∣ x₀ ∣ * ∣ x₀ ∣)
              part4 = begin-strict
                ∣ x₀ - xₙ ∣                             ≈⟨ ∣x-y∣≃∣y-x∣ x₀ xₙ ⟩
                ∣ xₙ - x₀ ∣                             <⟨ proj₂ m₀-getter n (ℕP.≤-trans (ℕP.m≤m⊔n m₀ n₀) n≥N) ⟩
                (+ 1 / (2 ℕ.* k)) ⋆ * (∣ x₀ ∣ * ∣ x₀ ∣)   ∎

              part5 : (∣ x₀ ∣ * ∣ x₀ ∣) * (∣x₀∣⁻¹ * ∣x₀∣⁻¹) ≃ oneℝ
              part5 = begin-equality
                (∣ x₀ ∣ * ∣ x₀ ∣) * (∣x₀∣⁻¹ * ∣x₀∣⁻¹)   ≈⟨ solve 2 (λ ∣x₀∣ ∣x₀∣⁻¹ ->
                                                          (∣x₀∣ ⊗ ∣x₀∣) ⊗ (∣x₀∣⁻¹ ⊗ ∣x₀∣⁻¹) ⊜
                                                          (∣x₀∣ ⊗ ∣x₀∣⁻¹) ⊗ (∣x₀∣ ⊗ ∣x₀∣⁻¹))
                                                          ≃-refl ∣ x₀ ∣ ∣x₀∣⁻¹ ⟩
                (∣ x₀ ∣ * ∣x₀∣⁻¹) * (∣ x₀ ∣ * ∣x₀∣⁻¹)   ≈⟨ *-cong {∣ x₀ ∣ * ∣x₀∣⁻¹} {oneℝ} {∣ x₀ ∣ * ∣x₀∣⁻¹} {oneℝ}
                                                           (*-inverseʳ ∣ x₀ ∣ ∣x₀∣≄0) (*-inverseʳ ∣ x₀ ∣ ∣x₀∣≄0) ⟩
                oneℝ * oneℝ                                ≈⟨ *-identityʳ oneℝ ⟩
                oneℝ                                      ∎
-}

@0 ∣xₙ∣→∣x₀∣ : ∀ {xs : ℕ -> ℝ} -> (x→x₀ : IsConvergent xs) -> ConvergesTo (λ n -> ∣ xs n ∣) ∣ proj₁' x→x₀ ∣
∣xₙ∣→∣x₀∣ {xs} (x₀ :^: MkCon x→x₀) = MkCon λ @0 {(suc k-1) -> let k = suc k-1 in
                                  proj₁ (x→x₀ k) :&: λ @0 {(suc n-1) n≥N -> let n = suc n-1 in begin
  ∣ ∣ xs n ∣ - ∣ x₀ ∣ ∣ ≤⟨ ∣∣x∣-∣y∣∣≤∣x-y∣ (xs n) x₀ ⟩
  ∣ xs n - x₀ ∣        ≤⟨ proj₂ (x→x₀ k) n n≥N ⟩
  (+ 1 / k) ⋆           ∎}}
  where open ≤-Reasoning

@0 0≤x⇒∣x∣≃x : ∀ {x} -> zeroℝ ≤ x -> ∣ x ∣ ≃ x
0≤x⇒∣x∣≃x {x} 0≤x = nonNegx⇒∣x∣≃x (nonNeg-cong (≃-trans (+-congʳ x (≃-sym 0≃-0)) (+-identityʳ x)) 0≤x)

@0 x≤y⇒0≤y-x : ∀ {x y} -> x ≤ y -> zeroℝ ≤ y - x
x≤y⇒0≤y-x {x} {y} x≤y = nonNeg-cong (≃-sym (≃-trans (+-congʳ (y - x) (≃-sym 0≃-0)) (+-identityʳ (y - x)))) x≤y

@0 xₙ≤yₙ⇒x₀≤y₀ : ∀ {xs ys : ℕ -> ℝ} -> ∀ {x₀ y₀ : ℝ} -> ConvergesTo xs x₀ -> ConvergesTo ys y₀ ->
              (∀ n -> {n ≢0} -> xs n ≤ ys n) -> x₀ ≤ y₀
xₙ≤yₙ⇒x₀≤y₀ {xs} {ys} {x₀} {y₀} (MkCon xₙ→x₀) (MkCon yₙ→y₀) xₙ≤yₙ = 0≤y-x⇒x≤y (begin
  zeroℝ          ≤⟨ 0≤∣x∣ (y₀ - x₀) ⟩
  ∣ y₀ - x₀ ∣ ≈⟨ uniqueness-of-limits (∣xₙ∣→∣x₀∣ (y₀ - x₀ :^: yₙ-xₙ→y₀-x₀))
                 (equalMembersEqualLimits (λ @0 {(suc n-1) -> let n = suc n-1 in
                 ≃-sym (0≤x⇒∣x∣≃x (x≤y⇒0≤y-x (xₙ≤yₙ n)))}) (y₀ - x₀ :^: yₙ-xₙ→y₀-x₀)) ⟩
  y₀ - x₀      ∎)
  where
    open ≤-Reasoning
    yₙ-xₙ→y₀-x₀ = limitOfSum (y₀ :^: MkCon yₙ→y₀) (- x₀ :^: limitOfNegate (x₀ :^: MkCon xₙ→x₀))

private
  @0 x-y≤z⇒x≤z+y : ∀ {x y z} -> x - y ≤ z -> x ≤ z + y
  x-y≤z⇒x≤z+y {x} {y} {z} x-y≤z = begin
    x         ≈⟨ solve 2 (λ x y -> x ⊜ x ⊖ y ⊕ y) ≃-refl x y ⟩
    x - y + y ≤⟨ +-monoˡ-≤ y x-y≤z ⟩
    z + y      ∎
    where open ≤-Reasoning

  @0 ∣x⊔y-z⊔w∣≤∣x-z∣⊔∣y-w∣ : ∀ x y z w -> ∣ x ⊔ y - (z ⊔ w) ∣ ≤ ∣ x - z ∣ ⊔ ∣ y - w ∣
  ∣x⊔y-z⊔w∣≤∣x-z∣⊔∣y-w∣ x y z w = ≤-respˡ-≃ (≃-sym (∣x∣≃x⊔-x (x ⊔ y - (z ⊔ w))))
                                (x≤z∧y≤z⇒x⊔y≤z
                                (lem x y (z ⊔ w) (∣ x - z ∣ ⊔ ∣ y - w ∣) part1 part2)
                                (≤-respˡ-≃ (solve 2 (λ x⊔y z⊔w ->
                                           z⊔w ⊖ x⊔y ⊜ (⊝ (x⊔y ⊖ z⊔w))) ≃-refl (x ⊔ y) (z ⊔ w))
                                           (lem z w (x ⊔ y) (∣ x - z ∣ ⊔ ∣ y - w ∣) part3 part4)))
    where
      open ≤-Reasoning
      lem : ∀ x y z w -> x - z ≤ w -> y - z ≤ w -> x ⊔ y - z ≤ w
      lem x y z w x-z≤w y-z≤w = begin
        x ⊔ y - z ≤⟨ +-monoˡ-≤ (- z) (x≤z∧y≤z⇒x⊔y≤z
                     (x-y≤z⇒x≤z+y x-z≤w)
                     (x-y≤z⇒x≤z+y y-z≤w)) ⟩
        w + z - z ≈⟨ solve 2 (λ w z -> w ⊕ z ⊖ z ⊜ w) ≃-refl w z ⟩
        w          ∎

      part1 : x - (z ⊔ w) ≤ ∣ x - z ∣ ⊔ ∣ y - w ∣
      part1 = begin
        x - (z ⊔ w)           ≤⟨ +-monoʳ-≤ x (neg-mono-≤ (x≤x⊔y z w)) ⟩
        x - z                 ≤⟨ x≤∣x∣ ⟩
        ∣ x - z ∣             ≤⟨ x≤x⊔y ∣ x - z ∣ ∣ y - w ∣ ⟩
        ∣ x - z ∣ ⊔ ∣ y - w ∣   ∎

      part2 : y - (z ⊔ w) ≤ ∣ x - z ∣ ⊔ ∣ y - w ∣ 
      part2 = begin
        y - (z ⊔ w)           ≤⟨ +-monoʳ-≤ y (neg-mono-≤ (x≤y⊔x w z)) ⟩
        y - w                 ≤⟨ x≤∣x∣ ⟩
        ∣ y - w ∣             ≤⟨ x≤y⊔x ∣ y - w ∣ ∣ x - z ∣ ⟩
        ∣ x - z ∣ ⊔ ∣ y - w ∣   ∎

      part3 : z - (x ⊔ y) ≤ ∣ x - z ∣ ⊔ ∣ y - w ∣
      part3 = begin
        z - (x ⊔ y)           ≤⟨ +-monoʳ-≤ z (neg-mono-≤ (x≤x⊔y x y)) ⟩
        z - x                 ≤⟨ x≤∣x∣ ⟩
        ∣ z - x ∣             ≈⟨ ∣x-y∣≃∣y-x∣ z x ⟩
        ∣ x - z ∣             ≤⟨ x≤x⊔y ∣ x - z ∣ ∣ y - w ∣ ⟩
        ∣ x - z ∣ ⊔ ∣ y - w ∣   ∎

      part4 : w - (x ⊔ y) ≤ ∣ x - z ∣ ⊔ ∣ y - w ∣
      part4 = begin
        w - (x ⊔ y)           ≤⟨ +-monoʳ-≤ w (neg-mono-≤ (x≤y⊔x y x)) ⟩
        w - y                 ≤⟨ x≤∣x∣ ⟩
        ∣ w - y ∣             ≈⟨ ∣x-y∣≃∣y-x∣ w y ⟩
        ∣ y - w ∣             ≤⟨ x≤y⊔x ∣ y - w ∣ ∣ x - z ∣ ⟩
        ∣ x - z ∣ ⊔ ∣ y - w ∣   ∎

@0 xₙ⊔yₙ→x₀⊔y₀ : ∀ {xs ys : ℕ -> ℝ} -> (xₙ→x₀ : IsConvergent xs) -> (yₙ→y₀ : IsConvergent ys) ->
              ConvergesTo (λ n -> xs n ⊔ ys n) (proj₁' xₙ→x₀ ⊔ proj₁' yₙ→y₀)
xₙ⊔yₙ→x₀⊔y₀ {xs} {ys} (x₀ :^: MkCon xₙ→x₀) (y₀ :^: MkCon yₙ→y₀) = MkCon (λ @0 {(suc k-1) ->
                      let k = suc k-1; N₁ = suc (proj₁ (xₙ→x₀ k)); N₂ = suc (proj₁ (yₙ→y₀ k)) in
                      ℕ.pred (N₁ ℕ.⊔ N₂) :&: λ @0 {(suc n-1) n≥N -> let n = suc n-1 in begin
  ∣ xs n ⊔ ys n - (x₀ ⊔ y₀) ∣   ≤⟨ ∣x⊔y-z⊔w∣≤∣x-z∣⊔∣y-w∣ (xs n) (ys n) x₀ y₀ ⟩
  ∣ xs n - x₀ ∣ ⊔ ∣ ys n - y₀ ∣ ≤⟨ x≤z∧y≤z⇒x⊔y≤z
                                  (proj₂ (xₙ→x₀ k) n (ℕP.≤-trans (ℕP.m≤m⊔n N₁ N₂) n≥N))
                                  (proj₂ (yₙ→y₀ k) n (ℕP.≤-trans (ℕP.m≤n⊔m N₁ N₂) n≥N)) ⟩
  (+ 1 / k) ⋆                    ∎}})
  where open ≤-Reasoning

seriesOfFrom : (ℕ -> ℝ) -> ℕ -> (ℕ -> ℝ)
seriesOfFrom = sum                  -- Actually, it will only be an alias for sum.
{-# COMPILE AGDA2HS seriesOfFrom #-}

-- The old version (but with a lowercase start):
@0 seriesOf_From_ : (ℕ -> ℝ) -> ℕ -> (ℕ -> ℝ)
(seriesOf xs From i) n = seriesOfFrom xs i n

-- Here, it cannot begin with a capital letter.
seriesOf : (ℕ -> ℝ) -> (ℕ -> ℝ)
seriesOf xs = seriesOfFrom xs 0
{-# COMPILE AGDA2HS seriesOf #-}

@0 limitShifting : ∀ xs -> ∀ k m n -> sum xs m k ≃ sum xs n k + sum xs m n
limitShifting xs k zero zero = ≃-sym (+-identityʳ (sum0 xs k))
limitShifting xs k zero (suc n) = solve 2 (λ a b -> a ⊜ a ⊖ b ⊕ b) ≃-refl (sum0 xs k) (sum0 xs (suc n))
limitShifting xs k (suc m) zero = solve 2 (λ a b -> a ⊖ b ⊜ a ⊕ (Κ 0ℚᵘ ⊖ b)) ≃-refl (sum0 xs k) (sum0 xs (suc m))
limitShifting xs k (suc m) (suc n) = solve 3 (λ a b c -> a ⊖ b ⊜ a ⊖ c ⊕ (c ⊖ b)) ≃-refl (sum0 xs k) (sum0 xs (suc m)) (sum0 xs (suc n))

@0 lowerLimitShiftPreservesConvergence : ∀ xs -> (∃0 λ n -> IsConvergent (seriesOf xs From n)) -> ∀ m -> IsConvergent (seriesOf xs From m)
lowerLimitShiftPreservesConvergence xs (n :&: (ℓ :^: MkCon hyp)) m = ℓ + sum xs m n :^: equalMembersEqualLimits (λ @0 {(suc k-1) -> let k = suc k-1 in
                                 ≃-sym (limitShifting xs k m n)}) (ℓ + sum xs m n :^:
                                 limitOfSum {seriesOf xs From n} {λ r -> sum xs m n} (ℓ :^: MkCon hyp) (sum xs m n :^: limitOfConst (λ @0 {(suc r-1) -> ≃-refl})))

cauchyConvergenceTestIf : ∀ xs -> IsConvergent (seriesOf xs) ->
                           ∀ k -> {@0 k≢0 : k ≢0} -> Σ0 ℕ λ Nₖ-1 -> ∀ m n -> m ℕ.≥ suc Nₖ-1 -> n ℕ.≥ suc Nₖ-1 ->
                           ∣ sum xs m n ∣ ≤ ((+ 1 / k) {k≢0}) ⋆
cauchyConvergenceTestIf xs (ℓ :^: MkCon hyp) k {k≢0} = proj₁ (hyp (2 ℕ.* k) {2k≢0 k≢0}) :&: theProof k {k≢0}
  where
  @0 2k≢0 : ∀ {k : ℕ} -> @0 k ≢0 -> 2 ℕ.* k ≢0
  2k≢0 {suc k-1} _ = tt
  -- when the type checker moans about unsolved metas, first check them in the type signature;
  -- even if the error message points to another place
  @0 theProof : ∀ (k : ℕ) {k≢0 : k ≢0} -> ∀ m n -> m ℕ.≥ suc (proj₁ (hyp (2 ℕ.* k) {2k≢0 k≢0})) -> n ℕ.≥ suc (proj₁ (hyp (2 ℕ.* k) {2k≢0 k≢0})) ->
                           ∣ sum xs m n ∣ ≤ ((+ 1 / k) {k≢0}) ⋆
  theProof (suc k-1) (suc m-1) (suc n-1) m≥N₂ₖ n≥N₂ₖ = let k = suc k-1; N₂ₖ = suc (proj₁ (hyp (2 ℕ.* k))); m = suc m-1; n = suc n-1 in
    begin
    ∣ sum0 xs n - sum0 xs m ∣                     ≈⟨ ∣-∣-cong (solve 3 (λ a b c -> a ⊖ b ⊜ a ⊖ c ⊕ (c ⊖ b))
                                                 ≃-refl (sum0 xs n) (sum0 xs m) ℓ) ⟩
    ∣ sum0 xs n - ℓ + (ℓ - sum0 xs m) ∣            ≤⟨ ∣x+y∣≤∣x∣+∣y∣ (sum0 xs n - ℓ) (ℓ - sum0 xs m) ⟩
    ∣ sum0 xs n - ℓ ∣ + ∣ ℓ - sum0 xs m ∣          ≤⟨ +-mono-≤
                                                   (proj₂ (hyp (2 ℕ.* k)) n n≥N₂ₖ)
                                                 (≤-respˡ-≃ (∣x-y∣≃∣y-x∣ (sum0 xs m) ℓ) (proj₂ (hyp (2 ℕ.* k)) m m≥N₂ₖ)) ⟩
    (+ 1 / (2 ℕ.* k)) ⋆ + (+ 1 / (2 ℕ.* k)) ⋆ ≈⟨ ≃-trans
                                                 (≃-sym (⋆-distrib-+ (+ 1 / (2 ℕ.* k)) (+ 1 / (2 ℕ.* k))))
                                                 (⋆-cong (ℚ.*≡* (ℤsolve 1 (λ k ->
                                                 (ℤΚ (+ 1) :* (ℤΚ (+ 2) :* k) :+ ℤΚ (+ 1) :* (ℤΚ (+ 2) :* k)) :* k :=
                                                 ℤΚ (+ 1) :* (ℤΚ (+ 2) :* k :* (ℤΚ (+ 2) :* k)))
                                                 refl (+ k)))) ⟩
    (+ 1 / k) ⋆                                ∎
    where open ≤-Reasoning
{-# COMPILE AGDA2HS cauchyConvergenceTestIf #-}

@0 cauchyConvergenceTestOnlyIf : ∀ xs ->
                               (∀ k -> {k≢0 : k ≢0} -> ∃0 λ Nₖ-1 -> ∀ m n -> m ℕ.≥ suc Nₖ-1 -> n ℕ.≥ suc Nₖ-1 ->
                                       ∣ sum xs m n ∣ ≤ ((+ 1 / k) {k≢0}) ⋆) ->
                               IsConvergent (seriesOf xs)
cauchyConvergenceTestOnlyIf xs hyp = fastCauchyToConvergent (seriesOf xs) (MkCauchy (λ @0 {(suc k-1) -> let k = suc k-1; Mₖ = suc (proj₁ (hyp k)) in
                                      ℕ.pred Mₖ :&: λ @0 {(suc m-1) (suc n-1) m≥Mₖ n≥Mₖ -> let m = suc m-1; n = suc n-1 in begin
  ∣ sum xs 0 m - sum xs 0 n ∣                   ≈⟨ ≃-refl ⟩
  ∣ sum xs n m ∣                              ≤⟨ proj₂ (hyp k) n m n≥Mₖ m≥Mₖ ⟩
  (+ 1 / k) ⋆                                ∎}}))
  where open ≤-Reasoning

@0 sumxₙisConvergent⇒xₙ→0 : ∀ xs -> IsConvergent (seriesOf xs) -> ConvergesTo xs zeroℝ
sumxₙisConvergent⇒xₙ→0 xs (ℓ :^: MkCon sumxₙ→ℓ) = MkCon (λ @0 {(suc k-1) -> let k = suc k-1; N₂ₖ = suc (proj₁ (sumxₙ→ℓ (2 ℕ.* k))) in
                                          ℕ.pred N₂ₖ :&: λ @0 {(suc n-1) n≥N₂ₖ -> let n = suc n-1; n+1 = suc n in begin
  ∣ xs n - zeroℝ ∣                             ≈⟨ ∣-∣-cong (solve 3 (λ sum0ⁿxᵢ xₙ ℓ ->
                                               xₙ ⊖ Κ 0ℚᵘ ⊜ (sum0ⁿxᵢ ⊕ xₙ) ⊖ ℓ ⊕ (ℓ ⊖ sum0ⁿxᵢ))
                                               ≃-refl (sum0 xs n) (xs n) ℓ) ⟩
  ∣ sum0 xs n+1 - ℓ + (ℓ - sum0 xs n) ∣          ≤⟨ ∣x+y∣≤∣x∣+∣y∣ (sum0 xs n+1 - ℓ) (ℓ - sum0 xs n) ⟩
  ∣ sum0 xs n+1 - ℓ ∣ + ∣ ℓ - sum0 xs n ∣        ≤⟨ +-mono-≤
                                               (proj₂ (sumxₙ→ℓ (2 ℕ.* k)) n+1 (ℕP.≤-trans n≥N₂ₖ (ℕP.n≤1+n n)))
                                               (≤-respˡ-≃ (∣x-y∣≃∣y-x∣ (sum0 xs n) ℓ) (proj₂ (sumxₙ→ℓ (2 ℕ.* k)) n n≥N₂ₖ)) ⟩
  (+ 1 / (2 ℕ.* k)) ⋆ + (+ 1 / (2 ℕ.* k)) ⋆ ≈⟨ ≃-trans
                                               (≃-sym (⋆-distrib-+ (+ 1 / (2 ℕ.* k)) (+ 1 / (2 ℕ.* k))))
                                               (⋆-cong (ℚ.*≡* (ℤsolve 1 (λ k ->
                                               (ℤΚ (+ 1) :* (ℤΚ (+ 2) :* k) :+ ℤΚ (+ 1) :* (ℤΚ (+ 2) :* k)) :* k :=
                                               ℤΚ (+ 1) :* (ℤΚ (+ 2) :* k :* (ℤΚ (+ 2) :* k)))
                                               refl (+ k)))) ⟩
  (+ 1 / k) ⋆                                ∎}})
  where open ≤-Reasoning

SeriesConvergesAbsolutely : @0 (ℕ -> ℝ) -> Set
SeriesConvergesAbsolutely xs = IsConvergent (seriesOf (λ k -> ∣ xs k ∣))
{-# COMPILE AGDA2HS SeriesConvergesAbsolutely #-}

{-
Changing termination depth doesn't help fix this weird lem recursion problem (tried different depths up to 10).
-}
@0 sum-cong : ∀ {xs ys : ℕ -> ℝ} -> (∀ n -> xs n ≃ ys n) -> ∀ m n -> sum xs m n ≃ sum ys m n
{-sum-cong {xs} {ys} xₙ≃yₙ zero zero = ≃-refl
sum-cong {xs} {ys} xₙ≃yₙ zero (suc n) = +-cong (sum-cong xₙ≃yₙ 0 n) (xₙ≃yₙ n)-}
sum-cong {xs} {ys} xₙ≃yₙ 0 n = lem n
  where
    lem : ∀ n -> sum xs 0 n ≃ sum ys 0 n
    lem 0 = ≃-refl
    lem (suc n) = +-cong (lem n) (xₙ≃yₙ n)
sum-cong {xs} {ys} xₙ≃yₙ (suc m) n = +-cong (sum-cong xₙ≃yₙ 0 n) (-‿cong (sum-cong xₙ≃yₙ 0 (suc m)))

{-
∣sumxᵢ∣ ≤ sum∣xᵢ∣ 


Sometimes it's easier to use sumᵀ instead of sum that gives
            sumᵢ₌ₖⁿ xᵢ = xₖ + ⋯ + xₙ
instead of
            sumᵢ₌ₖⁿ xᵢ = sumᵢ₌₀ⁿ xᵢ - sumᵢ₌₀ᵏ xᵢ
when k ≤ n. 

As an example, consider the triangle inequality proof for sum below.

Note that sumᵀ requires i≤n, which isn't what we want in general. Moreover, 
sumᵀ uses a somewhat complex with clause, so it's annoying to prove things about.
Hence the alternative definition.
-}

@0 sumᵀ : (ℕ -> ℝ) -> (i n : ℕ) -> (i ℕ.≤ n) -> ℝ
sumᵀ xs i n i≤n with ≤⇒≡∨< i n i≤n
... | inj₁ refl = zeroℝ
sumᵀ xs i (suc n-1) i≤n | inj₂ (ℕ.s≤s i<n) = sumᵀ xs i n-1 i<n + xs n-1

@0 sum-to-sumᵀ : ∀ (xs : ℕ -> ℝ) -> ∀ m n -> (m≤n : m ℕ.≤ n) -> sum xs m n ≃ sumᵀ xs m n m≤n
sum-to-sumᵀ xs zero n ℕ.z≤n = lem n
  where
    lem : ∀ n -> sum0 xs n ≃ sumᵀ xs 0 n ℕ.z≤n
    lem 0 = ≃-refl
    lem (suc n) with ≤⇒≡∨< 0 (suc n) ℕ.z≤n
    ... | inj₂ 0<n = +-congˡ (xs n) (lem n)
sum-to-sumᵀ xs (suc m-1) n m≤n with ≤⇒≡∨< (suc m-1) n m≤n
... | inj₁ refl = +-inverseʳ (sum0 xs (suc m-1))
sum-to-sumᵀ xs (suc m-1) (suc n-1) m≤n | inj₂ (ℕ.s≤s m<n) = begin
  sum0 xs n-1 + xs n-1 - (sum0 xs m-1 + xs m-1) ≈⟨ solve 3 (λ sum0ⁿ⁻¹xᵢ xₙ₋₁ sum0ᵐxᵢ ->
                                               sum0ⁿ⁻¹xᵢ ⊕ xₙ₋₁ ⊖ sum0ᵐxᵢ ⊜ sum0ⁿ⁻¹xᵢ ⊖ sum0ᵐxᵢ ⊕ xₙ₋₁)
                                               ≃-refl (sum0 xs n-1) (xs n-1) (sum0 xs (suc m-1)) ⟩
  sum0 xs n-1 - (sum0 xs m-1 + xs m-1) + xs n-1 ≈⟨ +-congˡ (xs n-1) (sum-to-sumᵀ xs (suc m-1) n-1 m<n) ⟩
  sumᵀ xs (suc m-1) n-1 m<n + xs n-1           ∎
  where open ≃-Reasoning

@0 sumᵀ-triangle-inequality : ∀ (xs : ℕ -> ℝ) -> ∀ m n -> (m≤n : m ℕ.≤ n) -> ∣ sumᵀ xs m n m≤n ∣ ≤ sumᵀ (λ k -> ∣ xs k ∣) m n m≤n
sumᵀ-triangle-inequality xs m n m≤n with ≤⇒≡∨< m n m≤n
... | inj₁ refl = ≤-reflexive (≃-reflexive (λ @0 {(suc k-1) -> ℚP.≃-refl}))
sumᵀ-triangle-inequality xs m (suc n-1) m≤n | inj₂ (ℕ.s≤s m<n) = let n = suc n-1 in begin
  ∣ sumᵀ xs m n-1 m<n + xs n-1 ∣                ≤⟨ ∣x+y∣≤∣x∣+∣y∣ (sumᵀ xs m n-1 m<n) (xs n-1) ⟩
  ∣ sumᵀ xs m n-1 m<n ∣ + ∣ xs n-1 ∣            ≤⟨ +-monoˡ-≤ ∣ xs n-1 ∣ (sumᵀ-triangle-inequality xs m n-1 m<n) ⟩
  sumᵀ (λ k -> ∣ xs k ∣) m n-1 m<n + ∣ xs n-1 ∣  ∎
  where open ≤-Reasoning

{-
Note that m ≤ n is required since, if m > n, then sum essentially flips m and n and may return a negative number.
-}
@0 sum-triangle-inequality : ∀ (xs : ℕ -> ℝ) -> ∀ m n -> m ℕ.≤ n -> ∣ sum xs m n ∣ ≤ sum (λ k -> ∣ xs k ∣) m n
sum-triangle-inequality xs m n m≤n = begin
  ∣ sum xs m n ∣                 ≈⟨ ∣-∣-cong (sum-to-sumᵀ xs m n m≤n) ⟩
  ∣ sumᵀ xs m n m≤n ∣            ≤⟨ sumᵀ-triangle-inequality xs m n m≤n ⟩
  sumᵀ (λ k -> ∣ xs k ∣) m n m≤n ≈⟨ ≃-sym (sum-to-sumᵀ (λ k -> ∣ xs k ∣) m n m≤n) ⟩
  sum (λ k -> ∣ xs k ∣) m n       ∎
  where open ≤-Reasoning

@0 sum0-mono-≤ : ∀ {xs ys} -> (∀ n -> xs n ≤ ys n) -> ∀ n -> sum0 xs n ≤ sum0 ys n
sum0-mono-≤ {xs} {ys} xₙ≤yₙ 0 = ≤-refl
sum0-mono-≤ {xs} {ys} xₙ≤yₙ (suc n) = +-mono-≤ (sum0-mono-≤ xₙ≤yₙ n) (xₙ≤yₙ n)

@0 sumᵀ-mono-≤ : ∀ {xs ys} -> (∀ n -> xs n ≤ ys n) -> ∀ m n -> (m≤n : m ℕ.≤ n) -> sumᵀ xs m n m≤n ≤ sumᵀ ys m n m≤n
sumᵀ-mono-≤ {xs} {ys} xₙ≤yₙ m n m≤n with ≤⇒≡∨< m n m≤n
... | inj₁ refl = ≤-refl
sumᵀ-mono-≤ {xs} {ys} xₙ≤yₙ m (suc n-1) m≤n | inj₂ (ℕ.s≤s m<n) = +-mono-≤ (sumᵀ-mono-≤ xₙ≤yₙ m n-1 m<n) (xₙ≤yₙ n-1)

@0 sum-mono-≤ : ∀ {xs ys} -> (∀ n -> xs n ≤ ys n) -> ∀ m n -> m ℕ.≤ n -> sum xs m n ≤ sum ys m n
sum-mono-≤ {xs} {ys} xₙ≤yₙ m n m≤n = begin
  sum xs m n      ≈⟨ sum-to-sumᵀ xs m n m≤n ⟩
  sumᵀ xs m n m≤n ≤⟨ sumᵀ-mono-≤ xₙ≤yₙ m n m≤n ⟩
  sumᵀ ys m n m≤n ≈⟨ ≃-sym (sum-to-sumᵀ ys m n m≤n) ⟩
  sum ys m n       ∎
  where open ≤-Reasoning

@0 neg-flips-sum : ∀ (xs : ℕ -> ℝ) -> ∀ m n -> - sum xs m n ≃ sum xs n m
neg-flips-sum xs 0 0 = ≃-sym 0≃-0
neg-flips-sum xs 0 (suc n) = ≃-sym (+-identityˡ _)
neg-flips-sum xs (suc m) zero = solve 1 (λ a -> ⊝ (Κ 0ℚᵘ ⊖ a) ⊜ a) ≃-refl (sum0 xs (suc m))
neg-flips-sum xs (suc m) (suc n) = solve 2 (λ a b -> ⊝ (a ⊖ b) ⊜ b ⊖ a) ≃-refl (sum0 xs (suc n)) (sum0 xs (suc m))

@0 sumᵀ-mono-≤-weak : ∀ {xs ys : ℕ -> ℝ} -> ∀ {m n} -> (m≤n : m ℕ.≤ n) -> (∀ k -> m ℕ.≤ k × k ℕ.≤ n -> xs k ≤ ys k) ->
                 sumᵀ xs m n m≤n ≤ sumᵀ ys m n m≤n
sumᵀ-mono-≤-weak {xs} {ys} {m} {n} m≤n hyp with ≤⇒≡∨< m n m≤n
... | inj₁ refl = ≤-refl
sumᵀ-mono-≤-weak {xs} {ys} {m} {suc n-1} m≤n hyp | inj₂ (ℕ.s≤s m<n) = +-mono-≤
                             (sumᵀ-mono-≤-weak m<n (λ k m≤k≤n-1 -> hyp k (proj₁ m≤k≤n-1 , ℕP.≤-trans (proj₂ m≤k≤n-1) (ℕP.n≤1+n n-1))))
                             (hyp n-1 (m<n , ℕP.n≤1+n n-1))

@0 sum-mono-≤-weak : ∀ {xs ys : ℕ -> ℝ} -> ∀ {m n} -> m ℕ.≤ n -> (∀ k -> m ℕ.≤ k × k ℕ.≤ n -> xs k ≤ ys k) ->
                sum xs m n ≤ sum ys m n
sum-mono-≤-weak {xs} {ys} {m} {n} m≤n hyp = begin
  sum xs m n      ≈⟨ sum-to-sumᵀ xs m n m≤n ⟩
  sumᵀ xs m n m≤n ≤⟨ sumᵀ-mono-≤-weak m≤n hyp ⟩
  sumᵀ ys m n m≤n ≈⟨ ≃-sym (sum-to-sumᵀ ys m n m≤n) ⟩
  sum ys m n       ∎
  where open ≤-Reasoning

@0 sum0≃0 : ∀ m n -> sum (λ k -> zeroℝ) m n ≃ zeroℝ
sum0≃0 zero n = lem n
  where
    lem : ∀ n -> sum0 (λ k -> zeroℝ) n ≃ zeroℝ
    lem zero = ≃-refl
    lem (suc n) = ≃-trans (+-identityʳ (sum0 (λ k -> zeroℝ) n)) (lem n)
sum0≃0 (suc m) n = begin
  sum0 (λ k -> zeroℝ) n - (sum0 (λ k -> zeroℝ) m + zeroℝ) ≈⟨ +-cong (sum0≃0 0 n) (-‿cong (sum0≃0 0 (suc m))) ⟩
  zeroℝ - zeroℝ                                    ≈⟨ +-inverseʳ zeroℝ ⟩
  zeroℝ                                          ∎
  where open ≃-Reasoning

@0 0≤xₙ⇒0≤sumxₙ : ∀ {xs : ℕ -> ℝ} -> ∀ {m n} -> m ℕ.≤ n -> (∀ k -> m ℕ.≤ k × k ℕ.≤ n -> zeroℝ ≤ xs k) ->
             zeroℝ ≤ sum xs m n
0≤xₙ⇒0≤sumxₙ {xs} {m} {n} m≤n hyp = begin
  zeroℝ                ≈⟨ ≃-sym (sum0≃0 m n) ⟩
  sum (λ k -> zeroℝ) m n ≤⟨ sum-mono-≤-weak m≤n hyp ⟩
  sum xs m n           ∎
  where open ≤-Reasoning

@0 nonNegxₙ⇒nonNegsumxₙ : ∀ {xs : ℕ -> ℝ} -> ∀ {m n} -> m ℕ.≤ n -> (∀ k -> m ℕ.≤ k × k ℕ.≤ n -> NonNegative (xs k)) ->
                     NonNegative (sum xs m n)
nonNegxₙ⇒nonNegsumxₙ {xs} {m} {n} m≤n hyp = nonNeg-cong (lem (sum xs m n))
                                          (0≤xₙ⇒0≤sumxₙ m≤n (λ k m≤k≤n -> nonNeg-cong (≃-sym (lem (xs k))) (hyp k m≤k≤n)))
  where
    lem : ∀ x -> x - zeroℝ ≃ x
    lem = solve 1 (λ x -> x ⊖ Κ 0ℚᵘ ⊜ x) ≃-refl

-- This differs from cauchyToConvergent in that
  -- it doesn't use the IsCauchy type and
  -- it assumes that m ℕ.> n.
cauchyConvergence : ∀ (xs : ℕ -> ℝ) ->
                     (∀ k -> {@0 k≢0 : k ≢0} -> Σ0 ℕ λ Nₖ-1 -> ∀ m n -> m ℕ.> n -> n ℕ.≥ suc Nₖ-1 -> ∣ xs m - xs n ∣ ≤ ((+ 1 / k) {k≢0}) ⋆) ->
                     IsConvergent xs
cauchyConvergence xs hyp = fastCauchyToConvergent xs (MkCauchy main)
  where
    main : ∀ k -> {@0 k≢0 : k ≢0} -> Σ0 ℕ λ Mₖ-1 -> ∀ m n -> m ℕ.≥ suc Mₖ-1 -> n ℕ.≥ suc Mₖ-1 ->
           ∣ xs m - xs n ∣ ≤ ((+ 1 / k) {k≢0}) ⋆
    main k {k≢0} = proj₁ (hyp k) :&: sub k {k≢0}
      where
        open ≤-Reasoning
        @0 sub : ∀ (k : ℕ) {k≢0 : k ≢0} ->
                  ∀ m n -> m ℕ.≥ suc (proj₁ (hyp k {k≢0})) -> n ℕ.≥ suc (proj₁ (hyp k {k≢0})) ->
                  ∣ xs m - xs n ∣ ≤ ((+ 1 / k) {k≢0}) ⋆
        sub (suc k-1) m n m≥Mₖ n≥Mₖ with ℕP.<-cmp m n
        ... | tri< m<n ¬b ¬c = let k = suc k-1 in begin
          ∣ xs m - xs n ∣ ≈⟨ ∣x-y∣≃∣y-x∣ (xs m) (xs n) ⟩
          ∣ xs n - xs m ∣ ≤⟨ proj₂ (hyp k) n m m<n m≥Mₖ ⟩
          (+ 1 / k) ⋆      ∎
        ... | tri≈ ¬a refl ¬c = let k = suc k-1 in begin
          ∣ xs m - xs m ∣ ≈⟨ ≃-trans (∣-∣-cong (+-inverseʳ (xs m))) (0≤x⇒∣x∣≃x ≤-refl) ⟩
          zeroℝ              ≤⟨ p≤q⇒p⋆≤q⋆ 0ℚᵘ (+ 1 / k) (ℚP.nonNegative⁻¹ _) ⟩
          (+ 1 / k) ⋆      ∎
        ... | tri> ¬a ¬b m>n = proj₂ (hyp (suc k-1)) m n m>n n≥Mₖ
{-# COMPILE AGDA2HS cauchyConvergence #-}

abstract
  fastCauchyConvergence : ∀ (xs : ℕ -> ℝ) ->
                            (∀ k -> {@0 k≢0 : k ≢0} -> Σ0 ℕ λ Nₖ-1 -> ∀ m n -> m ℕ.> n -> n ℕ.≥ suc Nₖ-1 -> ∣ xs m - xs n ∣ ≤ ((+ 1 / k) {k≢0}) ⋆) ->
                            IsConvergent xs
  fastCauchyConvergence = cauchyConvergence
  {-# COMPILE AGDA2HS fastCauchyConvergence #-}

-- Aliases with erased parameters.
@0 cauchy-convergence fast-cauchy-convergence :
                  ∀ {xs : ℕ -> ℝ} ->
                     (∀ k -> {@0 k≢0 : k ≢0} -> Σ0 ℕ λ Nₖ-1 -> ∀ m n -> m ℕ.> n -> n ℕ.≥ suc Nₖ-1 -> ∣ xs m - xs n ∣ ≤ ((+ 1 / k) {k≢0}) ⋆) ->
                     IsConvergent xs
cauchy-convergence {xs} = cauchyConvergence xs
fast-cauchy-convergence {xs} = fastCauchyConvergence xs

{-
This is a generalized version of Bishop's Proposition 3.5.

Proposition:
  If sumyₙ converges and if there is N∈ℕ such that
                ∣xₙ∣ ≤ yₙ                        (n ≥ N),
then sumxₙ converges.
Proof:
  Let k∈ℕ. Then there is N₂∈ℕ such that 
                     ∣sumᵢ₌ₙ₊₁ᵐ yᵢ∣ ≤ k⁻¹          (m > n ≥ N₂).
Let N₁∈ℕ such that ∣xₙ∣ ≤ yₙ for n ≥ N₁. Define N = max{N₁, N₂} and let
m > n ≥ N. Then
               ∣sumᵢ₌ₙ₊₁ᵐ xᵢ∣ ≤ sumᵢ₌ₙ₊₁ᵐ ∣xᵢ∣
                            ≤ sumᵢ₌ₙ₊₁ᵐ yᵢ  since m > n ≥ N₁
                            ≤ ∣sumᵢ₌ₙ₊₁ᵐ yᵢ∣
                            ≤ k⁻¹.
Hence sumxᵢ is convergent.                                               □
[2]
-}
proposition35 : ∀ (xs ys : ℕ -> ℝ) -> IsConvergent (seriesOf ys) -> (Σ0 ℕ λ N-1 -> ∀ n -> n ℕ.≥ suc N-1 -> ∣ xs n ∣ ≤ ys n) ->
                    IsConvergent (seriesOf xs)
proposition35 xs ys sumysCon (l₁M1 :&: n≥l₁⇒∣xₙ∣≤yₙ) = cauchyConvergence (seriesOf xs) (λ k {k≢0} ->
                            let sumysCauchy = cauchyConvergenceTestIf ys sumysCon k
                                  ; l₁ = suc l₁M1; l₂ = suc (proj₁ sumysCauchy); N = l₁ ℕ.⊔ l₂ in
                            ℕ.pred N :&: theProof k {k≢0})
  where
  @0 theProof : (k : ℕ) {k≢0 : k ≢0} ->
                (m n : ℕ) →
                m ℕ.> n →
                n ℕ.≥
                suc
                (ℕ.pred
                 (suc l₁M1 ℕ.⊔
                  suc (proj₁ (cauchyConvergenceTestIf ys sumysCon k {k≢0})))) →
                ∣ seriesOf xs m - seriesOf xs n ∣ ≤ ((+ 1 / k) {k≢0}) ⋆
  theProof (suc k-1) (suc m-1) (suc n-1) m>n n≥N =
                            let k = suc k-1; m = suc m-1; n = suc n-1
                                  ; sumysCauchy = cauchyConvergenceTestIf ys sumysCon k
                                  ; l₁ = suc l₁M1; l₂ = suc (proj₁ sumysCauchy)
                                  ; l₂≤N = ℕP.m≤n⊔m l₁ l₂
                                  ; m≥N = ℕP.<⇒≤ (ℕP.<-transʳ n≥N m>n) in
    begin
      ∣ sum xs n m ∣            ≤⟨ sum-triangle-inequality xs n m (ℕP.<⇒≤ m>n) ⟩
      sum (λ i -> ∣ xs i ∣) n m ≤⟨ sum-mono-≤-weak (ℕP.<⇒≤ m>n) (λ k n≤k≤m -> n≥l₁⇒∣xₙ∣≤yₙ k
                                 (ℕP.≤-trans (ℕP.≤-trans (ℕP.m≤m⊔n l₁ l₂) n≥N) (proj₁ n≤k≤m))) ⟩
      sum ys n m                ≤⟨ x≤∣x∣ ⟩
      ∣ sum ys n m ∣            ≤⟨ proj₂ sumysCauchy n m
                                 (ℕP.≤-trans l₂≤N n≥N) (ℕP.≤-trans l₂≤N m≥N) ⟩
      (+ 1 / k) ⋆              ∎
    where open ≤-Reasoning
{-# COMPILE AGDA2HS proposition35 #-}

-- Alias.
proposition-3-5 : ∀ {xs ys} -> IsConvergent (seriesOf ys) -> (Σ0 ℕ λ N-1 -> ∀ n -> n ℕ.≥ suc N-1 -> ∣ xs n ∣ ≤ ys n) ->
                    IsConvergent (seriesOf xs)
proposition-3-5 {xs} {ys} = proposition35 xs ys

@0 absolute⇒isConvergent : ∀ {xs : ℕ -> ℝ} -> SeriesConvergesAbsolutely xs -> IsConvergent (seriesOf xs)
absolute⇒isConvergent {xs} hyp = proposition-3-5 hyp (0 :&: (λ n n≥1 -> ≤-refl))

-- A prettier name to unpack the limit from an IsConvergent object.
lim : {@0 xs : ℕ -> ℝ} -> IsConvergent xs -> ℝ
-- lim {xs} (ℓ :^: hyp) = ℓ
lim = proj₁'
{-# COMPILE AGDA2HS lim #-}

-- I guess we don't actually use this for computations.
data _DivergesBy_ : REL (ℕ -> ℝ) ℝ 0ℓ where
  @0 div* : {f : ℕ -> ℝ} -> {ε : ℝ} -> @0 Positive ε ->
         @0 (∀ k -> {k≢0 : k ≢0} -> (∃ λ m -> ∃0 λ n -> m ℕ.≥ k × n ℕ.≥ k × ∣ f m - f n ∣ ≥ ε)) ->
         f DivergesBy ε

_isDivergent : (ℕ -> ℝ) -> Set
f isDivergent = ∃ λ ε -> f DivergesBy ε

@0 cauchy-getter : ∀ {xs} -> IsCauchy xs ->
                ∀ k -> {@0 k≢0 : k ≢0} -> ∃0 λ Mₖ-1 -> ∀ m n -> m ℕ.≥ suc Mₖ-1 -> n ℕ.≥ suc Mₖ-1 ->
                ∣ xs m - xs n ∣ ≤ ((+ 1 / k) {k≢0}) ⋆
cauchy-getter {xs} (MkCauchy hyp) = hyp

abstract
  @0 fast-cauchy-getter : ∀ {xs} -> IsCauchy xs ->
                       ∀ k -> {@0 k≢0 : k ≢0} -> ∃0 λ Mₖ-1 -> ∀ m n -> m ℕ.≥ suc Mₖ-1 -> n ℕ.≥ suc Mₖ-1 ->
                       ∣ xs m - xs n ∣ ≤ ((+ 1 / k) {k≢0}) ⋆
  fast-cauchy-getter = cauchy-getter

@0 ¬[isConvergent∧isDivergent] : ∀ xs -> ¬ (IsConvergent xs × xs isDivergent)
¬[isConvergent∧isDivergent] xs (hyp1 , ε , div* posε hyp2) = let fromdiv = archimedeanℝ₂ ε posε; k = suc (proj₁ fromdiv)
                                                                                    ; fromhyp1 = cauchy-getter (fast-convergent⇒cauchy hyp1) k
                                                                                    ; Nₖ = suc (proj₁ fromhyp1)
                                                                                    ; m = proj₁ (hyp2 Nₖ)
                                                                                    ; n = proj₁ (proj₂ (hyp2 Nₖ)) in
                                                                        <-irrefl ≃-refl (begin-strict
  (+ 1 / k) ⋆     <⟨ proj₂ fromdiv ⟩
  ε               ≤⟨ proj₂ (proj₂ (proj₂ (proj₂ (hyp2 Nₖ)))) ⟩
  ∣ xs m - xs n ∣ ≤⟨ proj₂ fromhyp1 m n
                     (proj₁ (proj₂ (proj₂ (hyp2 Nₖ))))
                     (proj₁ (proj₂ (proj₂ (proj₂ (hyp2 Nₖ))))) ⟩
  (+ 1 / k) ⋆      ∎)
  where open ≤-Reasoning

{-
(xₙ) is a subsequence of (yₙ) if there is h : ℕ -> ℕ such that
                              xₙ = yₕ₍ₙ₎                 (n∈ℕ)
and
                            h(n) < h(n+1)                (n∈ℕ).
[3]
-}
-- We don't use this either.
data _SubsequenceOf_ : Rel (ℕ -> ℝ) 0ℓ where
  @0 subseq* : {xs ys : ℕ -> ℝ} -> (∃0 λ (f : ℕ -> ℕ) ->
            (∀ n -> xs n ≃ ys (f n)) × (∀ n -> f n ℕ.< f (suc n))) ->
            xs SubsequenceOf ys

{-
Not sure what a more meaningful name for this is yet.
-}
@0 subsequence-helper : ∀ {f : ℕ -> ℕ} -> ∀ (k : ℕ) -> (∀ n -> f n ℕ.< f (suc n)) ->
                     ∃ λ (N : ℕ) -> ∀ n -> n ℕ.> N -> f n ℕ.> k  
subsequence-helper {f} zero hyp = 0 , λ @0 {(suc n-1) n>0 → ℕP.<-transʳ ℕ.z≤n (hyp n-1)}
subsequence-helper {f} (suc k) hyp = let ih = subsequence-helper k hyp; N = suc (proj₁ ih) in
                                     N , λ @0 {(suc n-1) (ℕ.s≤s n>N) → ℕP.<-transʳ (proj₂ ih n-1 n>N) (hyp n-1)}

@0 f[n]<f[n+1]⇒n≤f[n] : ∀ {f : ℕ -> ℕ} -> (∀ n -> f n ℕ.< f (suc n)) -> (∀ n -> n ℕ.≤ f n)
f[n]<f[n+1]⇒n≤f[n] {f} f[n]<f[n+1] 0 = ℕ.z≤n
f[n]<f[n+1]⇒n≤f[n] {f} f[n]<f[n+1] (suc n) = ℕP.<-transʳ (f[n]<f[n+1]⇒n≤f[n] f[n]<f[n+1] n) (f[n]<f[n+1] n)

@0 xₙ⊆yₙ∧yₙ→y⇒xₙ→y : {xs ys : ℕ → ℝ} → xs SubsequenceOf ys → (yₙ→y : IsConvergent ys) → ConvergesTo xs (lim yₙ→y)
xₙ⊆yₙ∧yₙ→y⇒xₙ→y {xs} {ys} (subseq* (f :&: hyp1 , hyp2)) (y :^: MkCon yₙ→y) = MkCon λ @0 {(suc k-1) → let k = suc k-1; N-get = yₙ→y k; N = suc (proj₁ N-get) in
                                                            ℕ.pred N :&: λ n n≥N → begin
  ∣ xs n - y ∣     ≈⟨ ∣-∣-cong (+-congˡ (- y) (hyp1 n)) ⟩
  ∣ ys (f n) - y ∣ ≤⟨ proj₂ N-get (f n) (ℕP.≤-trans n≥N (f[n]<f[n+1]⇒n≤f[n] hyp2 n)) ⟩
  (+ 1 / k) ⋆      ∎}
  where open ≤-Reasoning

abstract
  @0 fast-xₙ⊆yₙ∧yₙ→y⇒xₙ→y : {xs ys : ℕ → ℝ} → xs SubsequenceOf ys → (yₙ→y : IsConvergent ys) → ConvergesTo xs (lim yₙ→y)
  fast-xₙ⊆yₙ∧yₙ→y⇒xₙ→y = xₙ⊆yₙ∧yₙ→y⇒xₙ→y

--basically: if there is an ys such that ys does not converge to zeroℝ and xs is a subsequence of ys, then Σxs is divergent
@0 subsequence-divergence-test : ∀ {xs : ℕ -> ℝ} ->
                              (∃0 λ (r : ℝ) -> ∃0 λ (ys : ℕ -> ℝ) -> Positive r × ys SubsequenceOf xs × (∀ n -> ∣ ys n ∣ ≥ r)) ->
                              seriesOf xs isDivergent
subsequence-divergence-test {xs} (r :&: ys :&: posr , subseq* (f :&: yₙ⊂xₙ) , ∣yₙ∣≥r) =
                            r , div* posr (λ k -> let k≤f[k] = f[n]<f[n+1]⇒n≤f[n] (proj₂ yₙ⊂xₙ) k in
                            suc (f k) , f k :&: ℕP.≤-trans k≤f[k] (ℕP.n≤1+n (f k)) , k≤f[k] , (begin
  r                                          ≤⟨ ∣yₙ∣≥r k ⟩
  ∣ ys k ∣                                   ≈⟨ ∣-∣-cong (proj₁ yₙ⊂xₙ k) ⟩
  ∣ xs (f k) ∣                               ≈⟨ ∣-∣-cong (solve 2 (λ a b -> a ⊜ b ⊕ a ⊖ b) ≃-refl (xs (f k)) (sum0 xs (f k))) ⟩
  ∣ sum0 xs (suc (f k)) - sum0 xs (f k) ∣         ∎))
  where open ≤-Reasoning

@0 comparison-test-divergence : ∀ {xs ys : ℕ -> ℝ} -> (∃0 λ N₁ -> ∀ n -> n ℕ.≥ N₁ -> NonNegative (ys n)) ->
                             seriesOf ys isDivergent -> (∃0 λ N₂ -> ∀ n -> n ℕ.≥ N₂ -> xs n ≥ ys n) ->
                             seriesOf xs isDivergent
comparison-test-divergence {xs} {ys} (N₁ :&: n≥N₁⇒yₙ≥0) (ε , div* posε divsumyₙ) (N₂ :&: n≥N₂⇒xₙ≥yₙ) = ε , div* posε main
  where
    main : ∀ k -> {k ≢0} -> ∃ λ m -> ∃0 λ n -> m ℕ.≥ k × n ℕ.≥ k × ∣ sum0 xs m - sum0 xs n ∣ ≥ ε
    main (suc N₃-1) = let m = proj₁ (divsumyₙ N); n = proj₁ (proj₂ (divsumyₙ N))
                            ; N≤m = proj₁ (proj₂ (proj₂ (divsumyₙ N))); N≤n = proj₁ (proj₂ (proj₂ (proj₂ (divsumyₙ N))))
                            ; sumyₙhyp = proj₂ (proj₂ (proj₂ (proj₂ (divsumyₙ N)))) in
                            m , n :&: ℕP.≤-trans N₃≤N N≤m , ℕP.≤-trans N₃≤N N≤n ,
                            [ (λ m≥n -> sub m n N≤m N≤n m≥n sumyₙhyp) ,
                              (λ m≤n -> ≤-respʳ-≃ (∣x-y∣≃∣y-x∣ (sum0 xs n) (sum0 xs m)) (sub n m N≤n N≤m m≤n
                                        (≤-respʳ-≃ (∣x-y∣≃∣y-x∣ (sum0 ys m) (sum0 ys n)) sumyₙhyp))) ]′ (ℕP.≤-total n m)
      where
        open ≤-Reasoning
        N₃ = suc N₃-1
        N = suc (N₁ ℕ.⊔ N₂ ℕ.⊔ N₃)
        N₁≤N = ℕP.≤-trans (ℕP.≤-trans (ℕP.m≤m⊔n N₁ N₂) (ℕP.m≤m⊔n (N₁ ℕ.⊔ N₂) N₃)) (ℕP.n≤1+n (ℕ.pred N))
        N₂≤N = ℕP.≤-trans (ℕP.≤-trans (ℕP.m≤n⊔m N₁ N₂) (ℕP.m≤m⊔n (N₁ ℕ.⊔ N₂) N₃)) (ℕP.n≤1+n (ℕ.pred N))
        N₃≤N = ℕP.≤-trans (ℕP.m≤n⊔m (N₁ ℕ.⊔ N₂) N₃) (ℕP.n≤1+n (ℕ.pred N))
        sub : ∀ m n -> m ℕ.≥ N -> n ℕ.≥ N -> m ℕ.≥ n -> ∣ sum0 ys m - sum0 ys n ∣ ≥ ε -> ∣ sum0 xs m - sum0 xs n ∣ ≥ ε
        sub (suc m-1) (suc n-1) m≥N n≥N m≥n hyp = let m = suc m-1; n = suc n-1 in begin
          ε            ≤⟨ hyp ⟩
          ∣ sum ys n m ∣ ≈⟨ nonNegx⇒∣x∣≃x (nonNegxₙ⇒nonNegsumxₙ m≥n (λ k n≤k≤m -> n≥N₁⇒yₙ≥0 k
                          (ℕP.≤-trans (ℕP.≤-trans N₁≤N n≥N) (proj₁ n≤k≤m)))) ⟩
          sum ys n m     ≤⟨ sum-mono-≤-weak m≥n (λ k n≤k≤m -> n≥N₂⇒xₙ≥yₙ k
                          (ℕP.≤-trans (ℕP.≤-trans N₂≤N n≥N) (proj₁ n≤k≤m))) ⟩
          sum xs n m     ≤⟨ x≤∣x∣ ⟩
          ∣ sum xs n m ∣   ∎

archimedeanℝ₃ : ∀ (x y : ℝ) -> Positive x -> Σ0 ℕ λ n-1 -> (+ (suc n-1) / 1) ⋆ * x > y
archimedeanℝ₃ x y posx = let x≄0 = Either.Right (posxThenZeroLtx x posx); x⁻¹ = x \< x≄0
                                    ; arch = fastArchimedeanℝ (y * x⁻¹); n = suc (proj₁ arch) in
                            proj₁ arch :&: (begin-strict
  y               ≈⟨ ≃-sym (≃-trans (≃-trans (*-assoc y x⁻¹ x)
                     (*-congˡ {y} {x⁻¹ * x} {oneℝ} (*-inverseˡ x x≄0))) (*-identityʳ y)) ⟩
  y * x⁻¹ * x     <⟨ *-monoˡ-<-pos {x} posx {y * x⁻¹} {(+ n / 1) ⋆} (proj₂ arch) ⟩
  (+ n / 1) ⋆ * x  ∎)
  where open ≤-Reasoning
{-# COMPILE AGDA2HS archimedeanℝ₃ #-}

abstract
  fastArchimedeanℝ₃ : ∀ (x y : ℝ) -> Positive x -> Σ0 ℕ λ n-1 -> (+ (suc n-1) / 1) ⋆ * x > y
  fastArchimedeanℝ₃ = archimedeanℝ₃
  {-# COMPILE AGDA2HS fastArchimedeanℝ₃ #-}

@0 x≤y∧posx⇒y⁻¹≤x⁻¹ : ∀ {x y} -> x ≤ y -> Positive x -> (x≄0 : x ≄0) -> (y≄0 : y ≄0) ->
                   (y ⁻¹) y≄0 ≤ (x ⁻¹) x≄0
x≤y∧posx⇒y⁻¹≤x⁻¹ {x} {y} x≤y posx x≄0 y≄0 = let x⁻¹ = (x ⁻¹) x≄0; y⁻¹ = (y ⁻¹) y≄0 in begin
  y⁻¹             ≈⟨ ≃-sym (≃-trans (*-congˡ {y⁻¹} {x * x⁻¹} {oneℝ} (*-inverseʳ x x≄0)) (*-identityʳ y⁻¹)) ⟩
  y⁻¹ * (x * x⁻¹) ≤⟨ *-monoˡ-≤-nonNeg {x * x⁻¹} {y⁻¹} {y * x⁻¹}
                     (*-monoʳ-≤-nonNeg {x} {x⁻¹} {y} x≤y (nonNegx⇒nonNegx⁻¹ {x} (pos⇒nonNeg posx) x≄0))
                     (nonNegx⇒nonNegx⁻¹ {y} (pos⇒nonNeg (0<x⇒posx (<-≤-trans (posxThenZeroLtx x posx) x≤y))) y≄0) ⟩
  y⁻¹ * (y * x⁻¹) ≈⟨ ≃-trans (≃-trans (≃-sym (*-assoc y⁻¹ y x⁻¹))
                     (*-congʳ {x⁻¹} {y⁻¹ * y} {oneℝ} (*-inverseˡ y y≄0))) (*-identityˡ x⁻¹) ⟩
  x⁻¹              ∎
  where open ≤-Reasoning

densityOfℝ : ∀ (x y : ℝ) -> x < y -> Σ' ℝ λ ε -> (Positive ε) Tuple.× ((x < (x + ε)) Tuple.× ((x + ε) < y))  -- not a 3-member tuple because it's harder to get things out of
densityOfℝ x y xLty = let r-get = fastDensityOfℚ x y xLty; r = proj₁' r-get
                                          ; r≃x+r-x = solve 2 (λ r x -> r ⊜ x ⊕ (r ⊖ x)) ≃-refl (toReal r) x
                                          ; ε = (toReal r - x) in
                                ε :^: (
                                  (zeroLtxThenPosx ε (xLtyThenZeroLtyMinusx x (toReal r) (Tuple.fst (proj₂' r-get)))) Tuple.,
                                  ((ltRespREq x (toReal r) (x + ε) r≃x+r-x (Tuple.fst (proj₂' r-get))) Tuple.,
                                  (ltRespLEq y (toReal r) (x + ε) r≃x+r-x (Tuple.snd (proj₂' r-get)))))
{-# COMPILE AGDA2HS densityOfℝ #-}

-- Alias with erased parameters.
x<y⇒∃ε>0[x<x+ε<y] : ∀ {x y} -> x < y -> Σ' ℝ λ ε -> (Positive ε) Tuple.× ((x < (x + ε)) Tuple.× ((x + ε) < y))
x<y⇒∃ε>0[x<x+ε<y] {x} {y} = densityOfℝ x y

@0 0≤x,y⇒0≤x*y : ∀ {x y} -> zeroℝ ≤ x -> zeroℝ ≤ y -> zeroℝ ≤ x * y
0≤x,y⇒0≤x*y {x} {y} 0≤x 0≤y = nonNegx⇒0≤x (nonNegx,y⇒nonNegx*y (0≤x⇒nonNegx 0≤x) (0≤x⇒nonNegx 0≤y))

private
  @0 p²≥0 : ∀ p -> p ℚ.* p ℚ.≥ 0ℚᵘ
  p²≥0 (mkℚᵘ (+_ zero) d) = ℚP.nonNegative⁻¹ _
  p²≥0 (mkℚᵘ +[1+ n ] d) = ℚP.nonNegative⁻¹ _
  p²≥0 (mkℚᵘ (-[1+_] n) d) = ℚP.nonNegative⁻¹ _

@0 x²ⁿ≥0 : ∀ x -> ∀ n -> pow x (2 ℕ.* n) ≥ zeroℝ
x²ⁿ≥0 x n = begin
  zeroℝ                ≤⟨ nonNegx⇒0≤x (nonNeg* (λ @0 {(suc k-1) ->
                       ℚP.≤-trans (ℚP.nonPositive⁻¹ _)
                       (p²≥0 (seq (pow x n) _))})) ⟩
  pow x n * pow x n ≈⟨ xⁿxᵐ≃xⁿ⁺ᵐ x n n ⟩
  pow x (n ℕ.+ n)   ≡⟨ cong (λ k -> pow x k) (ℤP.+-injective (ℤsolve 1 (λ n ->
                       n :+ n := (n :+ (n :+ ℤΚ (+ 0)))) refl (+ n))) ⟩
  pow x (2 ℕ.* n)    ∎
  where open ≤-Reasoning


@0 0≤x⇒y≤y+x : ∀ {x} y -> zeroℝ ≤ x -> y ≤ y + x
0≤x⇒y≤y+x {x} y 0≤x = begin
  y      ≈⟨ ≃-sym (+-identityʳ y) ⟩
  y + zeroℝ ≤⟨ +-monoʳ-≤ y 0≤x ⟩
  y + x   ∎
  where open ≤-Reasoning

@0 bernoullis-inequality : ∀ {x} -> x ≥ - oneℝ -> ∀ (n : ℕ) -> pow (oneℝ + x) n ≥ oneℝ + (+ n / 1) ⋆ * x
bernoullis-inequality {x} x≥-1 0 = ≤-reflexive (solve 1 (λ x -> Κ 1ℚᵘ ⊕ Κ 0ℚᵘ ⊗ x ⊜ Κ 1ℚᵘ) ≃-refl x)
bernoullis-inequality {x} x≥-1 (suc n-1) = let n = suc n-1 in begin
  oneℝ + (+ n / 1) ⋆ * x                                    ≈⟨ ≃-sym (+-congʳ oneℝ (*-congʳ {x} (≃-trans
                                                             (solve 0 (Κ 1ℚᵘ ⊕ Κ (+ n-1 / 1) ⊜ Κ (1ℚᵘ ℚ.+ + n-1 / 1)) ≃-refl)
                                                             (⋆-cong (ℚ.*≡* (ℤsolve 1 (λ n-1 ->
                                                                     (ℤΚ (+ 1) :+ n-1 :* ℤΚ (+ 1)) :* ℤΚ (+ 1) :=
                                                                     (ℤΚ (+ 1) :+ n-1) :* ℤΚ (+ 1)) refl (+ n-1))))))) ⟩
  oneℝ + (oneℝ + (+ n-1 / 1) ⋆) * x                           ≤⟨ 0≤x⇒y≤y+x {(+ n-1 / 1) ⋆ * (x * x)} (oneℝ + (oneℝ + (+ n-1 / 1) ⋆) * x)
                                                             (0≤x,y⇒0≤x*y (p≤q⇒p⋆≤q⋆ 0ℚᵘ (+ n-1 / 1) (ℚP.nonNegative⁻¹ _))
                                                             (≤-respʳ-≃ (solve 1 (λ x -> Κ 1ℚᵘ ⊗ x ⊗ x ⊜ x ⊗ x) ≃-refl x) (x²ⁿ≥0 x 1))) ⟩
  oneℝ + (oneℝ + (+ n-1 / 1) ⋆) * x + (+ n-1 / 1) ⋆ * (x * x) ≈⟨ solve 3 (λ oneℝ n-1 x ->
                                                             Κ 1ℚᵘ ⊕ (oneℝ ⊕ n-1) ⊗ x ⊕ n-1 ⊗ (x ⊗ x) ⊜
                                                             Κ 1ℚᵘ ⊕ oneℝ ⊗ x ⊕ n-1 ⊗ x ⊕ n-1 ⊗ x ⊗ x)
                                                             ≃-refl oneℝ ((+ n-1 / 1) ⋆) x ⟩
  oneℝ + oneℝ * x + (+ n-1 / 1) ⋆ * x + (+ n-1 / 1) ⋆ * x * x ≈⟨ solve 2 (λ n-1 x ->
                                                             Κ 1ℚᵘ ⊕ Κ 1ℚᵘ ⊗ x ⊕ n-1 ⊗ x ⊕ n-1 ⊗ x ⊗ x ⊜
                                                             (Κ 1ℚᵘ ⊕ n-1 ⊗ x) ⊗ (Κ 1ℚᵘ ⊕ x))
                                                             ≃-refl ((+ n-1 / 1) ⋆) x ⟩
  (oneℝ + (+ n-1 / 1) ⋆ * x) * (oneℝ + x)                     ≤⟨ *-monoʳ-≤-nonNeg {oneℝ + (+ n-1 / 1) ⋆ * x} {oneℝ + x}
                                                              {pow (oneℝ + x) n-1}
                                                              (bernoullis-inequality {x} x≥-1 n-1)
                                                              (nonNeg-cong {x - - oneℝ} {oneℝ + x}
                                                              (solve 1 (λ x -> x ⊖ (⊝ Κ 1ℚᵘ) ⊜ Κ 1ℚᵘ ⊕ x) ≃-refl x)
                                                              x≥-1) ⟩
  pow (oneℝ + x) n-1 * (oneℝ + x)                              ∎
  where open ≤-Reasoning


@0 x≄0⇒xⁿ≄0 : ∀ {x} -> ∀ n -> x ≄0 -> pow x n ≄0
x≄0⇒xⁿ≄0 {x} zero x≄0 = Either.Right (pLtqThenToRealpLtToRealq 0ℚᵘ 1ℚᵘ (ℚP.positive⁻¹ _))
x≄0⇒xⁿ≄0 {x} (suc n) x≄0 = x≄0∧y≄0⇒x*y≄0 (x≄0⇒xⁿ≄0 n x≄0) x≄0

-- Same problem here.
postulate @0 [xⁿ]⁻¹≃[x⁻¹]ⁿ : ∀ {x} -> (x≄0 : x ≄0) -> ∀ n -> (xⁿ≄0 : pow x n ≄0) -> ((pow x n) ⁻¹) xⁿ≄0 ≃ pow ((x ⁻¹) x≄0) n
{-
[xⁿ]⁻¹≃[x⁻¹]ⁿ {x} x≄0 zero xⁿ≄0 = ⋆-distrib-⁻¹ 1ℚᵘ xⁿ≄0
[xⁿ]⁻¹≃[x⁻¹]ⁿ {x} x≄0 (suc n) xⁿ⁺¹≄0 = let xⁿ≄0 = x≄0⇒xⁿ≄0 {x} n x≄0 in begin
  ((pow x n * x) ⁻¹) xⁿ⁺¹≄0        ≈⟨ fast-⁻¹-distrib-* {pow x n} {x} xⁿ≄0 x≄0 xⁿ⁺¹≄0 ⟩
  ((pow x n) ⁻¹) xⁿ≄0 * (x ⁻¹) x≄0 ≈⟨ *-congʳ {(x ⁻¹) x≄0} {(pow x n ⁻¹) xⁿ≄0} {pow ((x ⁻¹) x≄0) n}
                                      ([xⁿ]⁻¹≃[x⁻¹]ⁿ {x} x≄0 n xⁿ≄0) ⟩
  pow ((x ⁻¹) x≄0) n * (x ⁻¹) x≄0   ∎
  where open ≃-Reasoning
-}

@0 1≤x∧m≤n⇒xᵐ≤xⁿ : ∀ {x} -> ∀ {m n} -> oneℝ ≤ x -> m ℕ.≤ n -> pow x m ≤ pow x n
1≤x∧m≤n⇒xᵐ≤xⁿ {x} {zero} {zero} 1≤x m≤n = ≤-refl
1≤x∧m≤n⇒xᵐ≤xⁿ {x} {zero} {suc n} 1≤x m≤n = lem (suc n)
  where
    open ≤-Reasoning
    lem : ∀ n -> oneℝ ≤ pow x n
    lem zero = ≤-refl
    lem (suc n) = begin
      oneℝ          ≤⟨ 1≤x ⟩
      x           ≈⟨ ≃-sym (*-identityˡ x) ⟩
      oneℝ * x      ≤⟨ *-monoʳ-≤-nonNeg (lem n)
                     (0≤x⇒nonNegx (≤-trans (p≤q⇒p⋆≤q⋆ 0ℚᵘ 1ℚᵘ (ℚP.nonNegative⁻¹ _)) 1≤x)) ⟩
      pow x n * x  ∎
1≤x∧m≤n⇒xᵐ≤xⁿ {x} {suc m} {suc n} 1≤x (ℕ.s≤s m≤n) = *-monoʳ-≤-nonNeg (1≤x∧m≤n⇒xᵐ≤xⁿ 1≤x m≤n)
                                                    (0≤x⇒nonNegx (≤-trans (p≤q⇒p⋆≤q⋆ 0ℚᵘ 1ℚᵘ (ℚP.nonNegative⁻¹ _)) 1≤x))

@0 nonNegx⇒nonNegxⁿ : ∀ {x} -> ∀ n -> NonNegative x -> NonNegative (pow x n)
nonNegx⇒nonNegxⁿ {x} zero nonx = nonNegp⇒nonNegp⋆ 1ℚᵘ _
nonNegx⇒nonNegxⁿ {x} (suc n) nonx = nonNegx,y⇒nonNegx*y (nonNegx⇒nonNegxⁿ n nonx) nonx

limitOfPositiveGeometricSequence : ∀ (r : ℝ) -> (zeroℝ < r) Tuple.× (r < oneℝ) ->
                                       ∀ j -> {@0 j≢0 : j ≢0} -> Σ0 ℕ λ Nₖ-1 -> ∀ n -> n ℕ.≥ suc Nₖ-1 -> pow r n ≤ toReal ((+ 1 / j) {j≢0})
limitOfPositiveGeometricSequence r (zeroLtr Tuple., rLt1) j {j≢0} = let N = suc (proj₁ (lem j {j≢0})) in
  ℕ.pred N :&: theProof j {j≢0}
  where
    open ≤-Reasoning
    rNeq0 = Either.Right zeroLtr
    t = r \< rNeq0
    -- have to use <-respˡ-≃0 here because of the erased ≃
    oneLtt : oneℝ < t
    oneLtt = let 0<1 = pLtqThenToRealpLtToRealq (+ 0 / 1) (+ 1 / 1) (ℚP.positive⁻¹ _); 1≄0 = Either.Right 0<1 in
                             ltRespLEq t (oneℝ \< 1≄0) oneℝ (⋆-distrib-⁻¹ (+ 1 / 1) 1≄0) (invMonoLt r oneℝ rLt1 rNeq0 1≄0 (zeroLtxThenPosx r zeroLtr) (zeroLtxThenPosx oneℝ 0<1))
    {-begin-strict
      oneℝ                     ≈⟨ ≃-sym ({!⋆-distrib-⁻¹ 1ℚᵘ 1≄0!}) ⟩
      (((+ 1 / 1) ⋆) ⁻¹) 1≄0 <⟨ {!x<y∧posx,y⇒y⁻¹<x⁻¹ {r} {oneℝ} r<1 r≄0 1≄0 (0<x⇒posx 0<r) (0<x⇒posx 0<1)!} ⟩
      t                       ∎-}
    @0 t≄0 : t ≄0
    t≄0 = Either.Right (0<x⇒0<x⁻¹ {r} rNeq0 zeroLtr)
    @0 tⁿ≄0 : ∀ n -> pow t n ≄0
    tⁿ≄0 0 = Either.Right (pLtqThenToRealpLtToRealq 0ℚᵘ 1ℚᵘ (ℚP.positive⁻¹ _))
    tⁿ≄0 (suc n) = x≄0∧y≄0⇒x*y≄0 (tⁿ≄0 n) t≄0
    arch : Σ0 ℕ λ n-1 -> (+ (suc n-1) / 1) ⋆ * (t - oneℝ) > oneℝ
    arch = fastArchimedeanℝ₃ (t - oneℝ) oneℝ oneLtt
    k : ℕ
    k = suc (proj₁ arch)

    @0 -1≤t-1 : - oneℝ ≤ t - oneℝ
    -1≤t-1 = begin
      - oneℝ        ≈⟨ ≃-sym (⋆-distrib-neg 1ℚᵘ) ⟩
      (ℚ.- 1ℚᵘ) ⋆ ≤⟨ p≤q⇒p⋆≤q⋆ (ℚ.- 1ℚᵘ) 0ℚᵘ (ℚP.nonPositive⁻¹ _) ⟩
      zeroℝ          ≤⟨ x≤y⇒0≤y-x (<⇒≤ oneLtt) ⟩
      t - oneℝ       ∎

    @0 tᵏⁿ≥n : ∀ n -> {n ≢0} -> pow t (k ℕ.* n) ≥ (+ n / 1) ⋆
    tᵏⁿ≥n (suc n-1) = let n = suc n-1 in begin
      (+ n / 1) ⋆                          ≈⟨ ≃-sym (*-identityˡ ((+ n / 1) ⋆)) ⟩
      oneℝ * (+ n / 1) ⋆                     ≤⟨ *-monoʳ-≤-nonNeg {oneℝ} {(+ n / 1) ⋆} {(+ k / 1) ⋆ * (t - oneℝ)}
                                              (<⇒≤ (proj₂ arch)) (nonNegp⇒nonNegp⋆ (+ n / 1) _) ⟩
      (+ k / 1) ⋆ * (t - oneℝ) * (+ n / 1) ⋆ ≈⟨ solve 3 (λ a b c -> a ⊗ b ⊗ c ⊜ a ⊗ c ⊗ b) ≃-refl ((+ k / 1) ⋆) (t - oneℝ) ((+ n / 1) ⋆) ⟩
      (+ k / 1) ⋆ * (+ n / 1) ⋆ * (t - oneℝ) ≈⟨ solve 1 (λ t-1 -> Κ (+ k / 1) ⊗ Κ (+ n / 1) ⊗ t-1 ⊜ Κ ((+ k / 1) ℚ.* (+ n / 1)) ⊗ t-1) ≃-refl (t - oneℝ) ⟩
      (+ (k ℕ.* n) / 1) ⋆ * (t - oneℝ)       ≤⟨ ≤-respˡ-≃ (+-identityˡ ((+ (k ℕ.* n) / 1) ⋆ * (t - oneℝ)))
                                              (+-monoˡ-≤ ((+ (k ℕ.* n) / 1) ⋆ * (t - oneℝ)) (p≤q⇒p⋆≤q⋆ 0ℚᵘ 1ℚᵘ (ℚP.nonNegative⁻¹ _))) ⟩
      oneℝ + (+ (k ℕ.* n) / 1) ⋆ * (t - oneℝ)  ≤⟨ bernoullis-inequality {t - oneℝ} -1≤t-1 (k ℕ.* n) ⟩
      pow (oneℝ + (t - oneℝ)) (k ℕ.* n)        ≈⟨ pow-cong (k ℕ.* n) (solve 1 (λ t -> Κ 1ℚᵘ ⊕ (t ⊖ Κ 1ℚᵘ) ⊜ t) ≃-refl t) ⟩
      pow t (k ℕ.* n)                       ∎

    lem : ∀ j -> @0 {j ≢0} -> Σ0 ℕ λ N-1 -> ∀ n -> n ℕ.≥ suc N-1 -> pow t n ≥ toReal (+ j / 1)
    lem j {j≢0} = ℕ.pred (k ℕ.* j) :&: theInnerProof j {j≢0}
      where
      @0 theInnerProof : ∀ j -> @0 {j ≢0} -> ∀ n -> n ℕ.≥ suc (ℕ.pred (k ℕ.* j)) -> pow t n ≥ toReal (+ j / 1)
      theInnerProof (suc j-1) n n≥kj = let j = suc j-1 in begin
        (+ j / 1) ⋆         ≤⟨ tᵏⁿ≥n j ⟩
        pow t (k ℕ.* j)     ≤⟨ 1≤x∧m≤n⇒xᵐ≤xⁿ {t} {k ℕ.* j} {n} (<⇒≤ oneLtt) n≥kj ⟩
        pow t n              ∎

    @0 j⋆≄0 : (j : ℕ) {j≢0 : j ≢0} → ((+ j / 1) ⋆) ≄0
    j⋆≄0 j {j≢0} = ∣↥p∣≢0⇒p⋆≄0 (+ j / 1) j≢0

    @0 theProof : ∀ (j : ℕ) {@0 j≢0 : j ≢0} -> ∀ n -> n ℕ.≥ suc (proj₁ (lem j {j≢0})) -> pow r n ≤ toReal ((+ 1 / j) {j≢0})
    theProof (suc j-1) n n≥N = let j = suc j-1 in begin
      pow r n                      ≈⟨ pow-cong n (≃-sym (⁻¹-involutive {r} rNeq0 t≄0)) ⟩
      pow ((t ⁻¹) t≄0) n           ≈⟨ ≃-sym ([xⁿ]⁻¹≃[x⁻¹]ⁿ {t} t≄0 n (tⁿ≄0 n)) ⟩
      ((pow t n) ⁻¹) (tⁿ≄0 n)      ≤⟨ x≤y∧posx⇒y⁻¹≤x⁻¹ {(+ j / 1) ⋆} {pow t n} (proj₂ (lem j) n n≥N) (pospThenPosToRealp (+ j / 1) _) (j⋆≄0 j) (tⁿ≄0 n) ⟩
      (((+ j / 1) ⋆) ⁻¹) (j⋆≄0 j)  ≈⟨ ⋆-distrib-⁻¹ (+ j / 1) (j⋆≄0 j) ⟩
      (+ 1 / j) ⋆               ∎
{-# COMPILE AGDA2HS limitOfPositiveGeometricSequence #-}

abstract
  fastLimitOfPositiveGeometricSequence : ∀ (r : ℝ) -> (zeroℝ < r) Tuple.× (r < oneℝ) ->
                                           ∀ j -> {@0 j≢0 : j ≢0} -> Σ0 ℕ λ Nₖ-1 -> ∀ n -> n ℕ.≥ suc Nₖ-1 -> pow r n ≤ toReal ((+ 1 / j) {j≢0})
  fastLimitOfPositiveGeometricSequence = limitOfPositiveGeometricSequence
  {-# COMPILE AGDA2HS fastLimitOfPositiveGeometricSequence #-}

-- Aliases.
@0 0<r<1⇒rⁿ→0 fast-0<r<1⇒rⁿ→0 : ∀ {r : ℝ} -> (zeroℝ < r) Tuple.× (r < oneℝ) ->
                                           ∀ j -> {@0 j≢0 : j ≢0} -> Σ0 ℕ λ Nₖ-1 -> ∀ n -> n ℕ.≥ suc Nₖ-1 -> pow r n ≤ toReal ((+ 1 / j) {j≢0})
0<r<1⇒rⁿ→0 {r} = limitOfPositiveGeometricSequence r
fast-0<r<1⇒rⁿ→0 {r} = fastLimitOfPositiveGeometricSequence r

@0 x≤y∧nonNegx⇒xⁿ≤yⁿ : ∀ {x y} -> ∀ n -> x ≤ y -> NonNegative x -> pow x n ≤ pow y n
x≤y∧nonNegx⇒xⁿ≤yⁿ {x} {y} zero x≤y nonx = ≤-refl
x≤y∧nonNegx⇒xⁿ≤yⁿ {x} {y} (suc n) x≤y nonx = *-mono-≤ (nonNegx⇒nonNegxⁿ n nonx) nonx (x≤y∧nonNegx⇒xⁿ≤yⁿ n x≤y nonx) x≤y

-- A modified, compilable version of subst; for dependent types (predicates) with a single erased parameter.
-- p has to be hidden.
-- But this doesn't seem to work with agda2hs.
{-
substErased : {a : Level.Level} {A : Set a} {ℓ : Level.Level} {p : A → Set ℓ}
     {@0 x y : A} →
     @0 (x ≡ y) → p x → p y
substErased _ {_} {_} refl px = px
{-# COMPILE AGDA2HS substErased #-}
-}

-- We can see it will terminate (we call it with n instead of sucn). So let's simply cheat.
{-# TERMINATING #-}
powRespPos : ∀ (x : ℝ) -> ∀ n -> Positive x -> Positive (pow x n)
powRespPos x zero posx = pospThenPosToRealp (+ 1 / 1) _
-- We have to prove that suc (ℕ.pred sucn) ≡ sucn.
-- And for this, we have to prove somehow that sucn ≢ 0.
powRespPos x sucn posx = let n = ℕ.pred sucn in substErasedPos {pow x (suc n)} {pow x sucn}
                                                                (cong (pow x) (ℕP.suc[pred[n]]≡n {sucn} sucn≢0))
                                                                (posxAndyThenPosxTimesy (pow x n) x (powRespPos x n posx) posx)
  where
  -- You know what? Let's postulate that for now.
  postulate @0 sucn≢0 : sucn ≢ 0
  -- A special case of substErased which agda2hs accepts.
  substErasedPos : {@0 x y : ℝ} -> @0 (x ≡ y) -> Positive x -> Positive y
  substErasedPos refl px = px
{-# COMPILE AGDA2HS powRespPos #-}


-- Alias.
@0 posx⇒posxⁿ : ∀ {x} -> ∀ n -> Positive x -> Positive (pow x n)
posx⇒posxⁿ {x} = powRespPos x

{-
@0 x<y∧nonNegx⇒xⁿ<yⁿ : ∀ {x y} -> ∀ n -> {n ≢0} -> x < y -> NonNegative x -> pow x n < pow y n
x<y∧nonNegx⇒xⁿ<yⁿ {x} {y} 1 x<y nonx = *-monoʳ-<-pos (posp⇒posp⋆ 1ℚᵘ _) x<y
x<y∧nonNegx⇒xⁿ<yⁿ {x} {y} (suc (suc n)) x<y nonx = begin-strict
  pow x (suc n) * x ≤⟨ *-monoˡ-≤-nonNeg (<⇒≤ {x} {y} x<y) (nonNegx⇒nonNegxⁿ {x} (suc n) nonx) ⟩
  pow x (suc n) * y <⟨ *-monoˡ-<-pos {y} (0<x⇒posx {y} (≤0-<-trans {zeroℝ} {x} {y} (nonNegx⇒0≤x nonx) x<y)) (x<y∧nonNegx⇒xⁿ<yⁿ {x} {y} (suc n) x<y nonx) ⟩
  pow y (suc n) * y  ∎
  where open ≤-Reasoning
-}
@0 ∣xⁿ∣≃∣x∣ⁿ : ∀ x -> ∀ n -> ∣ pow x n ∣ ≃ pow ∣ x ∣ n
∣xⁿ∣≃∣x∣ⁿ x zero = nonNegx⇒∣x∣≃x (0≤x⇒nonNegx (p≤q⇒p⋆≤q⋆ 0ℚᵘ 1ℚᵘ (ℚP.nonNegative⁻¹ _)))
∣xⁿ∣≃∣x∣ⁿ x (suc n) = begin
  ∣ pow x n * x ∣     ≈⟨ ∣x*y∣≃∣x∣*∣y∣ (pow x n) x ⟩
  ∣ pow x n ∣ * ∣ x ∣ ≈⟨ *-congʳ (∣xⁿ∣≃∣x∣ⁿ x n) ⟩
  pow ∣ x ∣ n * ∣ x ∣  ∎
  where open ≃-Reasoning

{-
This proof is an altered and further constructivized version of the proof at 
https://math.stackexchange.com/questions/1253129/as-the-limit-of-n-goes-to-infinity-prove-that-xn-0-if-operatornameabs  

Proposition:
  If ∣r∣ < 1, then (rⁿ)→0.
Proof:
  Let ε∈ℝ⁺ such that ∣r∣ < ∣r∣ + ε and 0 < ∣r∣ + ε < 1. If ([∣r∣ + ε]ⁿ)→0, then
(∣r∣ⁿ)→0, and so (rⁿ)→0. Let t = (∣r∣ + ε)⁻¹. Then t = 1 + (t - 1), where t - 1 > 0.
By the Archimedean Property, there is k∈ℕ such that k(t - 1) > 1. We have, for n∈ℕ:
             tᵏⁿ = (1 + (t-1))ᵏⁿ
                 ≥ 1 + k(t-1)n   by Bernoulli's inequality
                 > 1 + n         since k(t-1) > 1
                 > n,
so tᵏⁿ > n for all n∈ℕ (⋆).
  Let j∈ℕ and let N = k * j. Let n ≥ N. Then (∣r∣ + ε)ⁿ ≤ j⁻¹ ⇔ j ≤ tⁿ. We have:
           j < tᵏʲ by ⋆
             ≤ tⁿ  since n ≥ kj and (tⁿ) is an increasing sequence.
Thus ([∣r∣ + ε]ⁿ)→0, and so (rⁿ)→0.                                               □ -}

limitOfGeometricSequence : ∀ (r : ℝ) -> ∣ r ∣ < oneℝ -> ConvergesTo (λ n -> pow r n) zeroℝ
limitOfGeometricSequence r absrLtOne = MkCon (λ k {k≢0} -> let Nₖ = suc (proj₁ (getNₖ k {k≢0})) in ℕ.pred Nₖ :&: theProof k {k≢0})
  where
    open ≤-Reasoning
    εpack : Σ' ℝ λ ε -> (Positive ε) Tuple.× ((∣ r ∣ < (∣ r ∣ + ε)) Tuple.× ((∣ r ∣ + ε) < oneℝ))
    εpack = densityOfℝ (abs r) (oneℝ) absrLtOne
    ε : ℝ
    ε = proj₁' εpack
    εprop : (Positive ε) Tuple.× ((∣ r ∣ < (∣ r ∣ + ε)) Tuple.× ((∣ r ∣ + ε) < oneℝ))
    εprop = proj₂' εpack

    zeroLtAbsrPlusε : zeroℝ < ∣ r ∣ + ε
    zeroLtAbsrPlusε = ltLe0Trans zeroℝ ε (abs r + ε) (posxThenZeroLtx ε (Tuple.fst εprop)) (≤-respˡ-≃ (+-identityˡ ε) (+-monoˡ-≤ ε (0≤∣x∣ r)))

    @0 ∣r∣≤∣r∣+ε : ∣ r ∣ ≤ ∣ r ∣ + ε
    ∣r∣≤∣r∣+ε = begin
      ∣ r ∣      ≈⟨ ≃-sym (+-identityʳ ∣ r ∣) ⟩
      ∣ r ∣ + zeroℝ ≤⟨ +-monoʳ-≤ ∣ r ∣ {zeroℝ} {ε} (nonNegx⇒0≤x (pos⇒nonNeg (Tuple.fst εprop))) ⟩
      ∣ r ∣ + ε   ∎

    getNₖ = fastLimitOfPositiveGeometricSequence (abs r + ε) (zeroLtAbsrPlusε Tuple., (Tuple.snd (Tuple.snd (εprop))))

    @0 theProof : ∀ (k : ℕ) {k≢0 : k ≢0} ->
               (n : ℕ) →
               n ℕ.≥ suc (ℕ.pred (suc (proj₁ (getNₖ k {k≢0})))) →
               abs (pow r n - zeroℝ) ≤ toReal ((+ 1 / k) {k≢0})
    theProof (suc k-1) n n≥Nₖ = let k = suc k-1 in begin
      ∣ pow r n - zeroℝ ∣  ≈⟨ ∣-∣-cong (solve 1 (λ x -> x ⊖ Κ 0ℚᵘ ⊜ x) ≃-refl (pow r n)) ⟩
      ∣ pow r n ∣       ≈⟨ ∣xⁿ∣≃∣x∣ⁿ r n ⟩
      pow ∣ r ∣ n       ≤⟨ x≤y∧nonNegx⇒xⁿ≤yⁿ {∣ r ∣} {∣ r ∣ + ε} n ∣r∣≤∣r∣+ε (nonNeg∣x∣ r) ⟩
      pow (∣ r ∣ + ε) n ≤⟨ proj₂ (getNₖ k) n n≥Nₖ ⟩
      (+ 1 / k) ⋆        ∎
{-# COMPILE AGDA2HS limitOfGeometricSequence #-}

abstract
  @0 fastLimitOfGeometricSequence : ∀ (r : ℝ) -> ∣ r ∣ < oneℝ -> ConvergesTo (λ n -> pow r n) zeroℝ
  fastLimitOfGeometricSequence = limitOfGeometricSequence

-- Aliases.
@0 ∣r∣<1⇒rⁿ→0 fast-∣r∣<1⇒rⁿ→0 : ∀ {r : ℝ} -> ∣ r ∣ < oneℝ -> ConvergesTo (λ n -> pow r n) zeroℝ
∣r∣<1⇒rⁿ→0 {r} = limitOfGeometricSequence r
fast-∣r∣<1⇒rⁿ→0 {r} = fastLimitOfGeometricSequence r

private
  oneMinusrNeqZero : ∀ r -> ∣ r ∣ < oneℝ -> (oneℝ - r) ≄ zeroℝ
  oneMinusrNeqZero r absrLtOne = Either.Right (xLtyThenZeroLtyMinusx r oneℝ (Tuple.snd (absxLtyThenNegyLtxLty r oneℝ absrLtOne)))
  {-# COMPILE AGDA2HS oneMinusrNeqZero #-}

{-
Using the new solver, we can delete pretty much half the proof!
If the solver gets updated to a field solver, we can delete almost the entire thing.
-}
-- Gets stuck here too. (Inverses and negates don't seem to like each other now.)
postulate @0 geometric-sum : ∀ {r} -> ∀ n -> (∣r∣<1 : ∣ r ∣ < oneℝ) -> sum (λ i -> pow r i) 0 n ≃ (oneℝ - pow r n) * ((oneℝ - r) ⁻¹) (oneMinusrNeqZero r ∣r∣<1)
{-
geometric-sum {r} zero ∣r∣<1 = let [1-r]⁻¹ = ((oneℝ - r) ⁻¹) (oneMinusrNeqZero r ∣r∣<1) in
                                             solve 1 (λ x -> Κ 0ℚᵘ ⊜ (Κ 1ℚᵘ ⊖ Κ 1ℚᵘ) ⊗ x) ≃-refl [1-r]⁻¹
geometric-sum {r} (suc n) ∣r∣<1 = let [1-r]⁻¹ = ((oneℝ - r) ⁻¹) (oneMinusrNeqZero r ∣r∣<1) in begin
  sum0 (pow r) n + pow r n                                  ≈⟨ +-cong {sum0 (pow r) n} {(oneℝ - pow r n) * [1-r]⁻¹}
                                                             {pow r n} {pow r n * (oneℝ - r) * [1-r]⁻¹}
                                                             (geometric-sum {r} n ∣r∣<1)
                                                             (≃-sym (≃-trans (≃-trans
                                                             (*-assoc (pow r n) (oneℝ - r) [1-r]⁻¹)
                                                             (*-congˡ {pow r n} {(oneℝ - r) * [1-r]⁻¹} {oneℝ} (*-inverseʳ (oneℝ - r) (oneMinusrNeqZero r ∣r∣<1))))
                                                             (*-identityʳ (pow r n)))) ⟩
  (oneℝ - pow r n) * [1-r]⁻¹ + pow r n * (oneℝ - r) * [1-r]⁻¹ ≈⟨ solve 3 (λ r rⁿ [1-r]⁻¹ ->
                                                             (Κ 1ℚᵘ ⊖ rⁿ) ⊗ [1-r]⁻¹ ⊕ rⁿ ⊗ (Κ 1ℚᵘ ⊖ r) ⊗ [1-r]⁻¹ ⊜
                                                             (Κ 1ℚᵘ ⊖ (rⁿ ⊗ r)) ⊗ [1-r]⁻¹)
                                                             ≃-refl r (pow r n) [1-r]⁻¹ ⟩
  (oneℝ - pow r (suc n)) * [1-r]⁻¹                           ∎
  where open ≃-Reasoning
-}

geometricSeriesConverges : ∀ (r : ℝ) -> (∣r∣<1 : ∣ r ∣ < oneℝ) -> ConvergesTo (seriesOf (λ i -> pow r i)) ((oneℝ - r) \< (oneMinusrNeqZero r ∣r∣<1))
geometricSeriesConverges r absrLtOne = equalMembersEqualLimits {λ n -> (oneℝ - pow r n) * oneMinusrInv} {seriesOf rⁱ}
                            ((λ @0 {(suc n-1) -> let n = suc n-1 in ≃-sym (geometric-sum {r} n absrLtOne)}))
                             (oneMinusrInv :^: convergenceToEqual {λ n → (oneℝ - pow r n) * oneMinusrInv} {oneℝ * oneMinusrInv} {oneMinusrInv}
                             (limitOfProduct oneMinusrⁱ {λ i → oneMinusrInv} oneMinusrⁱConToOne oneMinusrInvConToOneMinusrInv) (*-identityˡ oneMinusrInv))
  where
    open ≃-Reasoning
    oneMinusrⁱ : ℕ -> ℝ
    oneMinusrⁱ = λ i -> oneℝ - pow r i
    oneMinusrInv = (oneℝ - r) \< (oneMinusrNeqZero r absrLtOne)
    @0 rⁱ : ℕ -> ℝ
    rⁱ = λ i -> pow r i
    rⁱConToZero : IsConvergent rⁱ
    rⁱConToZero = zeroℝ :^: limitOfGeometricSequence r absrLtOne
    oneConToOne : IsConvergent (λ _ -> oneℝ)
    oneConToOne = oneℝ :^: limitOfConst {λ _ -> oneℝ} {oneℝ} λ @0 {(suc n-1) -> ≃-refl}
    oneMinusrInvConToOneMinusrInv : IsConvergent (λ _ -> oneMinusrInv)
    oneMinusrInvConToOneMinusrInv = oneMinusrInv :^: limitOfConst {λ i -> oneMinusrInv} {oneMinusrInv} λ @0 {(suc n-1) -> ≃-refl}
    oneMinusrⁱConToOne : IsConvergent oneMinusrⁱ
    oneMinusrⁱConToOne = oneℝ :^: convergenceToEqual (limitOfSum oneConToOne (negate zeroℝ :^: limitOfNegate rⁱConToZero)) (≃-trans (+-congʳ oneℝ (≃-sym 0≃-0)) (+-identityʳ oneℝ))
{-# COMPILE AGDA2HS geometricSeriesConverges #-}

abstract
  @0 fastGeometricSeriesConverges : ∀ (r : ℝ) -> (∣r∣<1 : ∣ r ∣ < oneℝ) -> ConvergesTo (seriesOf (λ i -> pow r i)) ((oneℝ - r) \< (oneMinusrNeqZero r ∣r∣<1))
  fastGeometricSeriesConverges = geometricSeriesConverges

@0 geometric-series-converges fast-geometric-series-converges :
     ∀ {r} -> (∣r∣<1 : ∣ r ∣ < oneℝ) -> ConvergesTo (seriesOf (λ i -> pow r i)) (((oneℝ - r) ⁻¹) (oneMinusrNeqZero r ∣r∣<1))
geometric-series-converges {r} = geometricSeriesConverges r
fast-geometric-series-converges {r} = fastGeometricSeriesConverges r

geometricSeriesIsConvergent : ∀ (r : ℝ) -> ∣ r ∣ < oneℝ -> IsConvergent (seriesOf (λ i -> pow r i))
geometricSeriesIsConvergent r absrLtOne = limit :^: theProof
  where
  -- it got stuck until I created a helper function for the limit
  limit : ℝ
  limit = ((oneℝ - r) \< (oneMinusrNeqZero r absrLtOne))
  theProof : ConvergesTo (seriesOf (λ i -> pow r i)) limit
  theProof = geometricSeriesConverges r absrLtOne
{-# COMPILE AGDA2HS geometricSeriesIsConvergent #-}

abstract
  fastGeometricSeriesIsConvergent : ∀ (r : ℝ) -> ∣ r ∣ < oneℝ -> IsConvergent (seriesOf (λ i -> pow r i))
  fastGeometricSeriesIsConvergent = geometricSeriesIsConvergent
  {-# COMPILE AGDA2HS fastGeometricSeriesIsConvergent #-}

@0 geometric-series-isConvergent fast-geometric-series-isConvergent :
  ∀ {r : ℝ} -> ∣ r ∣ < oneℝ -> IsConvergent (seriesOf (λ i -> pow r i))
geometric-series-isConvergent {r} = geometricSeriesIsConvergent r
fast-geometric-series-isConvergent {r} = fastGeometricSeriesIsConvergent r

@0 sumcxₙ≃csumxₙ : ∀ (xs : ℕ -> ℝ) -> ∀ (c : ℝ) -> ∀ (m n : ℕ) -> sum (λ i -> c * xs i) m n ≃ c * sum xs m n
sumcxₙ≃csumxₙ xs c zero n = lem n
  where
    open ≃-Reasoning
    lem : ∀ n -> sum0 (λ i -> c * xs i) n ≃ c * sum0 xs n
    lem 0 = ≃-sym (*-zeroʳ c)
    lem (suc n) = begin
      sum0 (λ i -> c * xs i) n + c * xs n ≈⟨ +-congˡ (c * xs n) (lem n) ⟩
      c * sum0 xs n + c * xs n            ≈⟨ ≃-sym (*-distribˡ-+ c (sum0 xs n) (xs n)) ⟩
      c * (sum0 xs n + xs n)               ∎
sumcxₙ≃csumxₙ xs c (suc m) n = begin
  sum0 (λ i -> c * xs i) n - (sum0 (λ i -> c * xs i) m + c * xs m) ≈⟨ +-cong (sumcxₙ≃csumxₙ xs c 0 n)
                                                                  (-‿cong (≃-trans
                                                                  (+-congˡ (c * xs m) (sumcxₙ≃csumxₙ xs c 0 m))
                                                                  (≃-sym (*-distribˡ-+ c (sum0 xs m) (xs m))))) ⟩
  c * sum0 xs n - (c * (sum0 xs m + xs m))                         ≈⟨ solve 3 (λ c sum0ⁿxᵢ sum0ᵐ⁺¹xᵢ ->
                                                                  c ⊗ sum0ⁿxᵢ ⊖ c ⊗ sum0ᵐ⁺¹xᵢ ⊜ c ⊗ (sum0ⁿxᵢ ⊖ sum0ᵐ⁺¹xᵢ) )
                                                                  ≃-refl c (sum0 xs n) (sum0 xs (suc m)) ⟩
  c * (sum0 xs n - (sum0 xs m + xs m))                              ∎
  where open ≃-Reasoning

abstract
  @0 fast-sumcxₙ≃csumxₙ : ∀ (xs : ℕ -> ℝ) -> ∀ (c : ℝ) -> ∀ (m n : ℕ) -> sum (λ i -> c * xs i) m n ≃ c * sum xs m n
  fast-sumcxₙ≃csumxₙ = sumcxₙ≃csumxₙ

--for proposition-3-6-1
abstract
  private
    @0 take-out-const : (k c : ℝ) (n : ℕ) → @0 {n ≢0} →
              k * seriesOf (λ n₁ → pow c n₁) n ≃ seriesOf (λ n₁ → k * pow c n₁) n
    take-out-const k c (suc n-1) = let n = suc n-1 in ≃-sym (fast-sumcxₙ≃csumxₙ (λ i -> pow c i) k 0 n)

{- [7] -}

proposition361 : ∀ (xs : ℕ -> ℝ) -> ∀ (c : ℝ) -> (zeroℝ < c) Tuple.× (c < oneℝ) ->
                      (Σ0 ℕ λ lM1 -> ∀ n -> n ℕ.≥ suc lM1 -> ∣ xs (suc n) ∣ ≤ c * ∣ xs n ∣) ->
                      IsConvergent (seriesOf xs)
proposition361 xs c (zeroLtc Tuple., cLtOne) (lM1 :&: hyp) = proposition35 xs (λ n -> const * pow c n) (limit :^: part1)
                                                     (ℕ.pred l :&: λ n n≥l -> part2 n (≤⇒≡∨< l n n≥l))
  where
    open ≤-Reasoning
    l : ℕ
    l = suc lM1
    posc : Positive c
    posc = zeroLtxThenPosx c zeroLtc
    cᴺNeqZero : pow c l ≄ zeroℝ
    cᴺNeqZero = Either.Right (posxThenZeroLtx (pow c l) (powRespPos c l posc))
    cPowNegN : ℝ
    cPowNegN = (pow c l) \< cᴺNeqZero
    abscLtOne : ∣ c ∣ < oneℝ
    abscLtOne = negyLtxLtyThenAbsxLty c oneℝ (ltTrans (negate oneℝ) zeroℝ c (ltRespLEq zeroℝ (toReal (-[1+ 0 ] / 1)) (negate oneℝ) (⋆-distrib-neg 1ℚᵘ)
            (pLtqThenToRealpLtToRealq (ℚ.- 1ℚᵘ) (+ 0 / 1) (ℚP.negative⁻¹ _))) zeroLtc Tuple., cLtOne)

    powSeries : ℕ -> ℝ
    powSeries = seriesOf (pow c)
    -- λ n → pow c n slowed it down here
    consumcⁿ : IsConvergent powSeries
    consumcⁿ = fastGeometricSeriesIsConvergent c abscLtOne

    -- This one is used many times.
    const : ℝ
    const = abs (xs l) * cPowNegN

    -- We have to be quite verbose here in order to make it typecheck on time.
    @0 seq1 seq2 : ℕ -> ℝ
    seq1 = λ n → const * powSeries n
    seq2 = seriesOf (λ n → (const * pow c n))

    -- The common limit in part0 and part1.
    limit : ℝ
    limit = const * (proj₁' consumcⁿ)

    part0 : ConvergesTo seq1 limit
    part0 = limitOfProduct (λ _ → const) {powSeries}
              (const :^: theInnerProof)
              consumcⁿ
      where
      theInnerProof : ConvergesTo (λ _ → const) const
      theInnerProof = fastLimitOfConst {λ _ -> const} {const} (λ @0 {(suc n-1) -> ≃-refl})

    part1 : ConvergesTo seq2 limit
    part1 = fastEqualMembersEqualLimits
                    {seq1}
                    {seq2}
                    eqProof
                    (limit :^: part0)    -- part0 had to be put into a hole, but limit had to be given
      where
      -- This is erased, so we can leave it for later.
      postulate @0 eqProof : ∀ n -> @0 {n ≢0} -> seq1 n ≃ seq2 n
      -- eqProof = {!take-out-const const c!}

    {-
    part0 : (λ i → ∣ xs l ∣ * cPowNegN * seriesOf (λ n → pow c n) i IsConvergent
    part0 = ∣ xs l ∣ * cPowNegN * (proj₁ consumcⁿ) , {!limitOfProduct {λ i → ∣ xs l ∣ * cPowNegN} {seriesOf (λ i → pow c i)}
            (∣ xs l ∣ * cPowNegN , {!limitOfConst {λ i -> ∣ xs l ∣ * cPowNegN} {∣ xs l ∣ * cPowNegN} (λ @0 {(suc n-1) -> ≃-refl})!})
            consumcⁿ!}
    @0 take-out-const : (n : ℕ) {n≢0 : n ≢0} → sum0 (λ i → ∣ xs l ∣ * cPowNegN * pow c i) n ≃ ∣ xs l ∣ * cPowNegN * sum0 (λ i → pow c i) n
    take-out-const zero {()}
    take-out-const (suc n-1) {_} = let n = suc n-1 in {!fast-sumcxₙ≃csumxₙ (λ i -> pow c i) (∣ xs l ∣ * cPowNegN) 0 n!}
    part1 : seriesOf (λ n → ∣ xs l ∣ * cPowNegN * pow c n IsConvergent
    part1 = ∣ xs l ∣ * cPowNegN * (proj₁ consumcⁿ) ,
            {!equalMembersEqualLimits {λ i → ∣ xs l ∣ * cPowNegN * seriesOf (λ n → pow c n) i} {seriesOf (λ n → ∣ xs l ∣ * cPowNegN * pow c n)} {!take-out-const!} part0!}
    -}

    -- This too.
    postulate @0 part2 : ∀ n -> l ≡ n ⊎ l ℕ.< n -> ∣ xs n ∣ ≤ const * pow c n
    {-
    part2 .(suc lM1) (inj₁ refl) = {!≤-reflexive {abs (xs l)} {const * pow c l} (≃-sym (begin-equality
      ∣ xs l ∣ * cPowNegN * pow c l                 ≈⟨ *-assoc ∣ xs l ∣ cPowNegN (pow c l) ⟩
      ∣ xs l ∣ * (cPowNegN * pow c l)               ≈⟨ *-congˡ {∣ xs l ∣} {cPowNegN * pow c l} {oneℝ}
                                                  (*-inverseˡ (pow c l) cᴺNeqZero) ⟩
      ∣ xs l ∣ * oneℝ                            ≈⟨ *-identityʳ ∣ xs l ∣ ⟩
      ∣ xs l ∣                                  ∎))!}
    part2 (suc n) (inj₂ (ℕ.s≤s l<n)) = {!begin
      ∣ xs (suc n) ∣                 ≤⟨ hyp n l<n ⟩
      c * ∣ xs n ∣                   ≤⟨ *-monoˡ-≤-nonleg {∣ xs n ∣} {c} {∣ xs l ∣ * cPowNegN * pow c n}
                                        (part2 n (≤⇒≡∨< l n l<n)) (pos⇒nonleg posc) ⟩
      c * (∣ xs l ∣ * cPowNegN * pow c n) ≈⟨ solve 4 (λ a b c d -> a ⊗ (b ⊗ c ⊗ d) ⊜ b ⊗ c ⊗ (d ⊗ a))
                                        ≃-refl c ∣ xs l ∣ cPowNegN (pow c n) ⟩
      ∣ xs l ∣ * cPowNegN * pow c (suc n)  ∎!}
    -}
{-# COMPILE AGDA2HS proposition361 #-}

-- Alias.
proposition-3-6-1 : ∀ {xs : ℕ -> ℝ} -> ∀ {c : ℝ} -> (zeroℝ < c) Tuple.× (c < oneℝ) ->
                      (Σ0 ℕ λ lM1 -> ∀ n -> n ℕ.≥ suc lM1 -> ∣ xs (suc n) ∣ ≤ c * ∣ xs n ∣) ->
                      IsConvergent (seriesOf xs)
proposition-3-6-1 {xs} {c} = proposition361 xs c

{-
∣c∣>0⇒sumc-isDivergent : ∀ {c} -> ∣ c ∣ > zeroℝ -> seriesOf (λ i -> c) isDivergent
∣c∣>0⇒sumc-isDivergent {c} ∣c∣>0 = ∣ c ∣ , div* (0<x⇒posx ∣c∣>0)
                           (λ @0 {k -> suc k , k , ℕP.n≤1+n k , ℕP.≤-refl , ≤-reflexive (∣-∣-cong (≃-sym (begin
  sum0 (λ i -> c) k + c - sum0 (λ i -> c) k   ≈⟨ solve 2 (λ a b -> a ⊕ b ⊖ a ⊜ b)
                                             ≃-refl (sum0 (λ i -> c) k) c ⟩
  c                                        ∎)))})
  where open ≃-Reasoning

{- [8] -}
proposition-3-6-2 : ∀ {xs : ℕ -> ℝ} -> ∀ {c} -> oneℝ < c ->
                    (∃ λ N-1 -> ∀ n -> n ℕ.≥ suc N-1 -> ∣ xs (suc n) ∣ > c * ∣ xs n ∣) ->
                    seriesOf xs isDivergent
proposition-3-6-2 {xs} {c} 1<c (N-1 , hyp) = subsequence-divergence-test {xs} (∣ xs (suc N) ∣ ,
                                             (λ n -> xs (n ℕ.+ suc N)) , 0<x⇒posx {∣ xs (suc N) ∣} part1 ,
                                             subseq* ((λ n -> n ℕ.+ suc N) , (λ n -> ≃-refl) , (λ n -> ℕP.n<1+n (n ℕ.+ suc N))) ,
                                             λ n -> ≤-trans {∣ xs (suc N) ∣} {pow c (n ℕ.+ suc N) * c⁻ᴺ⁻¹ * ∣ xs (suc N) ∣} {∣ xs (n ℕ.+ suc N) ∣}
                                                    (part2-1 (n ℕ.+ suc N) (ℕP.m≤n+m (suc N) n))
                                                    (part2-2 (n ℕ.+ suc N) (≤⇒≡∨< (suc N) (n ℕ.+ suc N) (ℕP.m≤n+m (suc N) n))))
  where
    open ≤-Reasoning
    N = suc N-1
    n-N-1 = λ n -> ℤ.∣ + n ℤ.- + (suc N) ∣
    cᴺ⁺¹≄0 = inj₂ (posx⇒0<x {pow c (suc N)} (posx⇒posxⁿ {c} (suc N) (0<x⇒posx {c}
             (<-trans (pLtqThenToRealpLtToRealq 0ℚᵘ 1ℚᵘ (ℚP.positive⁻¹ _)) 1<c))))
    c⁻ᴺ⁻¹ = ((pow c (suc N)) ⁻¹) cᴺ⁺¹≄0
    posc = 0<x⇒posx (≤-<-trans (p≤q⇒p⋆≤q⋆ 0ℚᵘ 1ℚᵘ (ℚP.nonNegative⁻¹ _)) 1<c)

    part1 : ∣ xs (suc N) ∣ > zeroℝ
    part1 = begin-strict
      zeroℝ                 ≤⟨ nonNegx⇒0≤x (nonNegx,y⇒nonNegx*y (pos⇒nonNeg posc) (nonNeg∣x∣ (xs N))) ⟩
      c * ∣ xs N ∣       <⟨ hyp N ℕP.≤-refl ⟩
      ∣ xs (suc N) ∣      ∎

    part2-1 : ∀ n -> suc N ℕ.≤ n -> pow c n * c⁻ᴺ⁻¹ * ∣ xs (suc N) ∣ ≥ ∣ xs (suc N) ∣
    part2-1 n N+1≤n = begin
      ∣ xs (suc N) ∣                         ≈⟨ ≃-sym (*-identityˡ ∣ xs (suc N) ∣) ⟩
      oneℝ * ∣ xs (suc N) ∣                    ≈⟨ ≃-sym (*-congʳ {∣ xs (suc N) ∣} {pow c (suc N) * c⁻ᴺ⁻¹} {oneℝ}
                                                (*-inverseʳ (pow c (suc N)) cᴺ⁺¹≄0)) ⟩
      pow c (suc N) * c⁻ᴺ⁻¹ * ∣ xs (suc N) ∣ ≤⟨ *-monoʳ-≤-nonNeg {pow c (suc N) * c⁻ᴺ⁻¹} {∣ xs (suc N) ∣} {pow c n * c⁻ᴺ⁻¹}
                                                (*-monoʳ-≤-nonNeg {pow c (suc N)} {c⁻ᴺ⁻¹} {pow c n}
                                                (1≤x∧m≤n⇒xᵐ≤xⁿ {c} (<⇒≤ 1<c) N+1≤n)
                                                (nonNegx⇒nonNegx⁻¹ {pow c (suc N)} (nonNegx⇒nonNegxⁿ {c} (suc N)
                                                (pos⇒nonNeg {c} posc)) cᴺ⁺¹≄0))
                                                (nonNeg∣x∣ (xs (suc N))) ⟩
      pow c n * c⁻ᴺ⁻¹ * ∣ xs (suc N) ∣        ∎

    part2-2 : ∀ n -> suc N ≡ n ⊎ suc N ℕ.< n -> ∣ xs n ∣ ≥ pow c n * c⁻ᴺ⁻¹ * ∣ xs (suc N) ∣
    part2-2 .(suc (suc N-1)) (inj₁ refl) = begin
      pow c (suc N) * c⁻ᴺ⁻¹ * ∣ xs (suc N) ∣ ≈⟨ *-congʳ {∣ xs (suc N) ∣} {pow c (suc N) * c⁻ᴺ⁻¹} {oneℝ}
                                                (*-inverseʳ (pow c (suc N)) cᴺ⁺¹≄0) ⟩
      oneℝ * ∣ xs (suc N) ∣                    ≈⟨ *-identityˡ ∣ xs (suc N) ∣ ⟩
      ∣ xs (suc N) ∣                          ∎
    part2-2 (suc n) (inj₂ (ℕ.s≤s N<n)) = begin
      pow c n * c * c⁻ᴺ⁻¹ * ∣ xs (suc N) ∣   ≈⟨ solve 4 (λ x y z w -> x ⊗ y ⊗ z ⊗ w ⊜ y ⊗ (x ⊗ z ⊗ w))
                                                ≃-refl (pow c n) c c⁻ᴺ⁻¹ ∣ xs (suc N) ∣ ⟩
      c * (pow c n * c⁻ᴺ⁻¹ * ∣ xs (suc N) ∣) ≤⟨ *-monoˡ-≤-nonNeg {pow c n * c⁻ᴺ⁻¹ * ∣ xs (suc N) ∣} {c} {∣ xs n ∣}
                                                (part2-2 n (≤⇒≡∨< (suc N) n N<n))
                                                (pos⇒nonNeg {c} posc) ⟩
      c * ∣ xs n ∣                           <⟨ hyp n (ℕP.≤-trans (ℕP.n≤1+n N) N<n) ⟩
      ∣ xs (suc n) ∣                          ∎

ε-cauchy-convergence : ∀ {xs : ℕ -> ℝ} -> (∀ {ε} -> ε > zeroℝ -> ∃ λ N-1 -> ∀ m n -> m ℕ.> n -> n ℕ.≥ suc N-1 -> ∣ xs m - xs n ∣ ≤ ε) -> IsConvergent xs
ε-cauchy-convergence {xs} hyp = cauchy-convergence (λ @0 {(suc k-1) -> let k = suc k-1 in
                                hyp (pLtqThenToRealpLtToRealq 0ℚᵘ (+ 1 / k) (ℚP.positive⁻¹ _))})

abstract
  fast-ε-cauchy-convergence : ∀ {xs : ℕ -> ℝ} -> (∀ {ε} -> ε > zeroℝ -> ∃ λ N-1 -> ∀ m n -> m ℕ.> n -> n ℕ.≥ suc N-1 -> ∣ xs m - xs n ∣ ≤ ε) -> IsConvergent xs
  fast-ε-cauchy-convergence = ε-cauchy-convergence

ε-cauchy : ∀ {xs : ℕ -> ℝ} -> (∀ {ε} -> ε > zeroℝ -> ∃ λ N-1 -> ∀ m n -> m ℕ.> n -> n ℕ.≥ suc N-1 -> ∣ xs m - xs n ∣ ≤ ε) -> IsCauchy xs
ε-cauchy {xs} hyp = fast-convergent⇒cauchy (ε-cauchy-convergence hyp)

abstract
  fast-0<x⇒posx : ∀ {x} -> zeroℝ < x -> Positive x
  fast-0<x⇒posx = 0<x⇒posx
  
ε-from-convergence-cauchy : ∀ {xs : ℕ -> ℝ} -> (xₙ→ℓ : IsConvergent xs) ->
                            ∀ {ε : ℝ} -> ε > zeroℝ -> ∃ λ N-1 -> ∀ m n -> m ℕ.> n -> n ℕ.≥ suc N-1 -> ∣ xs m - xs n ∣ ≤ ε
ε-from-convergence-cauchy {xs} xₙ→ℓ {ε} ε>0 = let xₙ-cauchy = fast-cauchy-getter (fast-convergent⇒cauchy xₙ→ℓ)
                                                      ; arch = fastArchimedeanℝ₂ (fast-0<x⇒posx ε>0); k = suc (proj₁ arch) in
                                             proj₁ (xₙ-cauchy k) , λ m n m>n n≥N -> begin
  ∣ xs m - xs n ∣ ≤⟨ proj₂ (xₙ-cauchy k) m n
                     (ℕP.<⇒≤ (ℕP.<-transʳ n≥N m>n)) n≥N ⟩
  (+ 1 / k) ⋆     <⟨ proj₂ arch ⟩
  ε                ∎
  where open ≤-Reasoning

abstract
  fast-ε-from-convergence-cauchy : ∀ {xs : ℕ -> ℝ} -> (xₙ→ℓ : IsConvergent xs) ->
                                   ∀ {ε : ℝ} -> ε > zeroℝ -> ∃ λ N-1 -> ∀ m n -> m ℕ.> n -> n ℕ.≥ suc N-1 -> ∣ xs m - xs n ∣ ≤ ε
  fast-ε-from-convergence-cauchy = ε-from-convergence-cauchy

sumᵀ-mono-<-weak : ∀ {xs ys : ℕ -> ℝ} -> ∀ {m n} -> (m<n : m ℕ.< n) ->
                 (∀ k -> m ℕ.≤ k × k ℕ.≤ n -> xs k < ys k) ->
                 sumᵀ xs m n (ℕP.<⇒≤ m<n) < sumᵀ ys m n (ℕP.<⇒≤ m<n)
sumᵀ-mono-<-weak {xs} {ys} {m} {suc n} m<n hyp with ≤⇒≡∨< m (suc n) (ℕP.<⇒≤ m<n)
... | inj₁ refl = ⊥-elim (ℕP.<-irrefl refl m<n)
... | inj₂ (ℕ.s≤s y) = begin-strict
  sumᵀ xs m n y + xs n ≤⟨ +-monoˡ-≤ (xs n) (sumᵀ-mono-≤-weak y (λ k m≤k≤n -> <⇒≤ (hyp k
                        (proj₁ m≤k≤n , ℕP.≤-trans (proj₂ m≤k≤n) (ℕP.n≤1+n n))))) ⟩
  sumᵀ ys m n y + xs n <⟨ +-monoʳ-< (sumᵀ ys m n y) (hyp n (y , ℕP.n≤1+n n)) ⟩
  sumᵀ ys m n y + ys n  ∎
  where open ≤-Reasoning

sum-mono-<-weak : ∀ {xs ys : ℕ -> ℝ} -> ∀ (m n : ℕ) -> (m<n : m ℕ.< n) ->
           (∀ k -> m ℕ.≤ k × k ℕ.≤ n -> xs k < ys k) ->
           sum xs m n < sum ys m n
sum-mono-<-weak {xs} {ys} m n m<n hyp = let m≤n = ℕP.<⇒≤ m<n in begin-strict
  sum xs m n      ≈⟨ sum-to-sumᵀ xs m n m≤n ⟩
  sumᵀ xs m n m≤n <⟨ sumᵀ-mono-<-weak m<n hyp ⟩
  sumᵀ ys m n m≤n ≈⟨ ≃-sym (sum-to-sumᵀ ys m n m≤n) ⟩
  sum ys m n       ∎
  where open ≤-Reasoning

sum-mono-< : ∀ {xs ys : ℕ -> ℝ} -> ∀ (m n : ℕ) -> (m<n : m ℕ.< n) ->
           (∀ k -> xs k < ys k) -> sum xs m n < sum ys m n
sum-mono-< {xs} {ys} m n m<n hyp = sum-mono-<-weak m n m<n (λ k m≤k≤n -> hyp k)

0<x,y⇒0<x*y : ∀ {x y} -> zeroℝ < x -> zeroℝ < y -> zeroℝ < x * y
0<x,y⇒0<x*y 0<x 0<y = posx⇒0<x (posxAndyThenPosxTimesy (0<x⇒posx 0<x) (0<x⇒posx 0<y))

abstract
  fast-0<x,y⇒0<x*y : ∀ {x y} -> zeroℝ < x -> zeroℝ < y -> zeroℝ < x * y
  fast-0<x,y⇒0<x*y = 0<x,y⇒0<x*y

lemma-3-7-1 : ∀ {as xs : ℕ -> ℝ} -> ∀ {c : ℝ} -> zeroℝ < c ->
              (0<aₙ,xₙ : ∀ n -> (zeroℝ < as n) × (zeroℝ < xs n)) ->
              (λ n -> as n * xs n) ConvergesTo zeroℝ ->
              (∃ λ N-1 -> ∀ n -> n ℕ.≥ suc N-1 -> as n * xs n * (xs (suc n) ⁻¹) (inj₂ (proj₂ (0<aₙ,xₙ (suc n)))) - as (suc n) ≥ c) ->
              IsConvergent (seriesOf xs)
lemma-3-7-1 {as} {xs} {c} 0<c 0<aₙ,xₙ aₙxₙ→0 (N₁-1 , hyp) = fast-ε-cauchy-convergence (λ @0 {ε} ε>0 ->
                                                        let N₁ = suc N₁-1; N₂ = suc (proj₁ (res ε ε>0)); N = suc (N₁ ℕ.⊔ N₂) in
                                                        ℕ.pred N :&: λ @0 {(suc m-1) (suc n-1) (ℕ.s≤s m-1>n-1) (ℕ.s≤s n-1≥N-1) →
                                                        let m = suc m-1; n = suc n-1; m>n = ℕ.s≤s m-1>n-1; n≥N = ℕ.s≤s n-1≥N-1
                                                              ; c≄0 = inj₂ 0<c; c⁻¹ = (c ⁻¹) c≄0
                                                              ; nonNegc⁻¹ = nonNegx⇒nonNegx⁻¹ {c} (0≤x⇒nonNegx (<⇒≤ 0<c)) c≄0
                                                        in begin
  ∣ sum xs n m ∣                                                     ≈⟨ 0≤x⇒∣x∣≃x (0≤xₙ⇒0≤sumxₙ (ℕP.<⇒≤ m>n) (λ k n≤k≤m -> <⇒≤ (proj₂ (0<aₙ,xₙ k)))) ⟩
  sum xs n m                                                         ≈⟨ ≃-sym (≃-trans (*-congʳ {sum xs n m} (*-inverseˡ c c≄0)) (*-identityˡ (sum xs n m))) ⟩
  c⁻¹ * c * sum xs n m                                               ≈⟨ ≃-trans
                                                                      (*-assoc c⁻¹ c (sum xs n m))
                                                                      (*-congˡ {c⁻¹} {c * sum xs n m} {sum (λ i → c * xs i) n m}
                                                                      (≃-sym (sumcxₙ≃csumxₙ xs c n m))) ⟩
  c⁻¹ * sum (λ i -> c * xs i) n m                                    ≤⟨ *-monoˡ-≤-nonNeg {sum (λ i → c * xs i) n m} {c⁻¹}
                                                                      {sum (λ i → as (ℕ.pred i) * xs (ℕ.pred i) - as i * xs i) n m}
                                                                      (sum-mono-≤-weak {λ i → c * xs i}
                                                                      {λ i → as (ℕ.pred i) * xs (ℕ.pred i) - as i * xs i} {n} {m} (ℕP.<⇒≤ m>n)
                                                                      λ @0 { (suc k-1) (n≤k , k≤m) → part3 (suc k-1)
                                                                      (ℕP.<-transʳ (ℕP.m≤m⊔n N₁ N₂) (ℕP.<-transˡ (ℕP.n<1+n (ℕ.pred N))
                                                                      (ℕP.≤-trans n≥N n≤k)))}) nonNegc⁻¹ ⟩
  c⁻¹ * sum (λ i -> as (ℕ.pred i) * xs (ℕ.pred i) - as i * xs i) n m ≈⟨ *-congˡ {c⁻¹}
                                                                      {sum (λ i → as (ℕ.pred i) * xs (ℕ.pred i) - as i * xs i) n m}
                                                                      {as n-1 * xs n-1 - as m-1 * xs m-1} (≃-trans
                                                                      (sum-to-sumᵀ (λ i -> as (ℕ.pred i) * xs (ℕ.pred i) - as i * xs i) n m (ℕP.<⇒≤ m>n))
                                                                      (part2 m n (ℕP.<⇒≤ m>n))) ⟩
  c⁻¹ * (as n-1 * xs n-1 - as m-1 * xs m-1)                        ≤⟨ *-monoˡ-≤-nonNeg {as n-1 * xs n-1 - as m-1 * xs m-1} {c⁻¹} {c * ε}
                                                                      (≤-trans x≤∣x∣ (≤-respˡ-≃ (∣x-y∣≃∣y-x∣ (as m-1 * xs m-1) (as n-1 * xs n-1))
                                                                      (proj₂ (res ε ε>0) m-1 n-1 m-1>n-1 (ℕP.≤-trans (ℕP.m≤n⊔m N₁ N₂) n-1≥N-1)))) nonNegc⁻¹ ⟩
  c⁻¹ * (c * ε)                                                    ≈⟨ ≃-trans (≃-trans
                                                                      (≃-sym (*-assoc c⁻¹ c ε))
                                                                      (*-congʳ {ε} {c⁻¹ * c} {oneℝ} (*-inverseˡ c c≄0)))
                                                                      (*-identityˡ ε) ⟩
  ε                                                                 ∎})
  where
    open ≤-Reasoning
    -- If we don't use abstract for res, it will take forever to compute ℕP.m≤m⊔n N₁ N₂.
    abstract
      res : ∀ ε -> ε > zeroℝ -> ∃ λ N₂-1 -> ∀ m n -> m ℕ.> n -> n ℕ.≥ suc N₂-1 -> ∣ as m * xs m - as n * xs n ∣ ≤ c * ε
      res ε ε>0 = fast-ε-from-convergence-cauchy {λ n → as n * xs n} (zeroℝ , aₙxₙ→0) (fast-0<x,y⇒0<x*y 0<c ε>0)

    part1 : ∀ n -> n ℕ.≥ suc N₁-1 -> as n * xs n - as (suc n) * xs (suc n) ≥ c * xs (suc n)
    part1 n n≥N₁ = let n+1 = suc n; xₙ₊₁≄0 = inj₂ (proj₂ (0<aₙ,xₙ n+1)) in begin
      c * xs n+1                                                          ≤⟨ *-monoʳ-≤-nonNeg {c} {xs n+1}
                                                                             {as n * xs n * (xs n+1 ⁻¹) xₙ₊₁≄0 - as n+1}
                                                                             (hyp n n≥N₁)
                                                                             (pos⇒nonNeg (fast-0<x⇒posx (proj₂ (0<aₙ,xₙ n+1)))) ⟩
      (as n * xs n * ((xs n+1) ⁻¹) xₙ₊₁≄0 - as n+1) * xs n+1              ≈⟨ *-distribʳ-+ (xs n+1) (as n * xs n * ((xs n+1) ⁻¹) xₙ₊₁≄0) (- (as n+1)) ⟩
      as n * xs n * ((xs n+1) ⁻¹) xₙ₊₁≄0 * xs n+1 + (- (as n+1)) * xs n+1 ≈⟨ +-cong
                                                                             (≃-trans (≃-trans
                                                                             (*-assoc (as n * xs n) (((xs n+1) ⁻¹) xₙ₊₁≄0) (xs n+1))
                                                                             (*-congˡ (*-inverseˡ (xs n+1) xₙ₊₁≄0)))
                                                                             (*-identityʳ (as n * xs n)))
                                                                             (≃-sym (neg-distribˡ-* (as n+1) (xs n+1))) ⟩
      as n * xs n - as n+1 * xs n+1                                        ∎

    part2 : ∀ m n -> {n ≢0} -> (m≥n : m ℕ.≥ n) ->
           sumᵀ (λ i -> as (ℕ.pred i) * xs (ℕ.pred i) - as i * xs i) n m m≥n ≃ as (ℕ.pred n) * xs (ℕ.pred n) - as (ℕ.pred m) * xs (ℕ.pred m)
    part2 m n {n≢0} m≥n with ≤⇒≡∨< n m m≥n
    ... | inj₁ refl = ≃-sym (+-inverseʳ (as (ℕ.pred m) * xs (ℕ.pred m)))
    part2 (suc m-1) n {n≢0} m≥n | inj₂ (ℕ.s≤s y) = begin-equality
      sumᵀ (λ i -> as (ℕ.pred i) * xs (ℕ.pred i) - as i * xs i) n m-1 y +
      (as (ℕ.pred m-1) * xs (ℕ.pred m-1) - as m-1 * xs m-1)               ≈⟨ +-congˡ (as (ℕ.pred m-1) * xs (ℕ.pred m-1) - as m-1 * xs m-1)
                                                                             (part2 m-1 n {n≢0} y) ⟩
      as (ℕ.pred n) * xs (ℕ.pred n) - as (ℕ.pred m-1) * xs (ℕ.pred m-1) +
      (as (ℕ.pred m-1) * xs (ℕ.pred m-1) - as m-1 * xs m-1)               ≈⟨ solve 3 (λ x y z -> x ⊖ y ⊕ (y ⊖ z) ⊜ x ⊖ z)
                                                                             ≃-refl (as (ℕ.pred n) * xs (ℕ.pred n)) (as (ℕ.pred m-1) * xs (ℕ.pred m-1))
                                                                             (as m-1 * xs m-1) ⟩
      as (ℕ.pred n) * xs (ℕ.pred n) - as m-1 * xs m-1                      ∎

    part3 : ∀ n -> {n ≢0} -> n ℕ.> suc N₁-1 -> c * xs n ≤ as (ℕ.pred n) * xs (ℕ.pred n) - as n * xs n
    part3 (suc n-1) (ℕ.s≤s n-1>N₁-1) = let n = suc n-1; xₙ≄0 = inj₂ (proj₂ (0<aₙ,xₙ n)) in begin
      c * xs n                                                ≤⟨ *-monoʳ-≤-nonNeg {c} {xs n}
                                                                 {as n-1 * xs n-1 * (xs n ⁻¹) xₙ≄0 - as n}
                                                                 (hyp n-1 n-1>N₁-1)
                                                                 (pos⇒nonNeg (0<x⇒posx (proj₂ (0<aₙ,xₙ n)))) ⟩
      (as n-1 * xs n-1 * (xs n ⁻¹) xₙ≄0 - as n) * xs n        ≈⟨ solve 4 (λ aₙ₋₁xₙ₋₁ xₙ⁻¹ aₙ xₙ ->
                                                                 (aₙ₋₁xₙ₋₁ ⊗ xₙ⁻¹ ⊖ aₙ) ⊗ xₙ ⊜ aₙ₋₁xₙ₋₁ ⊗ (xₙ⁻¹ ⊗ xₙ) ⊖ aₙ ⊗ xₙ)
                                                                 ≃-refl (as n-1 * xs n-1) ((xs n ⁻¹) xₙ≄0) (as n) (xs n) ⟩
      as n-1 * xs n-1 * ((xs n ⁻¹) xₙ≄0 * xs n) - as n * xs n ≈⟨ +-congˡ (- (as n * xs n)) {as n-1 * xs n-1 * ((xs n ⁻¹) xₙ≄0 * xs n)} {as n-1 * xs n-1}
                                                                 (≃-trans (*-congˡ {as n-1 * xs n-1} (*-inverseˡ (xs n) xₙ≄0)) (*-identityʳ (as n-1 * xs n-1))) ⟩
      as n-1 * xs n-1 - as n * xs n                            ∎

[xₙ]isDivergent∧c≄0⇒[cxₙ]isDivergent : ∀ {xs} -> ∀ {c} -> xs isDivergent -> c ≄0 -> (λ n -> c * xs n) isDivergent
[xₙ]isDivergent∧c≄0⇒[cxₙ]isDivergent {xs} {c} (ε , div* posε hyp) c≄0 = ∣ c ∣ * ε ,
                                     div* (posxAndyThenPosxTimesy (x≄0⇒pos∣x∣ c≄0) posε) (λ @0 {(suc k-1) ->
                                     let k = suc k-1; m = proj₁ (hyp k); n = proj₁ (proj₂ (hyp k)) in
                                     m , n , proj₁ (proj₂ (proj₂ (hyp k))) , proj₁ (proj₂ (proj₂ (proj₂ (hyp k)))) , (begin
  ∣ c ∣ * ε               ≤⟨ *-monoˡ-≤-nonNeg (proj₂ (proj₂ (proj₂ (proj₂ (hyp k))))) (nonNeg∣x∣ c) ⟩
  ∣ c ∣ * ∣ xs m - xs n ∣ ≈⟨ ≃-sym (∣x*y∣≃∣x∣*∣y∣ c (xs m - xs n)) ⟩
  ∣ c * (xs m - xs n) ∣   ≈⟨ ∣-∣-cong (solve 3 (λ c xₘ xₙ → c ⊗ (xₘ ⊖ xₙ) ⊜ c ⊗ xₘ ⊖ c ⊗ xₙ)
                             ≃-refl c (xs m) (xs n)) ⟩
  ∣ c * xs m - c * xs n ∣  ∎)})
  where open ≤-Reasoning

DivergesBy-cong : ∀ {xs ys} -> ∀ {ε} -> xs DivergesBy ε -> (∀ n -> xs n ≃ ys n) -> ys DivergesBy ε
DivergesBy-cong {xs} {ys} {ε} (div* posε hyp) xₙ≃yₙ = div* posε (λ @0 {(suc k-1) ->
                              let k = suc k-1; m = proj₁ (hyp k); n = proj₁ (proj₂ (hyp k)) in
                              m , n , proj₁ (proj₂ (proj₂ (hyp k))) , proj₁ (proj₂ (proj₂ (proj₂ (hyp k)))) , (begin
  ε               ≤⟨ proj₂ (proj₂ (proj₂ (proj₂ (hyp k)))) ⟩
  ∣ xs m - xs n ∣ ≈⟨ ∣-∣-cong (+-cong (xₙ≃yₙ m) (-‿cong (xₙ≃yₙ n))) ⟩
  ∣ ys m - ys n ∣  ∎)})
  where open ≤-Reasoning

isDivergent-cong : ∀ {xs ys} -> xs isDivergent -> (∀ n -> xs n ≃ ys n) -> ys isDivergent
isDivergent-cong {xs} {ys} (ε , hyp) xₙ≃yₙ = ε , DivergesBy-cong hyp xₙ≃yₙ

sumxₙisDivergent∧c≄0⇒sumcxₙisDivergent : ∀ {xs} -> ∀ {c} -> seriesOf xs isDivergent -> c ≄0 -> seriesOf (λ n -> c * xs n) isDivergent
sumxₙisDivergent∧c≄0⇒sumcxₙisDivergent {xs} {c} hyp c≄0 = isDivergent-cong ([xₙ]isDivergent∧c≄0⇒[cxₙ]isDivergent hyp c≄0)
                                                      λ n -> ≃-sym (sumcxₙ≃csumxₙ xs c 0 n)

x≤y⇒x-y≤0 : ∀ {x y} -> x ≤ y -> x - y ≤ zeroℝ
x≤y⇒x-y≤0 {x} {y} x≤y = begin
  x - y ≤⟨ +-monoˡ-≤ (- y) x≤y ⟩
  y - y ≈⟨ +-inverseʳ y ⟩
  zeroℝ     ∎
  where open ≤-Reasoning

x-y≤0⇒x≤y : ∀ {x y} -> x - y ≤ zeroℝ -> x ≤ y
x-y≤0⇒x≤y {x} {y} x-y≤0 = begin
  x         ≈⟨ solve 2 (λ x y -> x ⊜ x ⊖ y ⊕ y) ≃-refl x y ⟩
  x - y + y ≤⟨ +-monoˡ-≤ y x-y≤0 ⟩
  zeroℝ + y    ≈⟨ +-identityˡ y ⟩
  y          ∎
  where open ≤-Reasoning

{-
x * x⁻¹ = 1
solve 1 
λ x x≄0 -> ????
-}
lemma-3-7-2 : ∀ {as xs : ℕ -> ℝ} -> (0<aₙ,xₙ : ∀ n -> (zeroℝ < as n) × (zeroℝ < xs n)) ->
              seriesOf (λ n -> (as n ⁻¹) (inj₂ (proj₁ (0<aₙ,xₙ n)))) isDivergent ->
              (∃ λ N-1 -> ∀ n -> n ℕ.≥ suc N-1 -> as n * xs n * (xs (suc n) ⁻¹) (inj₂ (proj₂ (0<aₙ,xₙ (suc n)))) - as (suc n) ≤ zeroℝ) ->
              seriesOf xs isDivergent
lemma-3-7-2 {as} {xs} 0<aₙ,xₙ divsumaₙ⁻¹ (N-1 , hyp) = comparison-test-divergence {xs}
                                                     {λ n → as N * xs N * (as n ⁻¹) (inj₂ (proj₁ (0<aₙ,xₙ n)))}
                                                     (0 , (λ n n≥0 -> part1 n))
                                                     (sumxₙisDivergent∧c≄0⇒sumcxₙisDivergent
                                                     {λ n → (as n ⁻¹) (inj₂ (proj₁ (0<aₙ,xₙ n)))} divsumaₙ⁻¹
                                                     (inj₂ (0<x,y⇒0<x*y (proj₁ (0<aₙ,xₙ N)) (proj₂ (0<aₙ,xₙ N)))))
                                                     (N , part4)
  where
    open ≤-Reasoning
    N = suc N-1
    abstract
      part1 : ∀ n -> NonNegative (as N * xs N * (as n ⁻¹) (inj₂ (proj₁ (0<aₙ,xₙ n))))
      part1 n = let aₙ⁻¹ = (as n ⁻¹) (inj₂ (proj₁ (0<aₙ,xₙ n))) in
                pos⇒nonNeg {as N * xs N * aₙ⁻¹} (posxAndyThenPosxTimesy {as N * xs N} {aₙ⁻¹}
                (posxAndyThenPosxTimesy (0<x⇒posx (proj₁ (0<aₙ,xₙ N))) (0<x⇒posx (proj₂ (0<aₙ,xₙ N))))
                (posxThenPosxInv (as n) (inj₂ (proj₁ (0<aₙ,xₙ n))) (0<x⇒posx (proj₁ (0<aₙ,xₙ n)))))

      part2 : ∀ n -> n ℕ.≥ N -> as n * xs n ≤ as (suc n) * xs (suc n)
      part2 n n≥N = let aₙ = as n; xₙ = xs n; aₙ₊₁ = as (suc n); xₙ₊₁ = xs (suc n)
                         ; xₙ₊₁>0 = proj₂ (0<aₙ,xₙ (suc n)); xₙ₊₁⁻¹ = (xₙ₊₁ ⁻¹) (inj₂ xₙ₊₁>0) in begin
        aₙ * xₙ                   ≈⟨ ≃-sym (≃-trans
                                     (*-congˡ {aₙ * xₙ} {xₙ₊₁ * xₙ₊₁⁻¹} {oneℝ} (*-inverseʳ xₙ₊₁ (inj₂ xₙ₊₁>0)))
                                     (*-identityʳ (aₙ * xₙ))) ⟩
        aₙ * xₙ * (xₙ₊₁ * xₙ₊₁⁻¹) ≤⟨ ≤-respˡ-≃
                                     (solve 4 (λ aₙ xₙ xₙ₊₁ xₙ₊₁⁻¹ ->
                                      aₙ ⊗ xₙ ⊗ xₙ₊₁⁻¹ ⊗ xₙ₊₁ ⊜ aₙ ⊗ xₙ ⊗ (xₙ₊₁ ⊗ xₙ₊₁⁻¹))
                                      ≃-refl aₙ xₙ xₙ₊₁ xₙ₊₁⁻¹)
                                      (*-monoʳ-≤-nonNeg {aₙ * xₙ * xₙ₊₁⁻¹} {xₙ₊₁} {aₙ₊₁}
                                      (x-y≤0⇒x≤y {aₙ * xₙ * xₙ₊₁⁻¹} {aₙ₊₁} (hyp n n≥N))
                                      (pos⇒nonNeg (0<x⇒posx xₙ₊₁>0))) ⟩
        aₙ₊₁ * xₙ₊₁                ∎

      part3 : ∀ n -> N ≡ n ⊎ N ℕ.< n -> as N * xs N ≤ as n * xs n
      part3 n (inj₁ refl)              = ≤-refl
      part3 (suc n) (inj₂ (ℕ.s≤s N≤n)) = ≤-trans (part3 n (≤⇒≡∨< N n N≤n)) (part2 n N≤n)

      part4 : ∀ n -> n ℕ.≥ N -> as N * xs N * (as n ⁻¹) (inj₂ (proj₁ (0<aₙ,xₙ n))) ≤ xs n
      part4 n n≥N = let aₙ>0 = proj₁ (0<aₙ,xₙ n); aₙ≄0 = inj₂ aₙ>0; aₙ⁻¹ = (as n ⁻¹) aₙ≄0 in begin
        as N * xs N * aₙ⁻¹ ≤⟨ *-monoʳ-≤-nonNeg {as N * xs N} {aₙ⁻¹} {as n * xs n}
                              (part3 n (≤⇒≡∨< N n n≥N)) (nonNegx⇒nonNegx⁻¹ {as n}
                              (pos⇒nonNeg (0<x⇒posx aₙ>0)) aₙ≄0) ⟩
        as n * xs n * aₙ⁻¹ ≈⟨ solve 3 (λ aₙ xₙ aₙ⁻¹ -> aₙ ⊗ xₙ ⊗ aₙ⁻¹ ⊜ aₙ ⊗ aₙ⁻¹ ⊗ xₙ)
                              ≃-refl (as n) (xs n) aₙ⁻¹ ⟩
        as n * aₙ⁻¹ * xs n ≈⟨ *-congʳ {xs n} {as n * aₙ⁻¹} {oneℝ}
                              (*-inverseʳ (as n) aₙ≄0) ⟩
        oneℝ * xs n          ≈⟨ *-identityˡ (xs n) ⟩
        xs n                ∎
        
-- Π₀ needed for proof of Lemma 3.8. Should extend to Π in a clean manner like how sum was extended.
-- Πᵢ₌₀ⁿxᵢ
--
Π₀ : (ℕ -> ℝ) -> ℕ -> ℝ
Π₀ a 0 = oneℝ
Π₀ a (suc n) = Π₀ a n * a n

{-Π : (ℕ -> ℝ) -> (i n : ℕ) -> (i≤n : i ℕ.≤ n) -> ℝ
Π a i n i≤n with ≤⇒≡∨< i n i≤n
... | inj₁ i≡n = oneℝ
... | inj₂ i<n = {!!}
-}

0≤x,y⇒0≤x+y : ∀ {x y} -> zeroℝ ≤ x -> zeroℝ ≤ y -> zeroℝ ≤ x + y
0≤x,y⇒0≤x+y {x} {y} 0≤x 0≤y = nonNegx⇒0≤x (nonNegx,y⇒nonNegx+y (0≤x⇒nonNegx 0≤x) (0≤x⇒nonNegx 0≤y))

{-
{-
Let (xₙ) be a sequence of positive numbers and let c > 0. If there is N∈ℕ such that
                                 n(xₙxₙ₊₁⁻¹ - 1) ≥ c                   (n ≥ N)
then (xₙ) converges to 0.
-}
lemma-3-8 : ∀ {xs} -> ∀ {c} -> (xₙ>0 : ∀ n -> xs n > zeroℝ) -> c > zeroℝ ->
            (∃ λ N-1 -> ∀ n -> n ℕ.≥ suc N-1 -> (+ n / 1) ⋆ * (xs n * (xs (suc n) ⁻¹) (inj₂ (xₙ>0 (suc n))) - oneℝ) ≥ c) ->
            ConvergesTo xs zeroℝ
lemma-3-8 {xs} {c} xₙ>0 c>0 (N-1 , hyp) = {!!}
  where
    open ≤-Reasoning
    N = suc N-1
    part1 : ∀ n -> Π₀ (λ i -> oneℝ + c * (+ (N ℕ.+ i) / 1) ⋆) n ≥ oneℝ + c * sum0 (λ i -> (+ 1 / (N ℕ.+ i)) ⋆) n
    part1 zero    = ≤-reflexive (solve 1 (λ c -> Κ 1ℚᵘ ⊕ c ⊗ Κ 0ℚᵘ ⊜ Κ 1ℚᵘ) ≃-refl c)
    part1 (suc n) = let S = oneℝ + c * (sum0 [N+i]⁻¹ n + (+ (N ℕ.+ n) / 1) ⋆) in begin
      oneℝ + c * (sum0 [N+i]⁻¹ n + (+ 1 / (N ℕ.+ n)) ⋆)               ≤⟨ +-monoʳ-≤ oneℝ (*-monoˡ-≤-nonNeg
                                                                     (+-monoʳ-≤ (sum0 [N+i]⁻¹ n) part1-1)
                                                                     (pos⇒nonNeg (0<x⇒posx c>0))) ⟩
      oneℝ + c * (sum0 [N+i]⁻¹ n + (+ (N ℕ.+ n) / 1) ⋆)               ≤⟨ ≤-respˡ-≃ (+-identityʳ S)
                                                                     (+-monoʳ-≤ S part1-2) ⟩
      oneℝ + c * (sum0 [N+i]⁻¹ n + (+ (N ℕ.+ n) / 1) ⋆) +
      c * c * (+ (N ℕ.+ n) / 1) ⋆ * sum0 [N+i]⁻¹ n                  ≈⟨ solve 3 (λ c sum0[N+i]⁻¹ N+n →
                                                                     Κ 1ℚᵘ ⊕ c ⊗ (sum0[N+i]⁻¹ ⊕ N+n) ⊕ c ⊗ c ⊗ N+n ⊗ sum0[N+i]⁻¹ ⊜
                                                                     Κ 1ℚᵘ ⊗ Κ 1ℚᵘ ⊕ Κ 1ℚᵘ ⊗ (c ⊗ N+n) ⊕ (c ⊗ sum0[N+i]⁻¹) ⊗ Κ 1ℚᵘ
                                                                     ⊕ (c ⊗ sum0[N+i]⁻¹) ⊗ (c ⊗ N+n))
                                                                     ≃-refl c (sum0 [N+i]⁻¹ n) ((+ (N ℕ.+ n) / 1) ⋆) ⟩
      oneℝ * oneℝ + oneℝ * (c * (+ (N ℕ.+ n) / 1) ⋆) +
      c * sum0 [N+i]⁻¹ n * oneℝ +
      c * sum0 [N+i]⁻¹ n * (c * (+ (N ℕ.+ n) / 1) ⋆)                ≈⟨ solve 4 (λ a b c d →
                                                                     a ⊗ c ⊕ a ⊗ d ⊕ b ⊗ c ⊕ b ⊗ d ⊜
                                                                     (a ⊕ b) ⊗ (c ⊕ d))
                                                                     ≃-refl oneℝ (c * sum0 [N+i]⁻¹ n) oneℝ (c * (+ (N ℕ.+ n) / 1) ⋆) ⟩
      (oneℝ + c * sum0 [N+i]⁻¹ n) * (oneℝ + c * (+ (N ℕ.+ n) / 1) ⋆)    ≤⟨ *-monoʳ-≤-nonNeg {oneℝ + c * sum0 [N+i]⁻¹ n}
                                                                     {oneℝ + c * (+ (N ℕ.+ n) / 1) ⋆}
                                                                     {Π₀ (λ i → oneℝ + c * (+ (N ℕ.+ i) / 1) ⋆) n}
                                                                     (part1 n) part1-3 ⟩
      Π₀ (λ i -> oneℝ +
      c * (+ (N ℕ.+ i) / 1) ⋆) n * (oneℝ + c * (+ (N ℕ.+ n) / 1) ⋆)  ∎
      where
        [N+i]⁻¹ = λ i -> (+ 1 / (N ℕ.+ i)) ⋆
        part1-1 : (+ 1 / (N ℕ.+ n)) ⋆ ≤ (+ (N ℕ.+ n) / 1) ⋆
        part1-1 = p≤q⇒p⋆≤q⋆ (+ 1 / (N ℕ.+ n)) (+ (N ℕ.+ n) / 1) (ℚ.*≤* (ℤ.+≤+ (ℕ.s≤s ℕ.z≤n)))

        part1-2 : zeroℝ ≤ c * c * (+ (N ℕ.+ n) / 1) ⋆ * sum0 [N+i]⁻¹ n
        part1-2 = 0≤x,y⇒0≤x*y {c * c * (+ (N ℕ.+ n) / 1) ⋆} {sum0 [N+i]⁻¹ n} (0≤x,y⇒0≤x*y {c * c} {(+ (N ℕ.+ n) / 1) ⋆}
              (<⇒≤ (0<x,y⇒0<x*y c>0 c>0))
              (p≤q⇒p⋆≤q⋆ 0ℚᵘ (+ (N ℕ.+ n) / 1) (ℚP.nonNegative⁻¹ _)))
              (≤-respˡ-≃ (sum0≃0 0 n) (sum-mono-≤ (λ n -> p≤q⇒p⋆≤q⋆ 0ℚᵘ (+ 1 / (N ℕ.+ n)) (ℚP.nonNegative⁻¹ _)) 0 n ℕ.z≤n))

        part1-3 : NonNegative (oneℝ + c * (+ (N ℕ.+ n) / 1) ⋆)
        part1-3 = 0≤x⇒nonNegx (0≤x,y⇒0≤x+y (p≤q⇒p⋆≤q⋆ 0ℚᵘ 1ℚᵘ (ℚP.nonNegative⁻¹ _))
                  (0≤x,y⇒0≤x*y (<⇒≤ c>0) (p≤q⇒p⋆≤q⋆ 0ℚᵘ (+ (N ℕ.+ n) / 1) (ℚP.nonNegative⁻¹ _))))

proposition-3-9-1 : ∀ {xs} -> (xₙ>0 : ∀ n -> xs n > zeroℝ) ->
                              (hyp : (λ n -> (+ n / 1) ⋆ * (xs n * (xs (suc n) ⁻¹) (inj₂ (xₙ>0 (suc n))) - oneℝ) IsConvergent) ->
                              proj₁ hyp > oneℝ ->
                              IsConvergent (seriesOf xs)
proposition-3-9-1 {xs} xₙ>0 (L :^: MkCon hyp) L>1 = {!!}
-}

{-
Lemma:
  Let (xₙ) be a sequence, c∈ℝ positive, and N∈ℤ⁺. If
                n(xₙxₙ₊₁ - 1) ≥ c                (n ≥ N),
then (xₙ)→0.
-}
{-lemma-3-8 : {xs : ℕ → ℝ} {c : ℝ} {N : ℕ} {N≢0 : N ≢0} → c > zeroℝ →
            ({n : ℕ} → n ℕ.≥ N → (+ n / 1) ⋆ * (xs n * xs (suc n) - oneℝ) ≥ c) → ConvergesTo xs zeroℝ
lemma-3-8 {xs} {c} {N} c>0 hyp = {!!} -}
-}


fact : ℕ → ℕ
fact zero    = 1
fact (suc n) = suc n ℕ.* fact n
-- Let's do this the easy way.
{-# FOREIGN AGDA2HS
fact :: Natural -> Natural
fact 0    = 1
fact n    = n * fact (n - 1)
#-}

-- Alias.
@0 _! : ℕ → ℕ
_! = fact

-- Strange, but @0'd expressions can't be used in dotted expressions (even though that's a stronger concept).
-- See Agda issue #6765.
-- But for now:
postulate .dotErased : ∀ {i} {A : Set i} -> @0 A -> A

@0 m,n≢0⇒mn≢0 : (m n : ℕ) {m≢0 : m ≢0} {n≢0 : n ≢0} → m ℕ.* n ≢0
m,n≢0⇒mn≢0 (suc m) (suc n) = _

@0 _!≢0 : (n : ℕ) → fact n ≢0
zero  !≢0 = _
suc n !≢0 = m,n≢0⇒mn≢0 (suc n) (fact n) {_} {n !≢0}

-- This result can be very tedious to prove without the automation provided by
-- pattern matching on q and t. See the definition of e for an example where
-- this was needed.
@0 p/q*r/t≡pr/qt : (p r : ℤ) (q t : ℕ) {q≢0 : q ≢0} {t≢0 : t ≢0} →
                (p / q) {q≢0} ℚ.* (r / t) {t≢0} ≡ ((p ℤ.* r) / (q ℕ.* t))
                {m,n≢0⇒mn≢0 q t {q≢0} {t≢0}}
p/q*r/t≡pr/qt p r (suc q-1) (suc t-1) = refl

{-
Define
  e = sumₙ₌₀(n!)⁻¹
The series converges by the ratio test.
-}

e : ℝ
e = proj₁' (proposition361 (λ n → toReal ((+ 1 / fact n) {dotErased (n !≢0)})) (toReal (+ 1 / 2))
          (pLtqThenToRealpLtToRealq (+ 0 / 1) (+ 1 / 2) (ℚP.positive⁻¹ _) Tuple.,
          pLtqThenToRealpLtToRealq (+ 1 / 2) (+ 1 / 1) (ℚ.*<* (ℤ.+<+ (ℕ.s≤s ℕP.≤-refl))))
          (0 :&: with-⋆))
  where
    factinv : ℕ → ℚᵘ
    factinv n = (+ 1 / fact n) {dotErased (n !≢0)}
    @0 _!⁻¹ : ℕ → ℚᵘ
    _!⁻¹ = factinv

    -- First we prove it without the absolute values and ⋆ conversions
    @0 without-⋆ : (n : ℕ) {n≢0 : n ≢0} → (suc n) !⁻¹ ℚ.≤ + 1 / 2 ℚ.* (n !⁻¹)
    without-⋆ (suc n-1) = let n = suc n-1; 2n!≢0 = m,n≢0⇒mn≢0 2 (fact n) {_} {n !≢0} in begin
      (suc n) !⁻¹                 ≤⟨ q≤r⇒+p/r≤+p/q 1 (2 ℕ.* n !) (fact (suc n)) {2n!≢0} {suc n !≢0}
                                     (ℕP.*-monoˡ-≤ (n !) {2} {suc n} (ℕ.s≤s (ℕ.s≤s ℕ.z≤n))) ⟩
      (+ 1 / (2 ℕ.* n !)) {2n!≢0} ≡⟨ sym (p/q*r/t≡pr/qt (+ 1) (+ 1) 2 (n !) {_} {n !≢0}) ⟩
      + 1 / 2 ℚ.* (n !⁻¹)          ∎
      where open ℚP.≤-Reasoning

    -- A lot of conversions between numerators and denominators required.
    -- Unfortunately Agda cannot immediately tell that the numerator of 1/n! is 1,
    -- hence these conversions.
    @0 with-⋆ : (n : ℕ) → n ℕ.≥ 1 → ∣ (suc n !⁻¹) ⋆ ∣ ≤ (+ 1 / 2) ⋆ * ∣ n !⁻¹ ⋆ ∣
    with-⋆ (suc n-1) n≥1 = let n = suc n-1 in begin
      (∣ (suc n !⁻¹) ⋆ ∣        ≈⟨ nonNegx⇒∣x∣≃x (nonNegp⇒nonNegp⋆ (suc n !⁻¹)
                                  (subst ℤ.NonNegative (sym (ℚP.↥[p/q]≡p (+ 1) (suc n !) {suc n !≢0})) _)) ⟩
      (suc n !⁻¹) ⋆            ≤⟨ p≤q⇒p⋆≤q⋆ (suc n !⁻¹) (+ 1 / 2 ℚ.* n !⁻¹) (without-⋆ n) ⟩
      (+ 1 / 2 ℚ.* (n !⁻¹)) ⋆  ≈⟨ ⋆-distrib-* (+ 1 / 2) (n !⁻¹) ⟩
      (+ 1 / 2) ⋆ * (n !⁻¹) ⋆  ≤⟨ *-monoˡ-≤-nonNeg x≤∣x∣ (nonNegp⇒nonNegp⋆ (+ 1 / 2) _) ⟩
      (+ 1 / 2) ⋆ * ∣ n !⁻¹ ⋆ ∣  ∎)
      where open ≤-Reasoning hiding (subst)
{-# COMPILE AGDA2HS e #-}
{-
{-
x≤0⇒∣x∣≃-x : {x : ℝ} → x ≤ zeroℝ → ∣ x ∣ ≃ - x
x≤0⇒∣x∣≃-x {x} x≤0 = begin-equality
  (∣ x ∣  ≈⟨ ≃-sym ∣-x∣≃∣x∣ ⟩
  ∣ - x ∣ ≈⟨ 0≤x⇒∣x∣≃x (≤-respˡ-≃ (≃-sym 0≃-0) (neg-mono-≤ x≤0)) ⟩
   - x    ∎)
  where open ≤-Reasoning

x≤y≤0⇒∣y∣≤∣x∣ : {x y : ℝ} → x ≤ y ≤ zeroℝ → ∣ y ∣ ≤ ∣ x ∣
x≤y≤0⇒∣y∣≤∣x∣ {x} {y} x≤y≤0 = begin
  ∣ y ∣  ≈⟨ x≤0⇒∣x∣≃-x (proj₂ x≤y≤0) ⟩
  - y   ≤⟨ neg-mono-≤ (proj₁ x≤y≤0) ⟩
  - x   ≈⟨ ≃-sym (x≤0⇒∣x∣≃-x (≤-trans (proj₁ x≤y≤0) (proj₂ x≤y≤0))) ⟩
  ∣ x ∣   ∎
  where open ≤-Reasoning

abstract
  fast-x≤y≤0⇒∣y∣≤∣x∣ : {x y : ℝ} → x ≤ y ≤ zeroℝ → ∣ y ∣ ≤ ∣ x ∣
  fast-x≤y≤0⇒∣y∣≤∣x∣ = x≤y≤0⇒∣y∣≤∣x∣

x<0⇒0<∣x∣ : {x : ℝ} → x < zeroℝ → zeroℝ < ∣ x ∣
x<0⇒0<∣x∣ {x} x<0 = begin-strict
  zeroℝ   ≈⟨ 0≃-0 ⟩
  - zeroℝ <⟨ neg-mono-< x<0 ⟩
  - x  ≈⟨ ≃-sym (x≤0⇒∣x∣≃-x (<⇒≤ x<0)) ⟩
  ∣ x ∣  ∎
  where open ≤-Reasoning

{-
Possible new naming convention:
How about isDecreasing and isDecreasing₂?
Then we can have a proof of isDecreasing⇒isDecreasing₂ and the converse.
This could be a better naming convention in the long run (instead of having
just some proof called altDecreasing that takes in isDecreasing and returns
isDecreasing₂).

Usability:
It would be nice if Agda could search through its library and check for functions
like isDecreasingₙ indexed by n.

We can do this using Emacs search of course but it's a bit cumbersome.

Pretty sure Lean has a feature like this.
-}
_isDecreasing : (xs : ℕ → ℝ) → Set
xs isDecreasing = (n : ℕ) → xs n ≥ xs (suc n)

_isDecreasing₂ : (xs : ℕ → ℝ) → Set
xs isDecreasing₂ = (m n : ℕ) → m ℕ.≥ n → xs m ≤ xs n

isDecreasing⇒isDecreasing₂ : {xs : ℕ → ℝ} → xs isDecreasing → xs isDecreasing₂
isDecreasing⇒isDecreasing₂ {xs} dec m n m≥n with ≤⇒≡∨< n m m≥n
... | inj₁ refl = ≤-refl
isDecreasing⇒isDecreasing₂ {xs} dec (suc m) n m≥n | inj₂ (ℕ.s≤s n≤m) = begin
  xs (suc m) ≤⟨ dec m ⟩
  xs m       ≤⟨ isDecreasing⇒isDecreasing₂ dec m n n≤m ⟩
  xs n        ∎
  where open ≤-Reasoning

abstract
  fast-isDecreasing⇒isDecreasing₂ : {xs : ℕ → ℝ} → xs isDecreasing → xs isDecreasing₂
  fast-isDecreasing⇒isDecreasing₂ = isDecreasing⇒isDecreasing₂

isDecreasing₂⇒isDecreasing : {xs : ℕ → ℝ} → xs isDecreasing₂ → xs isDecreasing
isDecreasing₂⇒isDecreasing {xs} dec₂ n = dec₂ (suc n) n (ℕP.n≤1+n n)

_isIncreasing : (xs : ℕ → ℝ) → Set
xs isIncreasing = (n : ℕ) → xs n ≤ xs (suc n)

_isIncreasing₂ : (xs : ℕ → ℝ) → Set
xs isIncreasing₂ = (m n : ℕ) → m ℕ.≥ n → xs m ≥ xs n

-- xs n ≤ xs m
-- - xs m ≤ - xs n
isIncreasing⇒isIncreasing₂ : {xs : ℕ → ℝ} → xs isIncreasing → xs isIncreasing₂
isIncreasing⇒isIncreasing₂ {xs} inc m n m≥n = ≤-respˡ-≃ (neg-involutive (xs n)) (≤-respʳ-≃ (neg-involutive (xs m)) (neg-mono-≤
                                              (isDecreasing⇒isDecreasing₂ (λ k → neg-mono-≤ (inc k)) m n m≥n)))

{-
Alternating Series Test:
  Let (xₙ) be a decreasing sequence that converges to 0. Then the series sum(-1)ᵏxₖ is convergent.
Proof:
  Since (xₙ)→0 and is decreasing, it follows that xₙ ≥ 0 for all n∈ℕ. We will show that 
the given sequence is a Cauchy sequence. Let n < m.
  ∣sumᵢ₌ₙᵐ(-1)ⁱxᵢ∣ ≤ xₙ?

Doesn't matter if n is even or odd 
Suppose n even. Then
∣(-1)ⁿxₙ + sumᵢ₌ₙ₊₁ᵐ(-1)ⁱxᵢ∣ = xₙ - xₙ₊₁ + sumᵢ₌ₙ₊₂ᵐ(-1)ⁱxᵢ
                          ≤ xₙ - xₙ₊₁ + xₙ₊₁ = xₙ.
Suppose n odd. Then

= ∣(-1)ⁿxₙ + ⋯ + (-1)ⁿ⁺ᵐ⁻ⁿxₙ₊ₘ₋ₙ∣
-}
{-
alternating-series-test : {xs : ℕ → ℝ} → xs isDecreasing → ConvergesTo xs zeroℝ →
                          seriesOf (λ n → pow (- oneℝ) n * xs n IsConvergent
alternating-series-test {xs} dec xₙ→0 = fastCauchyToConvergent {!!}
  where
    open ≤-Reasoning
    
    [-1]ᵏxₖ : ℕ → ℝ
    [-1]ᵏxₖ k = pow (- oneℝ) k * xs k

    dec₂ : xs isDecreasing₂
    dec₂ = fast-isDecreasing⇒isDecreasing₂ dec
  {-
  Let n∈ℕ and suppose, towards contradiction, that xₙ < 0. Then ∣xₙ∣ > 0.
  Since (xₙ)→0, there is N ≥ n such that ∣xₘ∣ < ∣xₙ∣ for m ≥ N ≥ n.
  As (xₙ) is decreasing and m ≥ n, we have xₘ ≤ xₙ < 0. Thus ∣xₙ∣ ≤ ∣xₘ∣,
  contradicting ∣xₘ∣ < ∣xₙ∣. Hence 0 ≤ xₙ.
  -}
    xₙ≥0 : (n : ℕ) → xs n ≥ zeroℝ
    xₙ≥0 n = ≮⇒≥ (λ xₙ<0 → let get = fast-ε-from-convergence (zeroℝ , xₙ→0) ∣ xs n ∣ (0<x⇒posx (x<0⇒0<∣x∣ xₙ<0))
                                     ; N = suc (proj₁ get); M = N ℕ.⊔ n in
                           <-irrefl ≃-refl (begin-strict
      ∣ xs n ∣      ≤⟨ x≤y≤0⇒∣y∣≤∣x∣ {xs M} {xs n} (dec₂ M n (ℕP.m≤n⊔m N n) , <⇒≤ xₙ<0) ⟩
      ∣ xs M ∣      ≈⟨ ∣-∣-cong (solve 1 (λ x → x ⊜ x ⊖ Κ 0ℚᵘ) ≃-refl (xs M)) ⟩
      ∣ xs M - zeroℝ ∣ <⟨ proj₂ get M (ℕP.m≤m⊔n N n) ⟩
      ∣ xs n ∣       ∎))

  {-
    ∣sumᵢ₌₃⁵(-1)ⁱxᵢ∣ = ∣-x₃ + x₄ - x₅∣
                  = x₃ - x₄ + x₅
                  ≤ x₃

    Split on n even or odd cases?
    n even:
    ∣sumᵢ₌ₙᵐ(-1)ⁱxᵢ∣ = sumᵢ₌ₙᵐ(-1)ⁱxᵢ ≤ xₙ
    n odd:
    ∣sumᵢ₌ₙᵐ(-1)ⁱxᵢ∣ = ∣-xₙ + sumᵢ₌ₙ₊₁ᵐ(-1)ⁱxᵢ∣
                  = xₙ - sumᵢ₌ₙ₊₁ᵐ(-1)ⁱxᵢ
                  ≤ xₙ
  -}
    partial≥0 : (m n : ℕ) → m ℕ.> n → sum [-1]ᵏxₖ n m ≥ zeroℝ
    partial≥0 m n m>n = {!!}

  {-
  -}
    lem : (m n : ℕ) → n ℕ.≤ m → [-1]ᵏxₖ n ≤ xs m
    lem m n n≤m with ≤⇒≡∨< n m n≤m
    ... | inj₁ refl = {!!}
    ... | inj₂ n<m  = {!!}



    {-lem : (m n : ℕ) → m ℕ.≥ n → sum [-1]ᵏxₖ n m ≤ xs n
    lem m n m≥n with ≤⇒≡∨< n m m≥n
    lem zero .0 m≥n | inj₁ refl          = xₙ≥0 0
    lem (suc m) .(suc m) m≥n | inj₁ refl = begin
      sum0 [-1]ᵏxₖ (suc m) - sum0 [-1]ᵏxₖ (suc m) ≈⟨ +-inverseʳ (sum0 [-1]ᵏxₖ (suc m)) ⟩
      zeroℝ                                      ≤⟨ xₙ≥0 (suc m) ⟩
      xs (suc m)                               ∎
    lem (suc m) n m≥n | inj₂ m>n = {!!}

    {-
    0 + 1x₀ ≥ 0 + 1x₀ + 1 * -1x₁ + 1 * -1x₂ 
    -}
    lem2 : (m n : ℕ) → (m>n : m ℕ.> n) →
           sumᵀ [-1]ᵏxₖ n m (ℕP.<⇒≤ m>n) ≥ sumᵀ [-1]ᵏxₖ n (2 ℕ.+ m) (ℕP.≤-trans (ℕP.<⇒≤ m>n) (ℕP.m≤n+m m 2))
    lem2 (suc zero) zero m≥n = {!sumᵀ [-1]ᵏxₖ 0 3 (ℕP.≤-trans (ℕP.<⇒≤ m≥n) (ℕP.m≤n+m 1 2))!}
    lem2 (suc zero) (suc n) (ℕ.s≤s ())
    lem2 (suc (suc m)) n m≥n = {!!}

    lem3 : (m n : ℕ) → (m≥n : m ℕ.≥ n) →
           sum [-1]ᵏxₖ n m ≤ xs m
    lem3 m n m≥n with ≤⇒≡∨< n m m≥n
    ... | inj₁ refl = {!!}
    lem3 (suc m) n m≥n | inj₂ m>n = {!!}-}

abstract
  fast-alternating-series-test : {xs : ℕ → ℝ} → xs isDecreasing → ConvergesTo xs zeroℝ →
                                 seriesOf (λ n → pow (- oneℝ) n * xs n IsConvergent
  fast-alternating-series-test = alternating-series-test

π : ℝ
π = (+ 4 / 1) ⋆ * proj₁ (fast-alternating-series-test {λ n → (+ 1 / (1 ℕ.+ 2 ℕ.* n)) ⋆}
                        dec [1+2k]⁻¹→0)
  where
    open ≤-Reasoning
    [1+2k]⁻¹ : ℕ → ℝ
    [1+2k]⁻¹ n = (+ 1 / (1 ℕ.+ 2 ℕ.* n)) ⋆
    
    dec : [1+2k]⁻¹ isDecreasing
    dec n = p≤q⇒p⋆≤q⋆ (+ 1 / (1 ℕ.+ 2 ℕ.* (suc n))) (+ 1 / (1 ℕ.+ 2 ℕ.* n))
            (q≤r⇒+p/r≤+p/q 1 (1 ℕ.+ 2 ℕ.* n) (1 ℕ.+ 2 ℕ.* (suc n))
            (ℕP.+-monoʳ-≤ 1 (ℕP.*-monoʳ-≤ 2 (ℕP.n≤1+n n))))

    [1+2k]⁻¹→0 : [1+2k]⁻¹ ConvergesTo zeroℝ
    [1+2k]⁻¹→0 = MkCon (λ @0 {(suc k-1) → let k = suc k-1 in
                 k-1 , λ n n≥k → begin
      ∣ [1+2k]⁻¹ n - zeroℝ ∣ ≈⟨ ∣-∣-cong (solve 1 (λ x → x ⊖ Κ 0ℚᵘ ⊜ x) ≃-refl ([1+2k]⁻¹ n)) ⟩
      ∣ [1+2k]⁻¹ n ∣      ≈⟨ nonNegx⇒∣x∣≃x (nonNegp⇒nonNegp⋆ (+ 1 / (1 ℕ.+ 2 ℕ.* n)) _) ⟩
      [1+2k]⁻¹ n         ≤⟨ p≤q⇒p⋆≤q⋆ (+ 1 / (1 ℕ.+ 2 ℕ.* n)) (+ 1 / (1 ℕ.+ 2 ℕ.* k))
                            (q≤r⇒+p/r≤+p/q 1 (1 ℕ.+ 2 ℕ.* k) (1 ℕ.+ 2 ℕ.* n)
                            (ℕ.s≤s (ℕP.*-monoʳ-≤ 2 n≥k))) ⟩
      [1+2k]⁻¹ k         ≤⟨ p≤q⇒p⋆≤q⋆ (+ 1 / (1 ℕ.+ 2 ℕ.* k)) (+ 1 / k)
                            (q≤r⇒+p/r≤+p/q 1 k (1 ℕ.+ 2 ℕ.* k)
                            (ℕP.≤-trans 
                            (ℕP.m≤n*m k {2} (ℕ.s≤s ℕ.z≤n)) (ℕP.n≤1+n (2 ℕ.* k)))) ⟩
      (+ 1 / k) ⋆         ∎})
-}

{-
Suppose xₙ > x. Then xₙ - x > 0, and so ther
-}
xₙisIncreasing⇒xₙ≤limxₙ : {xs : ℕ → ℝ} → xs isIncreasing → (xₙ→x : IsConvergent xs) →
                          (n : ℕ) → xs n ≤ lim xₙ→x
xₙisIncreasing⇒xₙ≤limxₙ {xs} xₙInc xₙ→x n = let x = lim xₙ→x in
                                            ≮⇒≥ (λ x<xₙ → <-irrefl ≃-refl let N-get = fast-ε-from-convergence xₙ→x (xs n - x) x<xₙ
                                                                                    ; N = suc (proj₁ N-get)
                                                                                    ; M = N ℕ.⊔ n in
                                            begin-strict
  xs n - x    ≤⟨ +-monoˡ-≤ (- x) (isIncreasing⇒isIncreasing₂ xₙInc M n (ℕP.m≤n⊔m N n)) ⟩
  xs M - x    ≤⟨ x≤∣x∣ ⟩
  ∣ xs M - x ∣ <⟨ proj₂ N-get M (ℕP.m≤m⊔n N n) ⟩
  xs n - x     ∎)
  where open ≤-Reasoning

xₙisIncreasing⇒-xₙisDecreasing : {xs : ℕ → ℝ} → xs isIncreasing → (λ n → - xs n) isDecreasing
xₙisIncreasing⇒-xₙisDecreasing {xs} xₙInc n = neg-mono-≤ (xₙInc n)

xₙisDecreasing⇒-xₙisIncreasing : {xs : ℕ → ℝ} → xs isDecreasing → (λ n → - xs n) isIncreasing
xₙisDecreasing⇒-xₙisIncreasing {xs} xₙDec n = neg-mono-≤ (xₙDec n)

{-
xₙ < x ⇒ 0 < x - xₙ

m ≥ n
x - xₘ < x - xₙ
⇒ xₙ < xₘ ≤ xₙ, ⊥
-}
xₙisDecreasing⇒limxₙ≤xₙ : {xs : ℕ → ℝ} → xs isDecreasing → (xₙ→x : IsConvergent xs) →
                          (n : ℕ) → lim xₙ→x ≤ xs n
xₙisDecreasing⇒limxₙ≤xₙ {xs} xₙDec xₙ→x n = let x = lim xₙ→x in begin
  x          ≈⟨ ≃-sym (neg-involutive x) ⟩
  - (- x)    ≤⟨ neg-mono-≤ (xₙisIncreasing⇒xₙ≤limxₙ (xₙisDecreasing⇒-xₙisIncreasing xₙDec) (- x , limitOfNegate xₙ→x) n) ⟩
  - (- xs n) ≈⟨ neg-involutive (xs n) ⟩
  xs n        ∎
  where open ≤-Reasoning
  
xₙ-yₙ→0⇒limxₙ≃limyₙ : {xs ys : ℕ → ℝ} → (xₙ→x : IsConvergent xs) → (yₙ→y : IsConvergent ys) →
                      (λ n → xs n - ys n) ConvergesTo zeroℝ →
                      lim xₙ→x ≃ lim yₙ→y
xₙ-yₙ→0⇒limxₙ≃limyₙ {xs} {ys} (x :^: MkCon xₙ→x) (y :^: MkCon yₙ→y) (MkCon xₙ-yₙ→0) = ∣x-y∣≤k⁻¹⇒x≃y x y
                    (λ @0 {(suc k-1) → let k = suc k-1; N₁-get = xₙ→x (3 ℕ.* k); N₁ = suc (proj₁ N₁-get)
                                          ; N₂-get = yₙ→y (3 ℕ.* k); N₂ = suc (proj₁ N₂-get)
                                          ; N₃-get = xₙ-yₙ→0 (3 ℕ.* k); N₃ = suc (proj₁ N₃-get)
                                          ; N = N₁ ℕ.⊔ N₂ ℕ.⊔ N₃; [3k]⁻¹ = + 1 / (3 ℕ.* k) in
                    begin
  ∣ x - y ∣                                         ≈⟨ ∣-∣-cong (solve 4 (λ x y xₙ yₙ →
                                                      x ⊖ y ⊜ (x ⊖ xₙ) ⊕ (yₙ ⊖ y) ⊕ (xₙ ⊖ yₙ))
                                                      ≃-refl x y (xs N) (ys N)) ⟩
  ∣ (x - xs N) + (ys N - y) + (xs N - ys N) ∣       ≤⟨ ≤-trans (∣x+y∣≤∣x∣+∣y∣ ((x - xs N) + (ys N - y)) (xs N - ys N))
                                                      (+-monoˡ-≤ ∣ xs N - ys N ∣ (∣x+y∣≤∣x∣+∣y∣ (x - xs N) (ys N - y))) ⟩
  ∣ x - xs N ∣ + ∣ ys N - y ∣ + ∣ xs N - ys N ∣       ≈⟨ +-cong (+-congˡ ∣ ys N - y ∣ (∣x-y∣≃∣y-x∣ x (xs N)))
                                                     (∣-∣-cong (solve 1 (λ a → a ⊜ a ⊖ Κ 0ℚᵘ) ≃-refl (xs N - ys N))) ⟩
  ∣ xs N - x ∣ + ∣ ys N - y ∣ + ∣ xs N - ys N - zeroℝ ∣  ≤⟨ +-mono-≤ (+-mono-≤
                                                      (proj₂ N₁-get N (ℕP.≤-trans (ℕP.m≤m⊔n N₁ N₂) (ℕP.m≤m⊔n (N₁ ℕ.⊔ N₂) N₃)))
                                                      (proj₂ N₂-get N (ℕP.≤-trans (ℕP.m≤n⊔m N₁ N₂) (ℕP.m≤m⊔n (N₁ ℕ.⊔ N₂) N₃))))
                                                      (proj₂ N₃-get N (ℕP.m≤n⊔m (N₁ ℕ.⊔ N₂) N₃)) ⟩
  [3k]⁻¹ ⋆ + [3k]⁻¹ ⋆ + [3k]⁻¹ ⋆                  ≈⟨ ≃-trans
                                                     (solve 0 (Κ [3k]⁻¹ ⊕ Κ [3k]⁻¹ ⊕ Κ [3k]⁻¹ ⊜ Κ ([3k]⁻¹ ℚ.+ [3k]⁻¹ ℚ.+ [3k]⁻¹)) ≃-refl)
                                                     (⋆-cong (ℚ.*≡* (ℤsolve 1 (λ k →
                                                     ((ℤΚ (+ 1) :* (ℤΚ (+ 3) :* k) :+ ℤΚ (+ 1) :* (ℤΚ (+ 3) :* k)) :* (ℤΚ (+ 3) :* k) :+
                                                     ℤΚ (+ 1) :* (ℤΚ (+ 3) :* k :* (ℤΚ (+ 3) :* k))) :* k :=
                                                     ℤΚ (+ 1) :* (ℤΚ (+ 3) :* k :* (ℤΚ (+ 3) :* k) :* (ℤΚ (+ 3) :* k)))
                                                     refl (+ k)))) ⟩
  (+ 1 / k) ⋆                                      ∎})
  where open ≤-Reasoning

abstract
  fast-xₙ-yₙ→0⇒limxₙ≃limyₙ : {xs ys : ℕ → ℝ} → (xₙ→x : IsConvergent xs) → (yₙ→y : IsConvergent ys) →
                             (λ n → xs n - ys n) ConvergesTo zeroℝ →
                             lim xₙ→x ≃ lim yₙ→y
  fast-xₙ-yₙ→0⇒limxₙ≃limyₙ = xₙ-yₙ→0⇒limxₙ≃limyₙ

private
  {-
    sum0ᵐ
  -}
  ε-addition-helper : (ε : ℝ) (k : ℕ) {k≢0 : k ≢0} (m : ℕ) → sum0 (λ n → ((+ 1 / k) {k≢0}) ⋆ * ε) m ≃ ((+ m / k) {k≢0}) ⋆ * ε
  ε-addition-helper ε (suc k-1) zero    = let k = suc k-1 in begin-equality
    zeroℝ              ≈⟨ ≃-sym (*-zeroˡ ε) ⟩
    zeroℝ * ε          ≈⟨ *-congʳ (⋆-cong (ℚ.*≡* (ℤP.*-zeroˡ (+ k)))) ⟩
    (+ 0 / k) ⋆ * ε  ∎
    where open ≤-Reasoning
  ε-addition-helper ε (suc k-1) (suc m) = let k = suc k-1 in begin-equality
    sum0 (λ n → (+ 1 / k) ⋆ * ε) m + (+ 1 / k) ⋆ * ε ≈⟨ +-congˡ ((+ 1 / k) ⋆ * ε) (ε-addition-helper ε k m) ⟩
    (+ m / k) ⋆ * ε + (+ 1 / k) ⋆ * ε              ≈⟨ ≃-trans (≃-trans
                                                      (≃-sym (*-distribʳ-+ ε ((+ m / k) ⋆) ((+ 1 / k) ⋆)))
                                                      (*-congʳ (≃-sym (⋆-distrib-+ (+ m / k) (+ 1 / k)))))
                                                      (*-congʳ (⋆-cong (ℚ.*≡* (ℤsolve 2 (λ m k →
                                                      (m :* k :+ ℤΚ (+ 1) :* k) :* k := (ℤΚ (+ 1) :+ m) :* (k :* k))
                                                      refl (+ m) (+ k))))) ⟩
    (+ (suc m) / k) ⋆ * ε                           ∎
    where open ≤-Reasoning

{-
For proofs where we have ε/n + ⋯ + ε/n = ε so we don't have to call the solver on a massive function.
-}
ε-addition : (ε : ℝ) (k : ℕ) {k≢0 : k ≢0} → sum0 (λ n → ((+ 1 / k) {k≢0}) ⋆ * ε) k ≃ ε
ε-addition ε (suc k-1) = let k = suc k-1 in begin-equality
  sum0 (λ n → (+ 1 / k) ⋆ * ε) k ≈⟨ ε-addition-helper ε k k ⟩
  (+ k / k) ⋆ * ε              ≈⟨ *-congʳ (⋆-cong (ℚ.*≡* (ℤP.*-comm (+ k) (+ 1)))) ⟩
  oneℝ * ε                       ≈⟨ *-identityˡ ε ⟩
  ε                             ∎
  where open ≤-Reasoning

abstract
  fast-ε-addition : (ε : ℝ) (k : ℕ) {k≢0 : k ≢0} → sum0 (λ n → ((+ 1 / k) {k≢0}) ⋆ * ε) k ≃ ε
  fast-ε-addition = ε-addition

convergesTo-getter : {xs : ℕ → ℝ} → (xₙ→x : IsConvergent xs) → ConvergesTo xs (lim xₙ→x
convergesTo-getter (x , xₙ→x) = xₙ→x

abstract
  fast-convergesTo-getter : {xs : ℕ → ℝ} → (xₙ→x : IsConvergent xs) → ConvergesTo xs (lim xₙ→x
  fast-convergesTo-getter = convergesTo-getter

{-
Order Limit Theorem
-}
{-
0 > x ⇒ -x > 0 ⇒ -x > xₙ - x > -x
-}
0≤xₙ⇒0≤limxₙ : {xs : ℕ → ℝ} → ((n : ℕ) → zeroℝ ≤ xs n) → (xₙ→x : IsConvergent xs)  → zeroℝ ≤ lim xₙ→x
0≤xₙ⇒0≤limxₙ {xs} 0≤xₙ xₙ→x = ≮⇒≥ λ x<0 → <-irrefl ≃-refl
                              (begin-strict
  - x                  ≤⟨ ≤-respˡ-≃ (+-identityˡ (- x)) (+-monoˡ-≤ (- x) (0≤xₙ N)) ⟩
  xs (N {x<0}) - x     <⟨ ≤-<-trans x≤∣x∣ (proj₂ N-get N ℕP.≤-refl) ⟩
  - x       ∎)
  where
    open ≤-Reasoning

    x : ℝ
    x = lim xₙ→x

    N-get : {x<0 : x < zeroℝ} → ∃ (λ N-1 → (n : ℕ) → n ℕ.≥ suc N-1 → ∣ xs n - x ∣ < - x)
    N-get {x<0} = fast-ε-from-convergence xₙ→x (- x) (0<x⇒posx (<-respˡ-≃ (≃-sym 0≃-0) (neg-mono-< x<0)))

    N : {x<0 : x < zeroℝ} → ℕ
    N {x<0} = suc (proj₁ (N-get {x<0}))

xₙ≤yₙ⇒limxₙ≤limyₙ : {xs ys : ℕ → ℝ} → ((n : ℕ) → xs n ≤ ys n) → (xₙ→x : IsConvergent xs) (yₙ→y : IsConvergent ys) → lim xₙ→x ≤ lim yₙ→y
xₙ≤yₙ⇒limxₙ≤limyₙ {xs} {ys} xₙ≤yₙ xₙ→x yₙ→y = 0≤y-x⇒x≤y (0≤xₙ⇒0≤limxₙ {λ n → ys n - xs n} (λ n → x≤y⇒0≤y-x (xₙ≤yₙ n))
                                              (lim yₙ→y - lim xₙ→x , limitOfSum yₙ→y (- lim xₙ→x , limitOfNegate xₙ→x)))

xₙ≤y⇒limxₙ≤y : {xs : ℕ → ℝ} {y : ℝ} → ((n : ℕ) → xs n ≤ y) → (xₙ→x : IsConvergent xs) → lim xₙ→x ≤ y
xₙ≤y⇒limxₙ≤y {xs} {y} xₙ≤y xₙ→x = xₙ≤yₙ⇒limxₙ≤limyₙ xₙ≤y xₙ→x (y , limitOfConst (λ n → ≃-refl))

{-
Common Limit Lemma:
  Let (xₙ) and (yₙ) be sequences such that
(i)   xₙ ≤ yₙ (n∈ℕ),
(ii)  (xₙ - yₙ) → 0,
(iii) (xₙ) is nondecreasing (xₙ ≤ xₙ₊₁), and
(iv)  (yₙ) is nonincreasing (yₙ₊₁ ≤ yₙ)
Then xₙ and yₙ converge to a common limit.
Proof:
  Let ε > 0. Then ∣xₙ - yₙ∣ < ε/2 for sufficiently large n, and for sufficiently large m > n, we have
∣xₘ - xₙ∣ = xₘ - xₙ + yₘ - yₘ
         ≤ xₘ - yₘ + yₙ - xₙ
         < ε/2 + ε/2 = ε
and
∣yₘ - yₙ∣ = yₙ - yₘ - xₙ + xₙ
         = yₙ - xₙ + xₙ - yₘ
         ≤ yₙ - xₙ + xₘ - yₘ
         < ε/2 + ε/2 = ε.
Hence (xₙ) and (yₙ) are Cauchy sequences. Then, since (xₙ - yₙ) → 0, their limits are equal.         □

Proposition:
  If x ≤ yₙ for all n∈ℕ and (yₙ)→y, then x ≤ y.
Proof:
  limx ≤ limyₙ
  x ≤ y
-}
common-limit-lemma : {xs ys : ℕ → ℝ} →
                     ((n : ℕ) → xs n ≤ ys n) →
                     (λ n → xs n - ys n) ConvergesTo zeroℝ →
                     xs isIncreasing → ys isDecreasing → 
                     ∃ λ (xₙ→x : IsConvergent xs) → ∃ λ (yₙ→y : IsConvergent ys) → lim xₙ→x ≃ lim yₙ→y × ((n : ℕ) → xs n ≤ lim xₙ→x ≤ ys n)
common-limit-lemma {xs} {ys} xₙ≤yₙ (MkCon xₙ-yₙ→0) xₙInc yₙDec = xₙ→x , yₙ→y , fast-xₙ-yₙ→0⇒limxₙ≃limyₙ xₙ→x yₙ→y (MkCon xₙ-yₙ→0) ,
                                                                λ n → xₙisIncreasing⇒xₙ≤limxₙ xₙInc xₙ→x n ,
                                                                ≤-trans (xₙ≤yₙ⇒limxₙ≤limyₙ xₙ≤yₙ xₙ→x yₙ→y) (xₙisDecreasing⇒limxₙ≤xₙ yₙDec yₙ→y n)
  where
    open ≤-Reasoning
    
    xₙ→x : IsConvergent xs
    xₙ→x = fast-cauchy-convergence (λ @0 {(suc k-1) → let k = suc k-1; N-get = xₙ-yₙ→0 (2 ℕ.* k); N = suc (proj₁ N-get) in
                     ℕ.pred N , λ m n m>n n≥N → begin
      ∣ xs m - xs n ∣                            ≈⟨ 0≤x⇒∣x∣≃x (x≤y⇒0≤y-x (isIncreasing⇒isIncreasing₂ xₙInc m n (ℕP.<⇒≤ m>n))) ⟩
      xs m - xs n                               ≈⟨ solve 3 (λ xₘ xₙ yₘ → xₘ ⊖ xₙ ⊜ xₘ ⊖ yₘ ⊕ (yₘ ⊖ xₙ))
                                                   ≃-refl (xs m) (xs n) (ys m) ⟩
      xs m - ys m + (ys m - xs n)               ≤⟨ +-monoʳ-≤ (xs m - ys m) (+-monoˡ-≤ (- xs n)
                                                   (isDecreasing⇒isDecreasing₂ yₙDec m n (ℕP.<⇒≤ m>n))) ⟩
      xs m - ys m + (ys n - xs n)               ≈⟨ solve 3 (λ a b c → a ⊕ (b ⊖ c) ⊜ (a ⊖ Κ 0ℚᵘ) ⊕ (Κ 0ℚᵘ ⊖ (c ⊖ b)))
                                                   ≃-refl (xs m - ys m) (ys n) (xs n) ⟩
      (xs m - ys m - zeroℝ) + (zeroℝ - (xs n - ys n)) ≤⟨ +-mono-≤
                                                   (≤-trans x≤∣x∣ (proj₂ N-get m (ℕP.≤-trans n≥N (ℕP.<⇒≤ m>n))))
                                                   (≤-trans x≤∣x∣ (≤-respˡ-≃ (∣x-y∣≃∣y-x∣ (xs n - ys n) zeroℝ) (proj₂ N-get n n≥N))) ⟩
      (+ 1 / (2 ℕ.* k)) ⋆ + (+ 1 / (2 ℕ.* k)) ⋆ ≈⟨ ≃-trans (≃-sym (⋆-distrib-+ _ _)) (⋆-cong (ℚ.*≡* (ℤsolve 1 (λ k →
                                                   (ℤΚ (+ 1) :* (ℤΚ (+ 2) :* k) :+ ℤΚ (+ 1) :* (ℤΚ (+ 2) :* k)) :* k :=
                                                   ℤΚ (+ 1) :* (ℤΚ (+ 2) :* k :* (ℤΚ (+ 2) :* k)))
                                                   refl (+ k)))) ⟩
      (+ 1 / k) ⋆                                ∎})

    yₙ→y : IsConvergent ys
    yₙ→y = fast-cauchy-convergence λ @0 {(suc k-1) → let k = suc k-1; N-get = xₙ-yₙ→0 (2 ℕ.* k); N = suc (proj₁ N-get) in
                     ℕ.pred N , λ m n m>n n≥N → begin
      ∣ ys m - ys n ∣                            ≈⟨ ≃-trans (∣x-y∣≃∣y-x∣ (ys m) (ys n))
                                                   (0≤x⇒∣x∣≃x (x≤y⇒0≤y-x (isDecreasing⇒isDecreasing₂ yₙDec m n (ℕP.<⇒≤ m>n)))) ⟩
      ys n - ys m                               ≈⟨ solve 3 (λ xₙ yₙ yₘ → yₙ ⊖ yₘ ⊜ yₙ ⊖ xₙ ⊕ (xₙ ⊖ yₘ)) ≃-refl (xs n) (ys n) (ys m)  ⟩
      ys n - xs n + (xs n - ys m)               ≤⟨ +-monoʳ-≤ (ys n - xs n) (+-monoˡ-≤ (- ys m)
                                                   (isIncreasing⇒isIncreasing₂ xₙInc m n (ℕP.<⇒≤ m>n))) ⟩
      ys n - xs n + (xs m - ys m)               ≈⟨ solve 4 (λ xₘ xₙ yₘ yₙ → yₙ ⊖ xₙ ⊕ (xₘ ⊖ yₘ) ⊜ ⊝ (xₙ ⊖ yₙ ⊖ Κ 0ℚᵘ) ⊕ (xₘ ⊖ yₘ ⊖ Κ 0ℚᵘ))
                                                   ≃-refl (xs m) (xs n) (ys m) (ys n) ⟩
      - (xs n - ys n - zeroℝ) + (xs m - ys m - zeroℝ) ≤⟨ +-mono-≤
                                                   (≤-trans x≤∣x∣ (≤-respˡ-≃ (≃-sym ∣-x∣≃∣x∣) (proj₂ N-get n n≥N)))
                                                   (≤-trans x≤∣x∣ (proj₂ N-get m (ℕP.≤-trans n≥N (ℕP.<⇒≤ m>n)))) ⟩
      (+ 1 / (2 ℕ.* k)) ⋆ + (+ 1 / (2 ℕ.* k)) ⋆ ≈⟨ ≃-trans (≃-sym (⋆-distrib-+ _ _)) (⋆-cong (ℚ.*≡* (ℤsolve 1 (λ k →
                                                   (ℤΚ (+ 1) :* (ℤΚ (+ 2) :* k) :+ ℤΚ (+ 1) :* (ℤΚ (+ 2) :* k)) :* k :=
                                                   ℤΚ (+ 1) :* (ℤΚ (+ 2) :* k :* (ℤΚ (+ 2) :* k)))
                                                   refl (+ k)))) ⟩
      (+ 1 / k) ⋆                                ∎}

    limxₙ≃limyₙ : lim xₙ→x ≃ lim yₙ→y
    limxₙ≃limyₙ = fast-xₙ-yₙ→0⇒limxₙ≃limyₙ xₙ→x yₙ→y (MkCon xₙ-yₙ→0)
    

abstract
  fast-common-limit-lemma :  {xs ys : ℕ → ℝ} →
                             ((n : ℕ) → xs n ≤ ys n) →
                             (λ n → xs n - ys n) ConvergesTo zeroℝ →
                             xs isIncreasing → ys isDecreasing → 
                             ∃ λ (xₙ→x : IsConvergent xs) → ∃ λ (yₙ→y : IsConvergent ys) → lim xₙ→x ≃ lim yₙ→y × ((n : ℕ) → xs n ≤ lim xₙ→x ≤ ys n)
  fast-common-limit-lemma = common-limit-lemma


convergence-getter : {xs : ℕ → ℝ} → (xₙ→x : IsConvergent xs) →
                     (k : ℕ) {k≢0 : k ≢0} → ∃ λ Nₖ-1 → (n : ℕ) → n ℕ.≥ suc Nₖ-1 →
                     ∣ xs n - lim xₙ→x ∣ ≤ ((+ 1 / k) {k≢0}) ⋆
convergence-getter (x :^: MkCon xₙ→x) = xₙ→x

abstract
  fast-convergence-getter : {xs : ℕ → ℝ} → (xₙ→x : IsConvergent xs) →
                            (k : ℕ) {k≢0 : k ≢0} → ∃ λ Nₖ-1 → (n : ℕ) → n ℕ.≥ suc Nₖ-1 →
                            ∣ xs n - lim xₙ→x ∣ ≤ ((+ 1 / k) {k≢0}) ⋆
  fast-convergence-getter = convergence-getter
-}
-}
