-- Product types (especially the existence quantifier)
-- with a non-erased value member and an erased proof member.

{-# OPTIONS --without-K --safe #-}

open import Agda.Primitive

record Σ0 {a b} (A : Set a) (@0 B : A → Set b) : Set (a ⊔ b) where
  constructor _,_
  field
    proj₁ : A
    @0 proj₂ : B proj₁

open Σ0 public
infixr 4 _,_

∃0 : ∀ {a b} {A : Set a} → @0 (A → Set b) → Set (a ⊔ b)
∃0 = Σ0 _

_×0_ : ∀ {a b} (A : Set a) → (@0 B : Set b) → Set (a ⊔ b)
A ×0 B = Σ0 A (λ _ → B)

infixr 2 _×0_
