-- Product types (especially the existence quantifier)
-- with a non-erased value member and an erased proof member.
-- ∃0 will often be used throughout the library.

-- {-# OPTIONS --without-K --safe #-}    commented out for agda2hs

open import Agda.Primitive

record Σ0 {i j} (a : Set i) (@0 b : a → Set j) : Set (i ⊔ j) where
  constructor _:&:_                      -- see https://stackoverflow.com/questions/10548170/what-characters-are-permitted-for-haskell-operators
  field
    proj₁ : a
    @0 proj₂ : b proj₁
{-# COMPILE AGDA2HS Σ0 newtype #-}
-- And sorry, you'll have to use _:&:_ instead of _,_.
open Σ0 public
infixr 4 _:&:_

∃0 : ∀ {a b} {A : Set a} → @0 (A → Set b) → Set (a ⊔ b)
∃0 = Σ0 _            -- it makes strange things from this...

{-
-- let's try something
open import Agda.Builtin.Bool
open import Agda.Builtin.Unit

TestType : Set
TestType = ∃0 {A = Bool} (λ {true → ⊤ ; false → ⊤})
{-# COMPILE AGDA2HS TestType #-}

well, this doesn't really work:
type TestType = ∃0
-}

-- doesn't work either... never mind; we don't really use it anyway
_×0_ : ∀ {a b} (A : Set a) → (@0 B : Set b) → Set (a ⊔ b)
A ×0 B = Σ0 A (λ _ → B)

infixr 2 _×0_
