-- Custom product types with various forms of erasure.

-- {-# OPTIONS --without-K --safe #-}    commented out for agda2hs
module ErasureProduct where

open import Agda.Primitive

-- A sigma type (especially the existence quantifier)
-- with a non-erased value member and an erased proof member.
-- ∃0 will often be used throughout the library as a shortening.
record Σ0 {i j} (a : Set i) (@0 b : a → Set j) : Set (i ⊔ j) where
  constructor _:&:_                      -- see https://stackoverflow.com/questions/10548170/what-characters-are-permitted-for-haskell-operators
  field
    proj₁ : a
    @0 proj₂ : b proj₁
-- And sorry, you'll have to use _:&:_ instead of _,_.
open Σ0 public
infixr 4 _:&:_
{-# COMPILE AGDA2HS Σ0 newtype #-}

∃0 : ∀ {a b} {A : Set a} → @0 (A → Set b) → Set (a ⊔ b)
∃0 = Σ0 _            -- it makes strange things from this...

-- doesn't work either... never mind; we don't really use it anyway
_×0_ : ∀ {a b} (A : Set a) → (@0 B : Set b) → Set (a ⊔ b)
A ×0 B = Σ0 A (λ _ → B)
infixr 2 _×0_

-- A record type which has both members compiled,
-- but the argument of the lambda is erased;
-- so that it won't be dependent-typed after compilation.
-- Haskell doesn't allow multiple constructors or destructors with the same name; hence the ' after the names.
record Σ' {i j} (a : Set i) (b : @0 a → Set j) : Set (i ⊔ j) where
  constructor _:^:_                      -- see https://stackoverflow.com/questions/10548170/what-characters-are-permitted-for-haskell-operators
  field
    proj₁' : a
    proj₂' : b proj₁'
open Σ' public
infixr 4 _:^:_
{-# COMPILE AGDA2HS Σ' #-}
