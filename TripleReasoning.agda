------------------------------------------------------------------------
-- A modified file based on the Agda standard library. Allows reasoning
-- with erased equality and _≤_ types and
-- a non-erased _<_ with erased type parameters.
-- But I don't think this would be useful
-- anywhere outside of this library, apart from being an example.
--
-- The basic code for equational reasoning with three relations:
-- equality, strict ordering and non-strict ordering.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

open import Relation.Binary
open import Data.Product using (_×_ ; _,_)

module TripleReasoning {a ℓ₁ ℓ₂ ℓ₃} {A : Set a}
  {@0 _≈_ : (x y : A) → Set}
  {@0 _≤_ : (x y : A) → Set}
  {_<_ : (@0 x y : A) → Set}

  -- instead of (isPreorder : IsPreorder _≈_ _≤_):
  (@0 ≈-refl  : Reflexive _≈_)
  (@0 ≈-sym   : Symmetric _≈_)
  (@0 ≈-trans : Transitive _≈_)
  (@0 ≤-reflexive : _≈_ ⇒ _≤_)
  (@0 ≤-trans : Transitive _≤_)

  (<-trans : (x y z : A) → @0 x < y → y < z → x < z)
  (<-respʳ-≈ : (x y z : A) → @0 y ≈ z → x < y → x < z)
  (<-respˡ-≈ : (x y z : A) → @0 y ≈ z → y < x → z < x)
  (@0 <⇒≤ : {x y : A} → x < y → x ≤ y)
  (<-≤-trans : (x y z : A) → x < y → @0 y ≤ z → x < z)
  (≤-<-trans : (x y z : A) → @0 x ≤ y → y < z → x < z)
  where

{-
-- Creating the implicitly parametered versions from the original ones, where necessary.
<-trans : {x y z : A} → x < y → y < z → x < z
<-trans {x} {y} {z} = <-trans-explicit x y z
<-resp-≈ : {x y z : A} → x < y → y < z → x < z
<-resp-≈ {x} {y} {z} = <-res
-}

open import Data.Product using (proj₁; proj₂)
open import Function.Base using (case_of_; id)
open import Level using (Level; _⊔_; Lift; lift)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; sym)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (True; toWitness)

-- Instead of IsPreorder's default definitions:
@0 ≤-respˡ-≈ : ∀ {x y z : A} → x ≈ y → x ≤ z → y ≤ z       -- _≤_ Respectsˡ _≈_
≤-respˡ-≈ x≈y x≤z = ≤-trans (≤-reflexive (≈-sym x≈y)) x≤z

@0 ≤-respʳ-≈ : ∀ {x y z : A} → x ≈ y → z ≤ x → z ≤ y       -- _≤_ Respectsʳ _≈_
≤-respʳ-≈ x≈y z≤x = ≤-trans z≤x (≤-reflexive x≈y)

{-
@0 ≤-resp-≈ : _≤_ Respects₂ _≈_
≤-resp-≈ = ≤-respʳ-≈ , ≤-respˡ-≈
-}

------------------------------------------------------------------------
-- A datatype to abstract over the current relation

infix 4 _IsRelatedTo_

data _IsRelatedTo_ (@0 x y : A) : Set (a ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) where
  strict    : (x<y : x < y) → x IsRelatedTo y
  nonstrict : (@0 x≤y : x ≤ y) → x IsRelatedTo y
  equals    : (@0 x≈y : x ≈ y) → x IsRelatedTo y


------------------------------------------------------------------------
-- Types that are used to ensure that the final relation proved by the
-- chain of reasoning can be converted into the required relation.

data IsStrict {@0 x y} : (x IsRelatedTo y) → Set (a ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) where
  isStrict : ∀ x<y → IsStrict (strict x<y)

IsStrict? : ∀ {@0 x y} (x≲y : x IsRelatedTo y) → Dec (IsStrict x≲y)
IsStrict? (strict    x<y) = yes (isStrict x<y)
IsStrict? (nonstrict _)   = no λ()
IsStrict? (equals    _)   = no λ()

extractStrict : ∀ {@0 x y} {x≲y : x IsRelatedTo y} → IsStrict x≲y → x < y
extractStrict (isStrict x<y) = x<y

data IsEquality {@0 x y} : @0 (x IsRelatedTo y) → Set (a ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) where
  @0 isEquality : ∀ (@0 x≈y : x ≈ y) → IsEquality (equals x≈y)

@0 IsEquality? : ∀ {x y} (x≲y : x IsRelatedTo y) → Dec (IsEquality x≲y)
IsEquality? (strict    _) = no λ()
IsEquality? (nonstrict _) = no λ()
IsEquality? (equals x≈y)  = yes (isEquality x≈y)

-- This is not compatible with Cubical Agda for some reason. But for now, so be it.
@0 extractEquality : ∀ {@0 x y} {x≲y : x IsRelatedTo y} → @0 (IsEquality x≲y) → x ≈ y
extractEquality (isEquality x≈y) = x≈y

------------------------------------------------------------------------
-- Reasoning combinators

-- See `Relation.Binary.Reasoning.Base.Partial` for the design decisions
-- behind these combinators.

infix  1 begin_ begin-strict_ begin-equality_
infixr 2 step-< step-≤ step-≈ step-≈˘ step-≡ step-≡˘ _≡⟨⟩_
infix  3 _∎

-- Beginnings of various types of proofs

@0 begin_ : ∀ {x y} → x IsRelatedTo y → x ≤ y
begin (strict    x<y) = <⇒≤ x<y
begin (nonstrict x≤y) = x≤y
begin (equals    x≈y) = ≤-reflexive x≈y

begin-strict_ : ∀ {x y} (r : x IsRelatedTo y) → {s : True (IsStrict? r)} → x < y
begin-strict_ r {s} = extractStrict (toWitness s)

@0 begin-equality_ : ∀ {x y} (r : x IsRelatedTo y) → {s : True (IsEquality? r)} → x ≈ y
begin-equality_ r {s} = extractEquality (toWitness s)

-- Step with the strict relation

step-< : ∀ (x : A) {y z : A} → y IsRelatedTo z → x < y → x IsRelatedTo z
step-< x {y} {z} (strict    y<z) x<y = strict (<-trans x y z x<y y<z)
step-< x {y} {z} (nonstrict y≤z) x<y = strict (<-≤-trans x y z x<y y≤z)
step-< x {y} {z} (equals    y≈z) x<y = strict (<-respʳ-≈ x y z y≈z x<y)

-- Step with the non-strict relation

step-≤ : ∀ (x : A) {y z : A} → y IsRelatedTo z → @0 (x ≤ y) → x IsRelatedTo z
step-≤ x {y} {z} (strict    y<z) x≤y = strict    (≤-<-trans x y z x≤y y<z)
step-≤ x         (nonstrict y≤z) x≤y = nonstrict (≤-trans x≤y y≤z)
step-≤ x         (equals    y≈z) x≤y = nonstrict (≤-respʳ-≈ y≈z x≤y)

-- Step with the setoid equality

step-≈  : ∀ (x : A) {y z : A} → y IsRelatedTo z → @0 x ≈ y → x IsRelatedTo z
step-≈ x {y} {z} (strict    y<z) x≈y = strict    (<-respˡ-≈ z y x (≈-sym x≈y) y<z)
step-≈ x {y} {z} (nonstrict y≤z) x≈y = nonstrict (≤-respˡ-≈ (≈-sym x≈y) y≤z)
step-≈ x         (equals    y≈z) x≈y = equals    (≈-trans x≈y y≈z)

-- Flipped step with the setoid equality

step-≈˘ : ∀ (x : A) {y z : A} → y IsRelatedTo z → @0 y ≈ x → x IsRelatedTo z
step-≈˘ x y∼z x≈y = step-≈ x y∼z (≈-sym x≈y)

-- A version of subst.

subst : ∀ {a} {X : Set a} (P : X → Set) {@0 x y : X} → @0 x ≡ y → P x → P y
subst P refl Px = Px

-- Step with non-trivial propositional equality

step-≡ : ∀ (@0 x : A) {@0 y z : A} → y IsRelatedTo z → x ≡ y → x IsRelatedTo z
step-≡ x {y} {z} (strict    y<z) x≡y = strict (subst (_< z) {y} {x} (sym x≡y) y<z)
step-≡ x {y} {z} (nonstrict y≤z) x≡y = nonstrict (subst (_≤ z) (sym x≡y) y≤z)
step-≡ x {y} {z} (equals    y≈z) x≡y = equals    (subst (_≈ z) (sym x≡y) y≈z)

-- Flipped step with non-trivial propositional equality

step-≡˘ : ∀ x {y z} → y IsRelatedTo z → y ≡ x → x IsRelatedTo z
step-≡˘ x y∼z x≡y = step-≡ x y∼z (sym x≡y)

-- Step with trivial propositional equality

_≡⟨⟩_ : ∀ (x : A) {y} → x IsRelatedTo y → x IsRelatedTo y
x ≡⟨⟩ x≲y = x≲y

-- Termination step

_∎ : ∀ x → x IsRelatedTo x
x ∎ = equals ≈-refl

-- Syntax declarations

syntax step-<  x y∼z x<y = x <⟨  x<y ⟩ y∼z
syntax step-≤  x y∼z x≤y = x ≤⟨  x≤y ⟩ y∼z
syntax step-≈  x y∼z x≈y = x ≈⟨  x≈y ⟩ y∼z
syntax step-≈˘ x y∼z y≈x = x ≈˘⟨ y≈x ⟩ y∼z
syntax step-≡  x y∼z x≡y = x ≡⟨  x≡y ⟩ y∼z
syntax step-≡˘ x y∼z y≡x = x ≡˘⟨ y≡x ⟩ y∼z
