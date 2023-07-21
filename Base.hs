module Base where

import Numeric.Natural
import Data.Ratio

-- here we are going to use the real denominator, not denominator-1
type ℚᵘ = Rational

-- this will be prettier if the problem with denominatorℕ in Agda gets solved
--() "(suc . \ r -> denominator-1 r)" => "denominatorNat"
denominatorNat :: Rational -> Natural
denominatorNat = fromInteger . denominator

denominatorMinus1 :: Rational -> Natural
denominatorMinus1 = (\n -> n-1) . denominatorNat

--() "divℕ" => "`divℕ`"
divNat :: Integer -> Natural -> Integer
divNat z n = z `div` (fromIntegral n)

--() "ℤ.∣_∣" => "intAbs"
intAbs :: Integer -> Natural
intAbs = fromInteger . abs

suc :: Natural -> Natural
suc = (+ 1)

-- pred is already used in Prelude
predNat :: Natural -> Natural
predNat n = n-1

-- The replacement for the constructor of the Agda ℚᵘ type.
mkℚᵘ :: Integer -> Natural -> Rational
mkℚᵘ a b = a % fromIntegral (b+1)

-- For the _/_ operator.
-- (%) is not enough, as we need type Integer -> Natural -> Rational.
(//) :: Integer -> Natural -> Rational
p // q = p % (toInteger q)

--() "ℕ.+" => "+"
--() "ℕ.-" => "-"
--() "ℕ.*" => "*"

--() "ℤ.+" => "+"
--() "ℤ.-" => "-"
--() "ℤ.*" => "*"

--() "ℚ.+" => "+"
--() "ℚ.-_" => "-"
--() "ℚ.*" => "*"
--() "ℚ.∣_∣" => "abs"

--() "ℕD./" => "`div`"

-- this can be omitted:
--() "pos" => ""

--() "/" => "%"

--() "(ℕ.⊔)" => "max"
--() "(ℚ.⊓)" => "min"
--() "(ℚ.⊔)" => "max"
