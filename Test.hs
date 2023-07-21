-- A test file, where I try what works and how fast.

module Test where

import Prelude hiding (seq)
import Numeric.Natural
import Data.Ratio

import Base
import Real

-- Now a test...
strangify :: ℚᵘ -> ℝ
strangify p = Mkℝ (\ n -> p + (1 % fromIntegral n))

testPow :: Natural -> ℚᵘ
testPow n = seq (pow (strangify (1 % 2)) n) 100000000000
-- testPow 70 is _very_ slow, but runs
-- it really runs out of memory, I think
