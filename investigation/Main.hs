-- A Main function to experiment with the rational (1/n!) series;
-- now using Int instead of Integer.
import Numeric.Natural
import Data.Ratio

type IntRational = Ratio Int

fact :: Int -> Int
fact 0 = 1
fact n
  | n>0        = product [1..n]
  | otherwise  = error "called fact with a negative number"

factSeq :: Int -> IntRational
factSeq n = 1 % fact n

-- fastSimplify is quite slow even if we only apply it to the end result.
series :: Int -> IntRational
series 0 = 0
series n = sum $ map factSeq [0..(n-1)]

main :: IO ()
main = putStrLn $ show $ series 2000
