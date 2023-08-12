-- A Main function to experiment with the rational (1/n!) series.
import Numeric.Natural
import Control.Monad.ST
import Data.STRef
import Control.Monad

{-
-- import Data.Ratio

fact :: Natural -> Natural
fact 0 = 1
fact n = product [1..n]

(//) :: Integer -> Natural -> Rational
int // nat = int % (fromIntegral nat)

a :: Natural -> Rational
a n = 1 // fact n

sa :: Natural -> Integer
sa 0 = 0
sa n = sum $ map (denominator . a) [0..(n-1)]

-- When you only sum the denominators, it actually works.
main :: IO ()
main = putStrLn $ show $ sa 5000
-}

-- Now let's try it with unnormalised rationals.
data URational = (:/) { numerator    :: Integer
                      , denominator  :: Integer }
infixl 7 :/

instance Show URational where
  show (a :/ b) = show a ++ " :/ " ++ show b

instance Eq URational where
  (a :/ b) == (c :/ d)  = a * d == b * c

-- Let's try something.
-- We will try to normalise "a bit". But not with every existing prime;
-- just with simple ones (let's say, with those less than 100).
{-
firstPrimes :: Integer -> [Integer]
firstPrimes limit = filter isPrime [2..limit]
  where
    isPrime :: Integer -> Bool
    isPrime p = null $ map ...
-}
{-
-- You know what?
firstPrimes :: [Integer]
firstPrimes = [2, 3, 5, 7{-, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97-}]

fastSimplify :: URational -> URational
fastSimplify q = runST $ fastSimplify' q firstPrimes
  where
  fastSimplify' :: URational -> [Integer] -> ST s URational
  fastSimplify' (a :/ b) ps = do
           a <- newSTRef a
           b <- newSTRef b
           go a b ps
  go :: STRef s Integer -> STRef s Integer -> [Integer] -> ST s URational
  go a b []       = do
           a <- readSTRef a
           b <- readSTRef b
           return (a :/ b)
  go a b (p:ps)   = do
           divideIfCan a b p
           go a b ps
    where
    divideIfCan :: STRef s Integer -> STRef s Integer -> Integer -> ST s ()
    divideIfCan a b p = do
      ai <- readSTRef a
      bi <- readSTRef b
      if mod ai p == 0 && mod bi p == 0 then do
             writeSTRef a (div ai p)
             writeSTRef b (div bi p)
             divideIfCan a b p
      else return ()
-}
{- Example:
fact 111 :/ fact 121 ==
1762952551090244663872161047107075788761409536026565516041574063347346955087248316436555574598462315773196047662837978913145847497199871623320096254145331200000000000000000000000000 :/ 809429852527344373968162284544935082997082306309701607045776233628497660426640521713391773997910182738287074185078904956856663439318382745047716214841147650721760223072092160000000000000000000000000000
fastSimplify (fact 111 :/ fact 121) ==
43460135791085702137040043234457948964634454523606263975103421610587590258590012051275740816047522914869026065786231961415687730981409549713134765625 :/ 19953986443050967911137516399950759384856568759636071537559231241605595674472345921933519198680423836931073196347805741381935098722870933593027275924682617187500000000000
fact 111 % fact 121 ==
1 % 459133090125866956800 -}

instance Num URational where
  -- Actually, fastSimplify is even worse than with (%)... it doesn't even like 1000.
  {-
  (a :/ b) + (c :/ d) = fastSimplify $ (a * d + c * b) :/ (b * d)
  (a :/ b) * (c :/ d) = fastSimplify $ (a * c) :/ (b * d)
  -}
  (a :/ b) + (c :/ d) = (a * d + c * b) :/ (b * d)
  (a :/ b) * (c :/ d) = (a * c) :/ (b * d)
  abs (a :/ b)        = abs a :/ abs b
  signum (a :/ b)     = fromInteger (signum a * signum b)
  fromInteger n       = n :/ 1
  negate (a :/ b)     = negate a :/ b

fact :: Integer -> Integer
fact 0 = 1
fact n
  | n>0        = product [1..n]
  | otherwise  = error "called fact with a negative number"

factSeq :: Integer -> URational
factSeq n = 1 :/ fact n

-- fastSimplify is quite slow even if we only apply it to the end result.
series :: Integer -> URational
series 0 = 0
series n = {-fastSimplify $-} sum $ map factSeq [0..(n-1)]

main :: IO ()
main = putStrLn $ show $ series 2000
