{-# LANGUAGE ViewPatterns #-}

module Numeric.QuadraticIrrational
  ( QI, qi, qi', unQI, unQI'
  , qiToFloat
  , qiReduce
  , qiAdd, qiSub, qiMul, qiDiv, qiRecip, qiPow
  ) where

-- TODO http://hackage.haskell.org/package/continued-fractions

import Control.Applicative ((<$))
import Control.Arrow (first)
import Control.Monad (guard)
import Data.List
import Data.Ratio
import Math.NumberTheory.Primes.Factorisation

-- | @a + b √c@
data QI = QI !Rational  -- ^ a
             !Rational  -- ^ b
             !Integer   -- ^ c
  deriving (Show, Read)

-- | Given @a@, @b@ and @c@ such that @n = a + b √c@, constuct a 'QI'
-- corresponding to @n@.
qi :: Rational  -- ^ a
   -> Rational  -- ^ b
   -> Integer   -- ^ c
   -> QI
qi a 0 _ = QI a 0 0
qi a _ 0 = QI a 0 0
qi a b (nonNegative "qi" -> c) = QI a b c

-- | Given @a@, @b@, @c@ and @d@ such that @n = (a + b √c)/d@, constuct a 'QI'
-- corresponding to @n@.
qi' :: Integer  -- ^ a
    -> Integer  -- ^ b
    -> Integer  -- ^ c
    -> Integer  -- ^ d
    -> QI
qi' a b (nonNegative "qi'" -> c) (nonZero "qi'" -> d) = qi (a % d) (b % d) c

-- | Given @n@ and @f@ such that @n = a + b √c@, run @f a b c@.
unQI :: QI -> (Rational -> Rational -> Integer -> a) -> a
unQI (QI a b c) f = f a b c

-- | Given @n@ and @f@ such that @n = (a + b √c)/d@, run @f a b c d@.
unQI' :: QI -> (Integer -> Integer -> Integer -> Integer -> a) -> a
unQI' n f = unQI n $ \a b c ->
  -- aN/aD + bN/bD = (aN bD + bN aD) / (aD bD)
  let a' = aN * bD
      b' = bN * aD
      d' = aD * bD
      (aN, aD) = (numerator a, denominator a)
      (bN, bD) = (numerator b, denominator b)
  in  f a' b' c d'

qiToFloat :: Floating a => QI -> a
qiToFloat n = unQI n $ \a b c ->
  fromRational a + fromRational b * sqrt (fromInteger c)

-- | Reduce a 'QI' to a potentially simpler form. Will factorize the number
-- inside the square root internally.
qiReduce :: QI -> QI
qiReduce n = unQI n go
  where
    go a b c
      | c  == 0   = qi a 0 0
      | c' == 1   = qi (a + b') 0 0
      | otherwise = qi a b' c'
      where
        ~(b', c') = first (b *) (separateSquareFactors c)

-- | Given @c@ such that @n = √c@, return @(b, c)@ such that @n = b √c@.
separateSquareFactors :: Integer -> (Rational, Integer)
separateSquareFactors = first fromInteger . foldl' go (1,1) . factorise
                      . nonNegative "separateSquareFactors"
  where
    go :: (Integer, Integer) -> (Integer, Int) -> (Integer, Integer)
    go ~(a, b) ~(fac, pow)
      | even pow  = (a*fac^(pow     `div` 2), b)
      | otherwise = (a*fac^((pow-1) `div` 2), b*fac)

qiAdd :: QI -> Rational -> QI
qiAdd n x = unQI n $ \a b c -> qi (a+x) b c

qiSub :: QI -> Rational -> QI
qiSub n x = qiAdd n (negate x)

qiMul :: QI -> Rational -> QI
qiMul n x = unQI n $ \a b c -> qi (a*x) (b*x) c

qiDiv :: QI -> Rational -> QI
qiDiv n (nonZero "qiDiv" -> x) = qiMul n (recip x)

qiRecip :: QI -> Maybe QI
qiRecip n = unQI' n $ \a b c d ->
  -- 1/((a + b √c)/d)                       =
  -- d/(a + b √c)                           =
  -- d (a − b √c) / ((a + b √c) (a − b √c)) =
  -- d (a − b √c) / (a² − b² c)             =
  -- a d − b d √c / (a² − b² c)
  let denom = (a*a - b*b * toInteger c)
  in  qi' (a * d) (negate (b * d)) c denom <$ guard (denom /= 0)

qiPow :: QI -> Integer -> QI
qiPow num (nonNegative "qiPow" -> pow) = unQI num $ \a b c ->
  let ~(a', b') = foldl' (addTerm a b c) (0, 0) . map binom $ [0..pow]
  in  qi a' b' c
  where
    -- multiplier, a power, (b √c) power
    binom k = (pow `choose` k, pow - k, k)

    -- (a + b √c)⁴                                                     =
    -- a⁴  +  4 a³ (b √c)  +  6 a² (b √c)²  +  4 a (b √c)³  +  (b √c)⁴ =
    -- a⁴  +  4 a³ b √c    +  6 a² b² c     +  4 a b³ √c³   +  b⁴ c²   =
    --  a⁴  +  6 a² b² c  +  b⁴ c²   +   4 a³ b √c    +  4 a b³ √c³    =
    -- (a⁴  +  6 a² b² c  +  b⁴ c²)  +  (4 a³ b √c/√c +  4 a b³ √c³/√c) √c
    addTerm a b c ~(a', b') ~(mul, aPow, bsqcPow)
      | even bsqcPow = (a' + term a b c mul aPow bsqcPow bsqcPow, b')
      | otherwise    = (a', b' + term a b c mul aPow bsqcPow (bsqcPow-1))

    term a b c mul aPow bPow cPow =
      fromInteger mul * a^aPow * b^bPow * fromInteger c^(cPow `div` 2)

choose :: Integral a => a -> a -> a
choose n' k'
  | k' < n' - k' = choose n' (n' - k')
  | otherwise = go n' k'
  where
    go _ 0 = 1
    go 0 _ = 0
    go n k = (n * choose (n - 1) (k - 1)) `div` k

nonNegative :: (Num a, Ord a, Show a) => String -> a -> a
nonNegative name = validate name "non-negative" (>= 0)

nonZero :: (Num a, Eq a, Show a) => String -> a -> a
nonZero name = validate name "non-zero" (/= 0)

validate :: Show a => String -> String -> (a -> Bool) -> a -> a
validate name expected f a
  | f a = a
  | otherwise =
      error ("Numeric.QuadraticIrrational." ++ name ++ ": Got " ++ show a
              ++ ", expected " ++ expected)
