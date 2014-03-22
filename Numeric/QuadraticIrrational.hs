{-# LANGUAGE ViewPatterns #-}

module Numeric.QuadraticIrrational
  ( QI, qi, qi', runQI, runQI', unQI, unQI'
  , qiToFloat
  , qiSimplify
  , qiAddR, qiSubR, qiMulR, qiDivR
  , qiNegate, qiRecip, qiAdd, qiSub, qiMul, qiDiv, qiPow
  , qiFloor, qiToContinuedFraction
  , module Numeric.QuadraticIrrational.CyclicList
  ) where

import Control.Applicative ((<$))
import Control.Arrow (first)
import Control.Monad.State
import Data.List
import Data.Ratio
import qualified Data.Set as Set
import Math.NumberTheory.Powers.Squares
import Math.NumberTheory.Primes.Factorisation

import Numeric.QuadraticIrrational.CyclicList

-- | @a + b √c@
data QI = QI !Rational  -- ^ a
             !Rational  -- ^ b
             !Integer   -- ^ c
  deriving (Show, Read)

type QITuple = (Rational, Rational, Integer)

-- | Given @a@, @b@ and @c@ such that @n = a + b √c@, constuct a 'QI'
-- corresponding to @n@.
qi :: Rational  -- ^ a
   -> Rational  -- ^ b
   -> Integer   -- ^ c
   -> QI
qi a 0 _ = QI a 0 0
qi a _ 0 = QI a 0 0
qi a b 1 = QI (a + b) 0 0
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
runQI :: QI -> (Rational -> Rational -> Integer -> a) -> a
runQI (QI a b c) f = f a b c

-- | Given @n@ and @f@ such that @n = (a + b √c)/d@, run @f a b c d@.
runQI' :: QI -> (Integer -> Integer -> Integer -> Integer -> a) -> a
runQI' (unQI -> ~(a,b,c)) f = f a' b' c d'
  where
    -- aN/aD + bN/bD = (aN bD + bN aD) / (aD bD)
    a' = aN * bD
    b' = bN * aD
    d' = aD * bD
    (aN, aD) = (numerator a, denominator a)
    (bN, bD) = (numerator b, denominator b)

-- | Given @n@ such that @n = a + b √c@, return @(a, b, c)@.
unQI :: QI -> (Rational, Rational, Integer)
unQI n = runQI n (,,)

-- | Given @n@ such that @n = (a + b √c)/d@, return @(a, b, c, d)@.
unQI' :: QI -> (Integer, Integer, Integer, Integer)
unQI' n = runQI' n (,,,)

qiToFloat :: Floating a => QI -> a
qiToFloat (unQI -> ~(a,b,c)) =
  fromRational a + fromRational b * sqrt (fromInteger c)

-- | Change a 'QI' to a potentially simpler form. Will factorize the number
-- inside the square root internally.
qiSimplify :: QI -> QI
qiSimplify (unQI -> ~(a,b,c))
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

qiAddR :: Real a => QI -> a -> QI
qiAddR (unQI -> ~(a,b,c)) (toRational -> x) = qi (a+x) b c

qiSubR :: Real a => QI -> a -> QI
qiSubR n (toRational -> x) = qiAddR n (negate x)

qiMulR :: Real a => QI -> a -> QI
qiMulR (unQI -> ~(a,b,c)) (toRational -> x) = qi (a*x) (b*x) c

qiDivR :: (Show a, Real a) => QI -> a -> QI
qiDivR n (toRational . nonZero "qiDiv" -> x) = qiMulR n (recip x)

qiNegate :: QI -> QI
qiNegate n = qiMulR n (-1 :: Rational)

qiRecip :: QI -> Maybe QI
qiRecip (unQI' -> ~(a,b,c,d)) =
  -- 1/((a + b √c)/d)                       =
  -- d/(a + b √c)                           =
  -- d (a − b √c) / ((a + b √c) (a − b √c)) =
  -- d (a − b √c) / (a² − b² c)             =
  -- a d − b d √c / (a² − b² c)
  qi' (a * d) (negate (b * d)) c denom <$ guard (denom /= 0)
  where denom = (a*a - b*b * toInteger c)

-- | Add two 'QI's if the square root terms are the same or zeros.
qiAdd :: QI -> QI -> Maybe QI
qiAdd (unQI -> ~(a,b,c)) (unQI -> ~(a',b',c'))
  | c  == 0   = Just (qi (a + a') b'       c')
  | c' == 0   = Just (qi (a + a') b        c)
  | c  == c'  = Just (qi (a + a') (b + b') c)
                -- a + b √c + a' + b' √c =
                -- (a + a') + (b + b') √c
  | otherwise = Nothing

-- | Subtract two 'QI's if the square root terms are the same or zeros.
qiSub :: QI -> QI -> Maybe QI
qiSub n n' = qiAdd n (qiNegate n')

-- | Multiply two 'QI's if the square root terms are the same or zeros.
qiMul :: QI -> QI -> Maybe QI
qiMul n@(unQI -> ~(a,b,c)) n'@(unQI -> ~(a',b',c'))
  | c  == 0   = Just (qiMulR n' a)
  | c' == 0   = Just (qiMulR n  a')
  | c  == c'  = Just (qi (a*a' + b*b'*fromInteger c) (a*b' + a'*b) c)
                -- (a + b √c) (a' + b' √c)           =
                -- a a' + a b' √c + a' b √c + b b' c =
                -- (a a' + b b' c) + (a b' + a' b) √c
  | otherwise = Nothing

-- | Divide two 'QI's if the square root terms are the same or zeros.
qiDiv :: QI -> QI -> Maybe QI
qiDiv n n' = qiMul n =<< qiRecip n'

qiPow :: QI -> Integer -> QI
qiPow num (nonNegative "qiPow" -> pow) = go num pow
  where
    go _ 0 = qi 1 0 0
    go n 1 = n
    go n p
      | even p    = go  (sudoQIMul n n) (p     `div` 2)
      | otherwise = go' (sudoQIMul n n) ((p-1) `div` 2) n

    -- Like go but multiplied with n'.
    go' _ 0 n' = n'
    go' n 1 n' = sudoQIMul n n'
    go' n p n'
      | even p    = go' (sudoQIMul n n) (p     `div` 2) n'
      | otherwise = go' (sudoQIMul n n) ((p-1) `div` 2) (sudoQIMul n n')

    -- Multiplying a QI with its own power will always succeed.
    sudoQIMul n n' = case qiMul n n' of ~(Just m) -> m

qiFloor :: QI -> Integer
qiFloor (unQI' -> ~(a,b,c,d)) =
  -- n = (a + b √c)/d
  -- n d = a + b √c
  -- n d = a + signum b · √(b² c)
  n_d `div` d
  where
    n_d = a + min (signum b * b2cLow) (signum b * b2cHigh)

    ~(b2cLow, b2cHigh) = iSqrtBounds (b*b * c)

-- Convert a 'QI' into a periodic continued fraction representation.
qiToContinuedFraction :: QI
                      -> (Integer, CycList Integer)
qiToContinuedFraction num
  | Just isLoopQI <- loopQI =
      case break isLoopQI cfs of
        (preLoop, ~(i:postLoop)) ->
          let is = takeWhile (not . isLoopQI) postLoop
          in  (i0, Cyc (map snd preLoop) (snd i) (map snd is))
  | otherwise =
      (i0, NonCyc (map snd cfs))
  where
    (i0, cfs) = qiToContinuedFractionList num

    loopQI :: Maybe ((QITuple,a) -> Bool)
    loopQI = evalState (go cfs) Set.empty
      where
        go ((n,_) : xs) = do
          haveSeen <- gets (Set.member n)
          modify (Set.insert n)
          if haveSeen
            then return (Just ((== n) . fst))
            else go xs
        go [] = return Nothing

qiToContinuedFractionList :: QI -> (Integer, [(QITuple, Integer)])
qiToContinuedFractionList num =
  case go (Just num) of
    -- There is always a first number.
    ~((_,i) : xs) -> (i, xs)
  where
    go (Just n) = (unQI n, i) : go (qiRecip (qiSubR n i))
      where i = qiFloor n
    go Nothing  = []

iSqrtBounds :: Integer -> (Integer, Integer)
iSqrtBounds n = (low, high)
  where
    low = integerSquareRoot n
    high | low*low == n = low
         | otherwise    = low + 1

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
