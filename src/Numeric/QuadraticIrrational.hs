{-# LANGUAGE ViewPatterns #-}

-- |
-- Module      : Numeric.QuadraticIrrational
-- Description : An implementation of quadratic irrationals
-- Copyright   : © 2014 Johan Kiviniemi
-- License     : MIT
-- Maintainer  : Johan Kiviniemi <devel@johan.kiviniemi.name>
-- Stability   : provisional
-- Portability : ViewPatterns
--
-- A library for exact computation with
-- <http://en.wikipedia.org/wiki/Quadratic_irrational quadratic irrationals>
-- with support for exact conversion from and to
-- <http://en.wikipedia.org/wiki/Periodic_continued_fraction (potentially periodic) simple continued fractions>.
--
-- A quadratic irrational is a number that can be expressed in the form
--
-- > (a + b √c) / d
--
-- where @a@, @b@ and @d@ are integers and @c@ is a square-free natural number.
--
-- Some examples of such numbers are
--
-- * @7/2@,
--
-- * @√2@,
--
-- * @(1 + √5)\/2@
--   (<http://en.wikipedia.org/wiki/Golden_ratio the golden ratio>),
--
-- * solutions to quadratic equations with rational constants – the
--   <http://en.wikipedia.org/wiki/Quadratic_formula quadratic formula> has a
--   familiar shape.
--
-- A simple continued fraction is a number expressed in the form
--
-- > a + 1/(b + 1/(c + 1/(d + 1/(e + …))))
--
-- or alternatively written as
--
-- > [a; b, c, d, e, …]
--
-- where @a@ is an integer and @b@, @c@, @d@, @e@, … are positive integers.
--
-- Every finite SCF represents a rational number and every infinite, periodic
-- SCF represents a quadratic irrational.
--
-- > 3.5      = [3; 2]
-- > (1+√5)/2 = [1; 1, 1, 1, …]
-- > √2       = [1; 2, 2, 2, …]

module Numeric.QuadraticIrrational
  ( -- * Constructors and deconstructors
    QI, qi, qi', runQI, runQI', unQI, unQI'
  , -- * Lenses
    _qi, _qi', _qiABD, _qiA, _qiB, _qiC, _qiD
  , -- * Numerical operations
    qiZero, qiOne, qiIsZero
  , qiToFloat
  , qiAddI, qiSubI, qiMulI, qiDivI
  , qiAddR, qiSubR, qiMulR, qiDivR
  , qiNegate, qiRecip, qiAdd, qiSub, qiMul, qiDiv, qiPow
  , qiFloor
  , -- * Continued fractions
    continuedFractionToQI, qiToContinuedFraction
  , continuedFractionApproximate
  , module Numeric.QuadraticIrrational.CyclicList
  ) where

import Control.Applicative
import Control.Monad.State
import qualified Data.Foldable as F
import Data.List
import Data.Maybe
import Data.Ratio
import qualified Data.Set as Set
import Math.NumberTheory.Powers.Squares
import Math.NumberTheory.Primes.Factorisation
import Text.Read

import Numeric.QuadraticIrrational.CyclicList
import Numeric.QuadraticIrrational.Internal.Lens

-- $setup
-- >>> import Data.Number.CReal

-- | @(a + b √c) \/ d@
data QI = QI !Integer
             !Integer
             !Integer
             !Integer
  deriving (Eq)

instance Show QI where
  showsPrec p (QI a b c d) = showParen (p > 10)
                           $ showString "qi " . showsPrec 11 a
                           . showChar   ' '   . showsPrec 11 b
                           . showChar   ' '   . showsPrec 11 c
                           . showChar   ' '   . showsPrec 11 d

instance Read QI where
  readPrec = parens rQI
    where
      rQI = prec 10 $ do
        Ident "qi" <- lexP
        qi <$> step readPrec <*> step readPrec <*> step readPrec
           <*> step readPrec

  readListPrec = readListPrecDefault

type QITuple = (Integer, Integer, Integer, Integer)

-- | Given @a@, @b@, @c@ and @d@ such that @n = (a + b √c)\/d@, constuct a 'QI'
-- corresponding to @n@.
--
-- >>> qi 3 4 5 6
-- qi 3 4 5 6
--
-- The fractions are reduced:
--
-- >>> qi 30 40 5 60
-- qi 3 4 5 6
--
-- If @b = 0@ then @c@ is zeroed and vice versa:
--
-- >>> qi 3 0 42 1
-- qi 3 0 0 1
--
-- >>> qi 3 42 0 1
-- qi 3 0 0 1
--
-- The @b √c@ term is simplified:
--
-- >>> qi 0 1 (5*5*6) 1
-- qi 0 5 6 1
--
-- If @c = 1@ (after simplification) then @b@ is moved to @a@:
--
-- >>> qi 1 5 (2*2) 1
-- qi 11 0 0 1
qi :: Integer  -- ^ a
   -> Integer  -- ^ b
   -> Integer  -- ^ c
   -> Integer  -- ^ d
   -> QI
qi a b (nonNegative "qi" -> c) (nonZero "qi" -> d)
  | b == 0    = reduceCons a 0 0 d
  | c == 0    = reduceCons a 0 0 d
  | c == 1    = reduceCons (a + b) 0 0 d
  | otherwise = simplifyReduceCons a b c d
{-# INLINE qi #-}

-- Construct a 'QI' without simplifying @b √c@. Make sure it has already been
-- simplified.
qiNoSimpl :: Integer -> Integer -> Integer -> Integer -> QI
qiNoSimpl a b (nonNegative "qiNoSimpl" -> c) (nonZero "qiNoSimpl" -> d)
  | b == 0    = reduceCons a 0 0 d
  | c == 0    = reduceCons a 0 0 d
  | c == 1    = reduceCons (a + b) 0 0 d
  | otherwise = reduceCons a b c d
{-# INLINE qiNoSimpl #-}

-- Simplify @b √c@ before constructing a 'QI'.
simplifyReduceCons :: Integer -> Integer -> Integer -> Integer -> QI
simplifyReduceCons a b (nonZero "simplifyReduceCons" -> c) d
  | c' == 1   = reduceCons (a + b') 0 0 d
  | otherwise = reduceCons a b' c' d
  where ~(b', c') = separateSquareFactors b c
{-# INLINE simplifyReduceCons #-}

-- | Given @b@ and @c@ such that @n = b √c@, return a potentially simplified
-- @(b, c)@.
separateSquareFactors :: Integer -> Integer -> (Integer, Integer)
separateSquareFactors b (nonNegative "separateSquareFactors" -> c) =
  case foldl' go (1,1) (factorise c) of
    ~(bMul, c') -> (b*bMul, c')
  where
    go :: (Integer, Integer) -> (Integer, Int) -> (Integer, Integer)
    go ~(i, j) ~(fac, pow) =
      i `seq` j `seq` fac `seq` pow `seq`
        if even pow
          then (i*fac^(pow     `div` 2), j)
          else (i*fac^((pow-1) `div` 2), j*fac)

-- Reduce the @a@, @b@, @d@ factors before constructing a 'QI'.
reduceCons :: Integer -> Integer -> Integer -> Integer -> QI
reduceCons a b c (nonZero "reduceCons" -> d) =
  QI (a `quot` q) (b `quot` q) c (d `quot` q)
  where q = signum d * (a `gcd` b `gcd` d)
{-# INLINE reduceCons #-}

-- | Given @a@, @b@ and @c@ such that @n = a + b √c@, constuct a 'QI'
-- corresponding to @n@.
--
-- >>> qi' 0.5 0.7 2
-- qi 5 7 2 10
qi' :: Rational  -- ^ a
    -> Rational  -- ^ b
    -> Integer   -- ^ c
    -> QI
qi' a b (nonNegative "qi'" -> c) = n
  where
    -- (aN/aD) + (bN/bD) √c = ((aN bD) + (bN aD) √c) / (aD bD)
    n = qi (aN*bD) (bN*aD) c (aD*bD)
    (aN, aD) = (numerator a, denominator a)
    (bN, bD) = (numerator b, denominator b)
{-# INLINE qi' #-}

-- | Given @n@ and @f@ such that @n = (a + b √c)\/d@, run @f a b c d@.
--
-- >>> runQI (qi 3 4 5 6) (\a b c d -> (a,b,c,d))
-- (3,4,5,6)
runQI :: QI -> (Integer -> Integer -> Integer -> Integer -> a) -> a
runQI (QI a b c d) f = f a b c d
{-# INLINE runQI #-}

-- | Given @n@ and @f@ such that @n = a + b √c@, run @f a b c@.
--
-- >>> runQI' (qi' 0.5 0.7 2) (\a b c -> (a, b, c))
-- (1 % 2,7 % 10,2)
runQI' :: QI -> (Rational -> Rational -> Integer -> a) -> a
runQI' (QI a b c d) f = f (a % d) (b % d) c
{-# INLINE runQI' #-}

-- | Given @n@ such that @n = (a + b √c)\/d@, return @(a, b, c, d)@.
--
-- >>> unQI (qi 3 4 5 6)
-- (3,4,5,6)
unQI :: QI -> (Integer, Integer, Integer, Integer)
unQI n = runQI n (,,,)
{-# INLINE unQI #-}

-- | Given @n@ such that @n = a + b √c@, return @(a, b, c)@.
--
-- >>> unQI' (qi' 0.5 0.7 2)
-- (1 % 2,7 % 10,2)
unQI' :: QI -> (Rational, Rational, Integer)
unQI' n = runQI' n (,,)
{-# INLINE unQI' #-}

-- | Given a 'QI' corresponding to @n = (a + b √c)\/d@, access @(a, b, c, d)@.
--
-- >>> view _qi (qi 3 4 5 6)
-- (3,4,5,6)
--
-- >>> over _qi (\(a,b,c,d) -> (a+10, b+10, c+10, d+10)) (qi 3 4 5 6)
-- qi 13 14 15 16
_qi :: Lens' QI (Integer, Integer, Integer, Integer)
_qi f n = (\ ~(a',b',c',d') -> qi a' b' c' d') <$> f (unQI n)
{-# INLINE _qi #-}

-- | Given a 'QI' corresponding to @n = a + b √c@, access @(a, b, c)@.
--
-- >>> view _qi' (qi' 0.5 0.7 2)
-- (1 % 2,7 % 10,2)
--
-- >>> over _qi' (\(a,b,c) -> (a/5, b/6, c*3)) (qi 3 4 5 6)
-- qi 9 10 15 90
_qi' :: Lens' QI (Rational, Rational, Integer)
_qi' f n = (\ ~(a',b',c') -> qi' a' b' c') <$> f (unQI' n)
{-# INLINE _qi' #-}

-- | Given a 'QI' corresponding to @n = (a + b √c)\/d@, access @(a, b, d)@.
-- Avoids having to simplify @b √c@ upon reconstruction.
--
-- >>> view _qiABD (qi 3 4 5 6)
-- (3,4,6)
--
-- >>> over _qiABD (\(a,b,d) -> (a+10, b+10, d+10)) (qi 3 4 5 6)
-- qi 13 14 5 16
_qiABD :: Lens' QI (Integer, Integer, Integer)
_qiABD f (unQI -> ~(a,b,c,d)) =
  (\ ~(a',b',d') -> qiNoSimpl a' b' c d') <$> f (a,b,d)
{-# INLINE _qiABD #-}

-- | Given a 'QI' corresponding to @n = (a + b √c)\/d@, access @a@. It is more
-- efficient to use '_qi' or '_qiABD' when modifying multiple terms at once.
--
-- >>> view _qiA (qi 3 4 5 6)
-- 3
--
-- >>> over _qiA (+ 10) (qi 3 4 5 6)
-- qi 13 4 5 6
_qiA :: Lens' QI Integer
_qiA = _qiABD . go
  where go f ~(a,b,d) = (\a' -> (a',b,d)) <$> f a

-- | Given a 'QI' corresponding to @n = (a + b √c)\/d@, access @b@. It is more
-- efficient to use '_qi' or '_qiABD' when modifying multiple terms at once.
--
-- >>> view _qiB (qi 3 4 5 6)
-- 4
--
-- >>> over _qiB (+ 10) (qi 3 4 5 6)
-- qi 3 14 5 6
_qiB :: Lens' QI Integer
_qiB = _qiABD . go
  where go f ~(a,b,d) = (\b' -> (a,b',d)) <$> f b

-- | Given a 'QI' corresponding to @n = (a + b √c)\/d@, access @c@. It is more
-- efficient to use '_qi' or '_qiABD' when modifying multiple terms at once.
--
-- >>> view _qiC (qi 3 4 5 6)
-- 5
--
-- >>> over _qiC (+ 10) (qi 3 4 5 6)
-- qi 3 4 15 6
_qiC :: Lens' QI Integer
_qiC = _qi . go
  where go f ~(a,b,c,d) = (\c' -> (a,b,c',d)) <$> f c

-- | Given a 'QI' corresponding to @n = (a + b √c)\/d@, access @d@. It is more
-- efficient to use '_qi' or '_qiABD' when modifying multiple terms at once.
--
-- >>> view _qiD (qi 3 4 5 6)
-- 6
--
-- >>> over _qiD (+ 10) (qi 3 4 5 6)
-- qi 3 4 5 16
_qiD :: Lens' QI Integer
_qiD = _qiABD . go
  where go f ~(a,b,d) = (\d' -> (a,b,d')) <$> f d

-- | The constant zero.
--
-- >>> qiZero
-- qi 0 0 0 1
qiZero :: QI
qiZero = qi 0 0 0 1
{-# INLINE qiZero #-}

-- | The constant one.
--
-- >>> qiOne
-- qi 1 0 0 1
qiOne :: QI
qiOne  = qi 1 0 0 1
{-# INLINE qiOne #-}

-- | Check if the value is zero.
--
-- >>> map qiIsZero [qiZero, qiOne, qiSubR (qi 7 0 0 2) 3.5]
-- [True,False,True]
qiIsZero :: QI -> Bool
-- If b = 0 then c = 0 and vice versa, guaranteed by the constructor.
qiIsZero (unQI -> ~(a,b,_,_)) = a == 0 && b == 0
{-# INLINE qiIsZero #-}

-- | Convert a 'QI' number into a 'Floating' one.
--
-- >>> qiToFloat (qi 3 4 5 6) == ((3 + 4 * sqrt 5)/6 :: Double)
-- True
qiToFloat :: Floating a => QI -> a
qiToFloat (unQI -> ~(a,b,c,d)) =
  (fromInteger a + fromInteger b * sqrt (fromInteger c)) / fromInteger d
{-# INLINE qiToFloat #-}

-- | Add an 'Integer' to a 'QI'.
--
-- >>> qi 3 4 5 6 `qiAddI` 1
-- qi 9 4 5 6
qiAddI :: QI -> Integer -> QI
qiAddI n x = over _qiABD go n
  where go ~(a,b,d) = a `seq` b `seq` d `seq` x `seq` (a + d*x, b, d)
{-# INLINE qiAddI #-}

-- | Add a 'Rational' to a 'QI'.
--
-- >>> qi 3 4 5 6 `qiAddR` 1.2
-- qi 51 20 5 30
qiAddR :: QI -> Rational -> QI
qiAddR n x = over _qiABD go n
  where
    -- n = (a + b √c)/d + xN/xD
    -- n = ((a + b √c) xD)/(d xD) + (d xN)/(d xD)
    -- n = ((a xD + d xN) + b xD √c)/(d xD)
    go ~(a,b,d) =
      a `seq` b `seq` d `seq` xN `seq` xD `seq` (a*xD + d*xN, b*xD, d*xD)
    (xN, xD) = (numerator x, denominator x)
{-# INLINE qiAddR #-}

-- | Subtract an 'Integer' from a 'QI'.
--
-- >>> qi 3 4 5 6 `qiSubI` 1
-- qi (-3) 4 5 6
qiSubI :: QI -> Integer -> QI
qiSubI n x = qiAddI n (negate x)
{-# INLINE qiSubI #-}

-- | Subtract a 'Rational' from a 'QI'.
--
-- >>> qi 3 4 5 6 `qiSubR` 1.2
-- qi (-21) 20 5 30
qiSubR :: QI -> Rational -> QI
qiSubR n x = qiAddR n (negate x)
{-# INLINE qiSubR #-}

-- | Multiply a 'QI' by an 'Integer'.
--
-- >>> qi 3 4 5 6 `qiMulI` 2
-- qi 3 4 5 3
qiMulI :: QI -> Integer -> QI
qiMulI n x = over _qiABD go n
  where go ~(a,b,d) = a `seq` b `seq` d `seq` x `seq` (a*x, b*x, d)
{-# INLINE qiMulI #-}

-- | Multiply a 'QI' by a 'Rational'.
--
-- >>> qi 3 4 5 6 `qiMulR` 0.5
-- qi 3 4 5 12
qiMulR :: QI -> Rational -> QI
qiMulR n x = over _qiABD go n
  where
    -- n = (a + b √c)/d xN/xD
    -- n = (a xN + b xN √c)/(d xD)
    go ~(a,b,d) = a `seq` b `seq` d `seq` xN `seq` xD `seq` (a*xN, b*xN, d*xD)
    (xN, xD) = (numerator x, denominator x)
{-# INLINE qiMulR #-}

-- | Divice a 'QI' by an 'Integer'.
--
-- >>> qi 3 4 5 6 `qiDivI` 2
-- qi 3 4 5 12
qiDivI :: QI -> Integer -> QI
qiDivI n (nonZero "qiDivI" -> x) = over _qiABD go n
  where go ~(a,b,d) = a `seq` b `seq` d `seq` x `seq` (a, b, d*x)
{-# INLINE qiDivI #-}

-- | Divice a 'QI' by a 'Rational'.
--
-- >>> qi 3 4 5 6 `qiDivR` 0.5
-- qi 3 4 5 3
qiDivR :: QI -> Rational -> QI
qiDivR n (nonZero "qiDivR" -> x) = qiMulR n (recip x)
{-# INLINE qiDivR #-}

-- | Negate a 'QI'.
--
-- >>> qiNegate (qi 3 4 5 6)
-- qi (-3) (-4) 5 6
qiNegate :: QI -> QI
qiNegate n = over _qiABD go n
  where go ~(a,b,d) = a `seq` b `seq` d `seq` (negate a, negate b, d)
{-# INLINE qiNegate #-}

-- | Compute the reciprocal of a 'QI'.
--
-- >>> qiRecip (qi 5 0 0 2)
-- Just (qi 2 0 0 5)
--
-- >>> qiRecip (qi 0 1 5 2)
-- Just (qi 0 2 5 5)
--
-- >>> qiRecip qiZero
-- Nothing
qiRecip :: QI -> Maybe QI
qiRecip n@(unQI -> ~(a,b,c,d))
  -- 1/((a + b √c)/d)                       =
  -- d/(a + b √c)                           =
  -- d (a − b √c) / ((a + b √c) (a − b √c)) =
  -- d (a − b √c) / (a² − b² c)             =
  -- (a d − b d √c) / (a² − b² c)
  | qiIsZero n = Nothing
  | denom == 0 = error ("qiRecip: Failed for " ++ show n)
  | otherwise  = Just (set _qiABD (a * d, negate (b * d), denom) n)
  where denom = (a*a - b*b * c)

-- | Add two 'QI's if the square root terms are the same or zeros.
--
-- >>> qi 3 4 5 6 `qiAdd` qiOne
-- Just (qi 9 4 5 6)
--
-- >>> qi 3 4 5 6 `qiAdd` qi 3 4 5 6
-- Just (qi 3 4 5 3)
--
-- >>> qi 0 1 5 1 `qiAdd` qi 0 1 6 1
-- Nothing
qiAdd :: QI -> QI -> Maybe QI
qiAdd n@(unQI -> ~(a,b,c,d)) n'@(unQI -> ~(a',b',c',d'))
  -- n = (a + b √c)/d + (a' + b' √c')/d'
  -- n = ((a + b √c) d' + (a' + b' √c') d)/(d d')
  -- if c = c' then n = ((a d' + a' d) + (b d' + b' d) √c)/(d d')
  | c  == 0   = Just (set _qiABD (a*d' + a'*d,        b'*d, d*d') n')
  | c' == 0   = Just (set _qiABD (a*d' + a'*d, b*d'       , d*d') n)
  | c  == c'  = Just (set _qiABD (a*d' + a'*d, b*d' + b'*d, d*d') n)
  | otherwise = Nothing

-- | Subtract two 'QI's if the square root terms are the same or zeros.
--
-- >>> qi 3 4 5 6 `qiSub` qiOne
-- Just (qi (-3) 4 5 6)
--
-- >>> qi 3 4 5 6 `qiSub` qi 3 4 5 6
-- Just (qi 0 0 0 1)
--
-- >>> qi 0 1 5 1 `qiSub` qi 0 1 6 1
-- Nothing
qiSub :: QI -> QI -> Maybe QI
qiSub n n' = qiAdd n (qiNegate n')

-- | Multiply two 'QI's if the square root terms are the same or zeros.
--
-- >>> qi 3 4 5 6 `qiMul` qiZero
-- Just (qi 0 0 0 1)
--
-- >>> qi 3 4 5 6 `qiMul` qiOne
-- Just (qi 3 4 5 6)
--
-- >>> qi 3 4 5 6 `qiMul` qi 3 4 5 6
-- Just (qi 89 24 5 36)
--
-- >>> qi 0 1 5 1 `qiMul` qi 0 1 6 1
-- Nothing
qiMul :: QI -> QI -> Maybe QI
qiMul n@(unQI -> ~(a,b,c,d)) n'@(unQI -> ~(a',b',c',d'))
  -- n = (a + b √c)/d (a' + b' √c')/d'
  -- n = (a a' + a b' √c' + a' b √c + b b' √c √c')/(d d')
  -- if c = 0  then n = (a a' + a b' √c')/(d d')
  -- if c' = 0 then n = (a a' + a' b √c)/(d d')
  -- if c = c' then n = ((a a' + b b' c) + (a b' + a' b) √c)/(d d')
  | c  == 0   = Just (set _qiABD (a*a'         , a*b'       , d*d') n')
  | c' == 0   = Just (set _qiABD (a*a'         ,        a'*b, d*d') n)
  | c  == c'  = Just (set _qiABD (a*a' + b*b'*c, a*b' + a'*b, d*d') n)
  | otherwise = Nothing

-- | Divide two 'QI's if the square root terms are the same or zeros.
--
-- >>> qi 3 4 5 6 `qiDiv` qiZero
-- Nothing
--
-- >>> qi 3 4 5 6 `qiDiv` qiOne
-- Just (qi 3 4 5 6)
--
-- >>> qi 3 4 5 6 `qiDiv` qi 3 4 5 6
-- Just (qi 1 0 0 1)
--
-- >>> qi 3 4 5 6 `qiDiv` qi 0 1 5 1
-- Just (qi 20 3 5 30)
--
-- >>> qi 0 1 5 1 `qiDiv` qi 0 1 6 1
-- Nothing
qiDiv :: QI -> QI -> Maybe QI
qiDiv n n' = qiMul n =<< qiRecip n'

-- | Exponentiate a 'QI' to an 'Integer' power.
--
-- >>> qi 3 4 5 6 `qiPow` 0
-- qi 1 0 0 1
--
-- >>> qi 3 4 5 6 `qiPow` 1
-- qi 3 4 5 6
--
-- >>> qi 3 4 5 6 `qiPow` 2
-- qi 89 24 5 36
qiPow :: QI -> Integer -> QI
qiPow num (nonNegative "qiPow" -> pow) = go num pow
  where
    go _ 0 = qiOne
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

-- | Compute the floor of a 'QI'.
--
-- >>> qiFloor (qi 10 0 0 2)
-- 5
--
-- >>> qiFloor (qi 10 2 2 2)
-- 6
--
-- >>> qiFloor (qi 10 2 5 2)
-- 7
qiFloor :: QI -> Integer
qiFloor (unQI -> ~(a,b,c,d)) =
  -- n = (a + b √c)/d
  -- n d = a + b √c
  -- n d = a + signum b · √(b² c)
  n_d `div` d
  where
    n_d = a + min (signum b * b2cLow) (signum b * b2cHigh)

    ~(b2cLow, b2cHigh) = iSqrtBounds (b*b * c)

-- | Convert a (possibly periodic) continued fraction to a 'QI'.
--
-- @[2; 2] = 2 + 1\/2 = 5\/2@.
--
-- >>> continuedFractionToQI (2,NonCyc [2])
-- qi 5 0 0 2
--
-- The golden ratio is @[1; 1, 1, …]@.
--
-- >>> showCReal 1000 (qiToFloat (continuedFractionToQI (1,Cyc [] 1 [])))
-- "1.6180339887498948482045868343656381177203091798057628621354486227052604628189024497072072041893911374847540880753868917521266338622235369317931800607667263544333890865959395829056383226613199282902678806752087668925017116962070322210432162695486262963136144381497587012203408058879544547492461856953648644492410443207713449470495658467885098743394422125448770664780915884607499887124007652170575179788341662562494075890697040002812104276217711177780531531714101170466659914669798731761356006708748071013179523689427521948435305678300228785699782977834784587822891109762500302696156170025046433824377648610283831268330372429267526311653392473167111211588186385133162038400522216579128667529465490681131715993432359734949850904094762132229810172610705961164562990981629055520852479035240602017279974717534277759277862561943208275051312181562855122248093947123414517022373580577278616008688382952304592647878017889921990270776903895321968198615143780314997411069260886742962267575605231727775203536139362"
--
-- >>> continuedFractionToQI (0,Cyc [83,78,65,75,69] 32 [66,65,68,71,69,82])
-- qi 987601513930253257378987883 1 14116473325908285531353005 81983584717737887813195873886
continuedFractionToQI :: (Integer, CycList Integer) -> QI
continuedFractionToQI (i0_, is_) = qiAddI (go is_) i0_
  where
    go (NonCyc as)   = goNonCyc as qiZero
    go (Cyc as b bs) = goNonCyc as (goCyc (b:bs))

    goNonCyc ((pos -> i):is) final = sudoQIRecip (qiAddI (goNonCyc is final) i)
    goNonCyc []              final = final

    goCyc is = sudoQIRecip (solvePeriodic is)

    -- x = (a x + b) / (c x + d)
    -- x (c x + d) = a x + b
    -- c x² + d x = a x + b
    -- c x² + (d − a) x − b = 0
    -- Apply quadratic formula, positive solution only.
    solvePeriodic is =
      case solvePeriodic' is of
        ~(a,b,c,d) ->
          a `seq` b `seq` c `seq` d `seq`
            qfPos c (d - a) (negate b)
      where
        qfPos i j k = qi (negate j) 1 (j*j - 4*i*k) (2*i)

    -- i + 1/((a x + b) / (c x + d))      =
    -- i + (c x + d)/(a x + b)            =
    -- ((a i x + b i + c x + d)/(a x + b) =
    -- ((a i + c) x + (b i + d))/(a x + b)
    solvePeriodic' ((pos -> i):is) =
      case solvePeriodic' is of
        ~(a,b,c,d) ->
          a `seq` b `seq` c `seq` d `seq` i `seq`
            (a*i+c, b*i+d, a, b)

    -- x = (1 x + 0) / (0 x + 1)
    solvePeriodic' [] = (1,0,0,1)

    sudoQIRecip n =
      fromMaybe (error "continuedFractionToQI: Divide by zero") (qiRecip n)

    pos = positive "continuedFractionToQI"

-- | Convert a 'QI' into a (possibly periodic) continued fraction.
--
-- @5\/2 = 2 + 1\/2 = [2; 2]@.
--
-- >>> qiToContinuedFraction (qi 5 0 0 2)
-- (2,NonCyc [2])
--
-- The golden ratio is @(1 + √5)\/2@. We can compute the corresponding PCF.
--
-- >>> qiToContinuedFraction (qi 1 1 5 2)
-- (1,Cyc [] 1 [])
--
-- >>> qiToContinuedFraction (qi 987601513930253257378987883 1 14116473325908285531353005 81983584717737887813195873886)
-- (0,Cyc [83,78,65,75,69] 32 [66,65,68,71,69,82])
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
    go (Just n) = (unQI n, i) : go (qiRecip (qiSubI n i))
      where i = qiFloor n
    go Nothing  = []

-- | Compute a rational partial evaluation of a continued fraction.
--
-- Rational approximations that converge toward φ:
--
-- >>> [ continuedFractionApproximate n (1, repeat 1) | n <- [0,3..18] ]
-- [1 % 1,5 % 3,21 % 13,89 % 55,377 % 233,1597 % 987,6765 % 4181]
continuedFractionApproximate :: F.Foldable f
                             => Int -> (Integer, f Integer) -> Rational
continuedFractionApproximate n (i0, F.toList -> is) =
  fromInteger i0 +
    foldr (\(pos -> i) r -> recip (fromInteger i + r)) 0 (take n is)
  where
    pos = positive "continuedFractionApproximate"

iSqrtBounds :: Integer -> (Integer, Integer)
iSqrtBounds n = (low, high)
  where
    low = integerSquareRoot n
    high | low*low == n = low
         | otherwise    = low + 1

nonNegative :: (Num a, Ord a, Show a) => String -> a -> a
nonNegative name = validate name "non-negative" (>= 0)
{-# INLINE nonNegative #-}

positive :: (Num a, Ord a, Show a) => String -> a -> a
positive name = validate name "positive" (> 0)
{-# INLINE positive #-}

nonZero :: (Num a, Eq a, Show a) => String -> a -> a
nonZero name = validate name "non-zero" (/= 0)
{-# INLINE nonZero #-}

validate :: Show a => String -> String -> (a -> Bool) -> a -> a
validate name expected f a
  | f a = a
  | otherwise =
      error ("Numeric.QuadraticIrrational." ++ name ++ ": Got " ++ show a
              ++ ", expected " ++ expected)
{-# INLINE validate #-}
