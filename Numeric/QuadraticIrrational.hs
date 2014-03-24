{-# LANGUAGE ViewPatterns #-}

module Numeric.QuadraticIrrational
  ( QI, qi, qi', qiModify, runQI, runQI', unQI, unQI'
  , qiZero, qiOne, qiIsZero
  , qiToFloat
  , qiAddR, qiSubR, qiMulR, qiDivR
  , qiNegate, qiRecip, qiAdd, qiSub, qiMul, qiDiv, qiPow
  , qiFloor, continuedFractionToQI, qiToContinuedFraction
  , module Numeric.QuadraticIrrational.CyclicList
  ) where

import Control.Applicative
import Control.Monad.State
import Data.List
import Data.Maybe
import Data.Ratio
import qualified Data.Set as Set
import Math.NumberTheory.Powers.Squares
import Math.NumberTheory.Primes.Factorisation
import Text.Read

import Numeric.QuadraticIrrational.CyclicList

-- | @(a + b √c) / d@
data QI = QI !Integer  -- ^ a
             !Integer  -- ^ b
             !Integer  -- ^ c
             !Integer  -- ^ d

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

-- | Given @a@, @b@, @c@ and @d@ such that @n = (a + b √c)/d@, constuct a 'QI'
-- corresponding to @n@.
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

-- | Given a 'QI' corresponding to @n = (a + b √c)/d@, modify @(a, b, d)@.
-- Avoids having to simplify @b √c@.
qiModify :: QI
         -> (Integer -> Integer -> Integer -> (Integer, Integer, Integer))
         -> QI
qiModify (QI a b c d) f = reduceCons a' b' c d'
  where (a', b', d') = f a b d
{-# INLINE qiModify #-}

-- | Given @n@ and @f@ such that @n = (a + b √c)/d@, run @f a b c d@.
runQI :: QI -> (Integer -> Integer -> Integer -> Integer -> a) -> a
runQI (QI a b c d) f = f a b c d
{-# INLINE runQI #-}

-- | Given @n@ and @f@ such that @n = a + b √c@, run @f a b c@.
runQI' :: QI -> (Rational -> Rational -> Integer -> a) -> a
runQI' (QI a b c d) f = f (a % d) (b % d) c
{-# INLINE runQI' #-}

-- | Given @n@ such that @n = (a + b √c)/d@, return @(a, b, c, d)@.
unQI :: QI -> (Integer, Integer, Integer, Integer)
unQI n = runQI n (,,,)
{-# INLINE unQI #-}

-- | Given @n@ such that @n = a + b √c@, return @(a, b, c)@.
unQI' :: QI -> (Rational, Rational, Integer)
unQI' n = runQI' n (,,)
{-# INLINE unQI' #-}

qiZero, qiOne :: QI
qiZero = qi 0 0 0 1
qiOne  = qi 1 0 0 1
{-# INLINE qiZero #-}
{-# INLINE qiOne #-}

qiIsZero :: QI -> Bool
qiIsZero (unQI -> ~(a,b,_,_)) = a == 0 && b == 0

qiToFloat :: Floating a => QI -> a
qiToFloat (unQI -> ~(a,b,c,d)) =
  (fromInteger a + fromInteger b * sqrt (fromInteger c)) / fromInteger d

qiAddR :: Real a => QI -> a -> QI
qiAddR (unQI' -> ~(a,b,c)) (toRational -> x) = qi' (a+x) b c

qiSubR :: Real a => QI -> a -> QI
qiSubR n (toRational -> x) = qiAddR n (negate x)

qiMulR :: Real a => QI -> a -> QI
qiMulR (unQI' -> ~(a,b,c)) (toRational -> x) = qi' (a*x) (b*x) c

qiDivR :: (Show a, Real a) => QI -> a -> QI
qiDivR n (toRational . nonZero "qiDiv" -> x) = qiMulR n (recip x)

qiNegate :: QI -> QI
qiNegate n = qiMulR n (-1 :: Rational)

qiRecip :: QI -> Maybe QI
qiRecip n@(unQI -> ~(a,b,c,d))
  -- 1/((a + b √c)/d)                       =
  -- d/(a + b √c)                           =
  -- d (a − b √c) / ((a + b √c) (a − b √c)) =
  -- d (a − b √c) / (a² − b² c)             =
  -- (a d − b d √c) / (a² − b² c)
  | qiIsZero n = Nothing
  | denom == 0 = error ("qiRecip: Failed for " ++ show n)
  | otherwise  = Just (qi (a * d) (negate (b * d)) c denom)
  where denom = (a*a - b*b * c)

-- | Add two 'QI's if the square root terms are the same or zeros.
qiAdd :: QI -> QI -> Maybe QI
qiAdd (unQI' -> ~(a,b,c)) (unQI' -> ~(a',b',c'))
  | c  == 0   = Just (qi' (a + a') b'       c')
  | c' == 0   = Just (qi' (a + a') b        c)
  | c  == c'  = Just (qi' (a + a') (b + b') c)
                -- a + b √c + a' + b' √c =
                -- (a + a') + (b + b') √c
  | otherwise = Nothing

-- | Subtract two 'QI's if the square root terms are the same or zeros.
qiSub :: QI -> QI -> Maybe QI
qiSub n n' = qiAdd n (qiNegate n')

-- | Multiply two 'QI's if the square root terms are the same or zeros.
qiMul :: QI -> QI -> Maybe QI
qiMul n@(unQI' -> ~(a,b,c)) n'@(unQI' -> ~(a',b',c'))
  | c  == 0   = Just (qiMulR n' a)
  | c' == 0   = Just (qiMulR n  a')
  | c  == c'  = Just (qi' (a*a' + b*b'*fromInteger c) (a*b' + a'*b) c)
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

qiFloor :: QI -> Integer
qiFloor (unQI -> ~(a,b,c,d)) =
  -- n = (a + b √c)/d
  -- n d = a + b √c
  -- n d = a + signum b · √(b² c)
  n_d `div` d
  where
    n_d = a + min (signum b * b2cLow) (signum b * b2cHigh)

    ~(b2cLow, b2cHigh) = iSqrtBounds (b*b * c)

continuedFractionToQI :: (Integer, CycList Integer) -> QI
continuedFractionToQI (i0_, is_) = qiAddR (go is_) i0_
  where
    go (NonCyc as)   = goNonCyc as qiZero
    go (Cyc as b bs) = goNonCyc as (goCyc (b:bs))

    goNonCyc ((pos -> i):is) final = sudoQIRecip (qiAddR (goNonCyc is final) i)
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
