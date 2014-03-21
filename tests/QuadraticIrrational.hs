{-# LANGUAGE ViewPatterns #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

module Main (main) where

import Control.Applicative
import Data.Number.CReal
import Test.Tasty
import Test.Tasty.QuickCheck

import Numeric.QuadraticIrrational

-- Slow but precise.
type RefFloat = CReal

instance Arbitrary QI where
  arbitrary = consQI <$> arbitrary <*> arbitrary <*> arbitrary
    where
     consQI a b (NonNegative c) = qi a b c

  shrink (unQI -> ~(a,b,c)) =
    [ qi a' b  c  | a' <- shrink a ] ++
    [ qi a  b' c  | b' <- shrink b ] ++
    [ qi a  b  c' | NonNegative c' <- shrink (NonNegative c) ]

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests =
  testGroup "QuadraticIrrational"
    [ testGroup "Construction/destruction/conversion"
      [ testProperty "qi/runQI" $ \a b (NonNegative c) ->
          runQI (qi a b c) $ \a' b' c' ->
            approxEq' (approxQI a b c) (approxQI a' b' c')

      , testProperty "qi/runQI'" $ \a b (NonNegative c) ->
          runQI' (qi a b c) $ \a' b' c' d' ->
            approxEq' (approxQI a b c) (approxQI' a' b' c' d')

      , testProperty "qi'/runQI" $ \a b (NonNegative c) (NonZero d) ->
          runQI (qi' a b c d) $ \a' b' c' ->
            approxEq' (approxQI' a b c d) (approxQI a' b' c')

      , testProperty "qi'/runQI'" $ \a b (NonNegative c) (NonZero d) ->
          runQI' (qi' a b c d) $ \a' b' c' d' ->
            approxEq' (approxQI' a b c d) (approxQI' a' b' c' d')

      , testProperty "qiToFloat" $ \a b (NonNegative c) ->
          approxEq' (qiToFloat (qi a b c)) (approxQI a b c)
      ]

    , testGroup "Numerical operations"
      [ testProperty "qiSimplify" $ \n ->
          approxEq' (qiToFloat n) (qiToFloat (qiSimplify n))

      , testProperty "qiAddR" $ \n x ->
          approxEq' (qiToFloat (qiAddR n x)) (qiToFloat n + fromRational x)

      , testProperty "qiSubR" $ \n x ->
          approxEq' (qiToFloat (qiSubR n x)) (qiToFloat n - fromRational x)

      , testProperty "qiMulR" $ \n x ->
          approxEq' (qiToFloat (qiMulR n x)) (qiToFloat n * fromRational x)

      , testProperty "qiDivR" $ \n x ->
          x /= 0 ==>
            approxEq' (qiToFloat (qiDivR n x)) (qiToFloat n / fromRational x)

      , testProperty "qiNegate" $ \n ->
          approxEq' (qiToFloat (qiNegate n)) (negate (qiToFloat n))

      , testProperty "qiRecip" $ \n ->
          not (approxEq (qiToFloat n) 0)
            ==> let ~(Just nr) = qiRecip n
                in  approxEq' (qiToFloat nr) (recip (qiToFloat n))

      , testProperty "qiAdd" $ \a b (NonNegative c) a' b' c0Zero c1Zero ->
          let n  = qi a  b  (if c0Zero then 0 else c)
              n' = qi a' b' (if c1Zero then 0 else c)
              ~(Just r) = qiAdd n n'
          in  approxEq' (qiToFloat r) (qiToFloat n + qiToFloat n')

      , testProperty "qiSub" $ \a b (NonNegative c) a' b' c0Zero c1Zero ->
          let n  = qi a  b  (if c0Zero then 0 else c)
              n' = qi a' b' (if c1Zero then 0 else c)
              ~(Just r) = qiSub n n'
          in  approxEq' (qiToFloat r) (qiToFloat n - qiToFloat n')

      , testProperty "qiMul" $ \a b (NonNegative c) a' b' c0Zero c1Zero ->
          let n  = qi a  b  (if c0Zero then 0 else c)
              n' = qi a' b' (if c1Zero then 0 else c)
              ~(Just r) = qiMul n n'
          in  approxEq' (qiToFloat r) (qiToFloat n * qiToFloat n')

      , testProperty "qiDiv" $ \a b (NonNegative c) a' b' c0Zero c1Zero ->
          let n  = qi a  b  (if c0Zero then 0 else c)
              n' = qi a' b' (if c1Zero then 0 else c)
              ~(Just r) = qiDiv n n'
          in  not (approxEq (qiToFloat n') 0)
                ==> approxEq' (qiToFloat r) (qiToFloat n / qiToFloat n')

      , testProperty "qiPow" $ \n (NonNegative p) ->
          approxEq' (qiToFloat (qiPow n p))
                    -- CReal seems to diverge in 0 ** 1, use (^).
                    (qiToFloat n ^ p)

      , testProperty "qiFloor" $ \n ->
          qiFloor n === floor (qiToFloat n :: RefFloat)
      ]
    ]

approxQI :: Rational -> Rational -> Integer -> RefFloat
approxQI (fromRational -> a) (fromRational -> b) (fromInteger -> c) =
  a + b * sqrt c

approxQI' :: Integer -> Integer -> Integer -> Integer -> RefFloat
approxQI' (fromInteger -> a) (fromInteger -> b) (fromInteger -> c)
          (fromInteger -> d) =
  (a + b * sqrt c) / d

approxEq :: RefFloat -> RefFloat -> Bool
approxEq a b = abs (b - a) < 1e-6 * maximum [ 1, abs a, abs b ]

approxEq' :: RefFloat -> RefFloat -> Property
approxEq' a b =
  counterexample (show a ++ " is not approximately " ++ show b ++ " (diff = "
                   ++ show (abs (b - a)) ++ ")")
                 (approxEq a b)
