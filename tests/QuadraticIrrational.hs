{-# LANGUAGE ViewPatterns #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

module Main (main) where

import Control.Applicative
--import Numeric.Compensated
import Test.Tasty
import Test.Tasty.QuickCheck

import Numeric.QuadraticIrrational

--type RefFloat = Overcompensated Double
-- TODO Double precision issues.
type RefFloat = Double

instance Arbitrary QI where
  arbitrary = consQI <$> arbitrary <*> arbitrary <*> arbitrary
    where
     consQI a b (NonNegative c) = qi a b c

  shrink n = unQI n $ \a b c ->
    [ qi a' b  c  | a' <- shrink a ] ++
    [ qi a  b' c  | b' <- shrink b ] ++
    [ qi a  b  c' | NonNegative c' <- shrink (NonNegative c) ]

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests =
  testGroup "QuadraticIrrational"
    [ testGroup "Construction/destruction/conversion"
      [ testProperty "qi/unQI" $ \a b (NonNegative c) ->
          unQI (qi a b c) $ \a' b' c' ->
            approxEq' (approxQI a b c) (approxQI a' b' c')

      , testProperty "qi/unQI'" $ \a b (NonNegative c) ->
          unQI' (qi a b c) $ \a' b' c' d' ->
            approxEq' (approxQI a b c) (approxQI' a' b' c' d')

      , testProperty "qi'/unQI" $ \a b (NonNegative c) (NonZero d) ->
          unQI (qi' a b c d) $ \a' b' c' ->
            approxEq' (approxQI' a b c d) (approxQI a' b' c')

      , testProperty "qi'/unQI'" $ \a b (NonNegative c) (NonZero d) ->
          unQI' (qi' a b c d) $ \a' b' c' d' ->
            approxEq' (approxQI' a b c d) (approxQI' a' b' c' d')

      , testProperty "qiToFloat" $ \a b (NonNegative c) ->
          approxEq' (qiToFloat (qi a b c)) (approxQI a b c)
      ]

    , testGroup "Numerical operations"
      [ testProperty "qiSimplify" $ \n ->
          approxEq' (unQI n approxQI) (unQI (qiSimplify n) approxQI)

      , testProperty "qiAddR" $ \n x ->
          approxEq' (unQI (qiAddR n x) approxQI)
                    (unQI n approxQI + fromRational x)

      , testProperty "qiSubR" $ \n x ->
          approxEq' (unQI (qiSubR n x) approxQI)
                    (unQI n approxQI - fromRational x)

      , testProperty "qiMulR" $ \n x ->
          approxEq' (unQI (qiMulR n x) approxQI)
                    (unQI n approxQI * fromRational x)

      , testProperty "qiDivR" $ \n x ->
          x /= 0 ==>
            approxEq' (unQI (qiDivR n x) approxQI)
                      (unQI n approxQI / fromRational x)

      , testProperty "qiRecip" $ \n ->
          not (approxEq (unQI n approxQI) 0)
            ==> let ~(Just nr) = qiRecip n
                in  approxEq' (unQI nr approxQI) (recip (unQI n approxQI))

      , testProperty "qiPow" $ \n (NonNegative p) ->
          approxEq' (unQI (qiPow n p) approxQI)
                    (unQI n approxQI ** fromInteger p)
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
