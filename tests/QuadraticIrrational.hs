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
  arbitrary = consQI <$> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary
    where
     consQI a b (NonNegative c) (NonZero d) = qi a b c d

  shrink (unQI -> ~(a,b,c,d)) =
    [ qi a' b  c  d  | a' <- shrink a ] ++
    [ qi a  b' c  d  | b' <- shrink b ] ++
    [ qi a  b  c' d  | NonNegative c' <- shrink (NonNegative c) ] ++
    [ qi a  b  c  d' | NonZero     d' <- shrink (NonZero     d) ]

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests =
  testGroup "QuadraticIrrational"
    [ testGroup "Construction/destruction/conversion"
      [ testProperty "qi/runQI" $ \a b (NonNegative c) (NonZero d) ->
          runQI (qi a b c d) $ \a' b' c' d' ->
            approxEq' (approxQI a b c d) (approxQI a' b' c' d')

      , testProperty "qi/runQI'" $ \a b (NonNegative c) (NonZero d) ->
          runQI' (qi a b c d) $ \a' b' c' ->
            approxEq' (approxQI a b c d) (approxQI' a' b' c')

      , testProperty "qi'/runQI" $ \a b (NonNegative c) ->
          runQI (qi' a b c) $ \a' b' c' d' ->
            approxEq' (approxQI' a b c) (approxQI a' b' c' d')

      , testProperty "qi'/runQI'" $ \a b (NonNegative c) ->
          runQI' (qi' a b c) $ \a' b' c' ->
            approxEq' (approxQI' a b c) (approxQI' a' b' c')

      , testProperty "qiModify" $ \n a' b' (NonZero d') ->
          runQI n $ \a b c d ->
            approxEq' (qiToFloat (qiModify n (\a_ b_ d_ ->
                                                (a_+a', b_-b', d_*d'))))
                      (qiToFloat (qi (a+a') (b-b') c (d*d')))

      , testProperty "qiToFloat" $ \a b (NonNegative c) (NonZero d) ->
          approxEq' (qiToFloat (qi a b c d)) (approxQI a b c d)
      ]

    , testGroup "Numerical operations"
      [ testProperty "qiAddI" $ \n x ->
          approxEq' (qiToFloat (qiAddI n x)) (qiToFloat n + fromInteger x)

      , testProperty "qiSubI" $ \n x ->
          approxEq' (qiToFloat (qiSubI n x)) (qiToFloat n - fromInteger x)

      , testProperty "qiMulI" $ \n x ->
          approxEq' (qiToFloat (qiMulI n x)) (qiToFloat n * fromInteger x)

      , testProperty "qiDivI" $ \n x ->
          x /= 0 ==>
            approxEq' (qiToFloat (qiDivI n x)) (qiToFloat n / fromInteger x)

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

      , testProperty "qiAdd" . withCompatiblePair $ \n n' ->
          let ~(Just r) = qiAdd n n'
          in  approxEq' (qiToFloat r) (qiToFloat n + qiToFloat n')

      , testProperty "qiSub" . withCompatiblePair $ \n n' ->
          let ~(Just r) = qiSub n n'
          in  approxEq' (qiToFloat r) (qiToFloat n - qiToFloat n')

      , testProperty "qiMul" . withCompatiblePair $ \n n' ->
          let ~(Just r) = qiMul n n'
          in  approxEq' (qiToFloat r) (qiToFloat n * qiToFloat n')

      , testProperty "qiDiv" . withCompatiblePair $ \n n' ->
          let ~(Just r) = qiDiv n n'
          in  not (approxEq (qiToFloat n') 0)
                ==> approxEq' (qiToFloat r) (qiToFloat n / qiToFloat n')

      , testProperty "qiPow" $ \n (NonNegative p) ->
          -- Limit the power for speed.
          (p <= 10) ==>
            approxEq' (qiToFloat (qiPow n p))
                      -- CReal seems to diverge in 0 ** 1, use (^).
                      (qiToFloat n ^ p)

      , testProperty "qiFloor" $ \n ->
          qiFloor n === floor (qiToFloat n :: RefFloat)

      , testProperty "qiToContinuedFraction/continuedFractionToQI" $ \n ->
          let cf  = qiToContinuedFraction n
              len = case cf of
                      (_, NonCyc _)   -> 0
                      (_, Cyc _ _ xs) -> length xs
          -- Limit the length of the periodic part for speed.
          in (len <= 100) ==>
               approxEq' (qiToFloat n) (qiToFloat (continuedFractionToQI cf))
      ]
    ]

withCompatiblePair :: Testable p
                   => (QI -> QI -> p) -> QI -> QI -> Bool -> Bool -> Property
withCompatiblePair f n0_ n1_ c0Zero c1Zero =
  counterexample ("n0 = " ++ show n0) . counterexample ("n1 = " ++ show n1) $
    f n0 n1
  where
    n0 = runQI n0_ $ \a b c d ->
           qi a b (if c0Zero then 0 else c) d

    n1 = runQI n0_ $ \_ _ c _ -> runQI n1_ $ \a b _ d ->
           qi a b (if c1Zero then 0 else c) d

approxQI :: Integer -> Integer -> Integer -> Integer -> RefFloat
approxQI a b c d =
  (fromInteger a + fromInteger b * sqrt (fromInteger c)) / fromInteger d

approxQI' :: Rational -> Rational -> Integer -> RefFloat
approxQI' a b c =
  fromRational a + fromRational b * sqrt (fromInteger c)

approxEq :: RefFloat -> RefFloat -> Bool
approxEq a b = abs (b - a) < 1e-6 * maximum [ 1, abs a, abs b ]

approxEq' :: RefFloat -> RefFloat -> Property
approxEq' a b =
  counterexample (show a ++ " is not approximately " ++ show b ++ " (diff = "
                   ++ show (abs (b - a)) ++ ")")
                 (approxEq a b)
