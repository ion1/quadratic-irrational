{-# OPTIONS_GHC -fno-warn-orphans #-}

module CyclicList (tests) where

import Control.Applicative
import qualified Data.Foldable as F
import Test.Tasty
import Test.Tasty.QuickCheck

import Numeric.QuadraticIrrational.CyclicList

instance Arbitrary a => Arbitrary (CycList a) where
  arbitrary = oneof [ NonCyc <$> arbitrary
                    , Cyc <$> arbitrary <*> arbitrary <*> arbitrary
                    ]

  shrink (NonCyc as)   = [ NonCyc as'   | as' <- shrink as ]
  shrink (Cyc as b bs) = [ Cyc as' b bs | as' <- shrink as ]
                      ++ [ Cyc as b' bs | b'  <- shrink b  ]
                      ++ [ Cyc as b bs' | bs' <- shrink bs ]

tests :: TestTree
tests =
  testGroup "CyclicList"
    [ testProperty "fmap" . withListEquiv $ \asC asL ->
        initEq' (fmap (*10) asC) (fmap (*10) asL)
    , testProperty "toList" . withListEquiv $ \asC asL ->
        take 1000 (F.toList asC) === take 1000 asL
    ]

withListEquiv :: (CycList Integer -> [Integer] -> b) -> CycList Integer -> b
withListEquiv f cl@(NonCyc as)   = f cl as
withListEquiv f cl@(Cyc as b bs) = f cl (as ++ cycle (b:bs))

initEq :: Eq a => CycList a -> [a] -> Bool
initEq (NonCyc as)   cs = take 1000 cs == take 1000 as
initEq (Cyc as b bs) cs = take 1000 cs == take 1000 (as ++ cycle (b:bs))

initEq' :: (Eq a, Show a) => CycList a -> [a] -> Property
initEq' (NonCyc as)   cs = take 1000 cs === take 1000 as
initEq' (Cyc as b bs) cs = take 1000 cs === take 1000 (as ++ cycle (b:bs))
