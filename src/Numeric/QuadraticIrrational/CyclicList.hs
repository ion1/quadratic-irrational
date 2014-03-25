-- |
-- Module      : Numeric.QuadraticIrrational.CyclicList
-- Description : A container for a possibly cyclic list.
-- Copyright   : © 2014 Johan Kiviniemi
-- License     : MIT
-- Maintainer  : Johan Kiviniemi <devel@johan.kiviniemi.name>
-- Stability   : provisional
-- Portability : portable

module Numeric.QuadraticIrrational.CyclicList
  ( CycList (..)
  ) where

import Data.Foldable
import Data.Monoid

-- | A container for a possibly cyclic list.
--
-- >>> toList (NonCyc "hello")
-- "hello"
--
-- >>> take 70 (toList (Cyc "prefix " 'c' "ycle"))
-- "prefix cyclecyclecyclecyclecyclecyclecyclecyclecyclecyclecyclecyclecyc"
data CycList a = NonCyc [a]  -- ^ A non-cyclic list.
               | Cyc [a] a [a]
                 -- ^ A non-cyclic list followed by the head of a cyclic list
                 -- followed by the tail of the cyclic list.
  deriving (Eq, Ord, Read, Show)

instance Functor CycList where
  fmap f (NonCyc as) = NonCyc (fmap f as)
  fmap f (Cyc as b bs) = Cyc (fmap f as) (f b) (fmap f bs)

instance Foldable CycList where
  foldMap f (NonCyc as)   = foldMap f as
  foldMap f (Cyc as b bs) = foldMap f as <> foldMap f (cycle (b:bs))
