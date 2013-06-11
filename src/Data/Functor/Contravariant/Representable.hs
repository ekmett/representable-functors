{-# LANGUAGE TypeFamilies, FlexibleContexts, FlexibleInstances #-}
{-# OPTIONS_GHC -fenable-rewrite-rules #-}
----------------------------------------------------------------------
-- |
-- Copyright   :  (c) Edward Kmett 2011-2013
-- License     :  BSD3
--
-- Maintainer  :  ekmett@gmail.com
-- Stability   :  experimental
--
-- Representable contravariant endofunctors over the category of Haskell
-- types are isomorphic to @(_ -> r)@ and resemble mappings to a
-- fixed range.
----------------------------------------------------------------------
module Data.Functor.Contravariant.Representable
  (
  -- * Values
    Value
  -- * Contravariant Keyed
  , Valued(..)
  -- * Contravariant Indexed
  , Coindexed(..)
  -- * Representable Contravariant Functors
  , Representable(..)
  -- * Default definitions
  , contramapDefault
  , contramapWithValueDefault
  ) where

import Control.Monad.Reader
import Data.Functor.Contravariant
import Data.Functor.Contravariant.Day
import Data.Functor.Product
import Data.Functor.Coproduct
import Prelude hiding (lookup)

type family Value (f :: * -> *)

-- | Dual to 'Keyed'.
class Contravariant f => Valued f where
  contramapWithValue :: (b -> Either a (Value f)) -> f a -> f b

instance (Valued f, Valued g) => Valued (Day f g) where
  contramapWithValue d2eafg (Day fb gc abc) = Day (contramapWithValue id fb) (contramapWithValue id gc) $ \d -> case d2eafg d of
    Left a -> case abc a of
      (b, c) -> (Left b, Left c)
    Right (vf, vg) -> (Right vf, Right vg)

-- | Dual to 'Indexed'.
class Coindexed f where
  coindex :: f a -> a -> Value f

type instance Value (Day f g) = (Value f, Value g)

instance (Coindexed f, Coindexed g) => Coindexed (Day f g) where
  coindex (Day fb gc abc) a = case abc a of
    (b, c) -> (coindex fb b, coindex gc c)

-- | A 'Contravariant' functor @f@ is 'Representable' if 'contrarep' and 'coindex' witness an isomorphism to @(_ -> Value f)@.
class (Coindexed f, Valued f) => Representable f where
  -- | > contramap f (contrarep g) = contrarep (g . f)
  contrarep :: (a -> Value f) -> f a

instance (Representable f, Representable g) => Representable (Day f g) where
  contrarep a2fg = Day (contrarep fst) (contrarep snd) $ \a -> let b = a2fg a in (b,b)
  {-# INLINE contrarep #-}

{-# RULES
"contrarep/coindex" forall t. contrarep (coindex t) = t
 #-}

-- * Default definitions

contramapDefault :: Representable f => (a -> b) -> f b -> f a
contramapDefault f = contrarep . (. f) . coindex

contramapWithValueDefault :: Representable f => (b -> Either a (Value f)) -> f a -> f b
contramapWithValueDefault f p = contrarep $ either (coindex p) id . f

-- * Dual arrows

type instance Value (Op r) = r

instance Valued (Op r) where
  contramapWithValue = contramapWithValueDefault

instance Coindexed (Op r) where
  coindex = getOp

instance Representable (Op r) where
  contrarep = Op

-- * Predicates

type instance Value Predicate = Bool

instance Valued Predicate where
  contramapWithValue = contramapWithValueDefault

instance Coindexed Predicate where
  coindex = getPredicate

instance Representable Predicate where
  contrarep = Predicate

-- * Products

type instance Value (Product f g) = (Value f, Value g)

instance (Valued f, Valued g) => Valued (Product f g) where
  -- contramapWithValue :: (b -> Either a (Value f)) -> f a -> f b
  contramapWithValue h (Pair f g) = Pair
      (contramapWithValue (fmap fst . h) f)
      (contramapWithValue (fmap snd . h) g)
      -- (contramapWithValue (either id snd . h) g)
      -- (either g snd . h)

instance (Coindexed f, Coindexed g) => Coindexed (Product f g) where
  coindex (Pair f g) a = (coindex f a, coindex g a)

instance (Representable f, Representable g) => Representable (Product f g) where
  contrarep f = Pair (contrarep (fst . f)) (contrarep (snd . f))

-- * Coproducts

type instance Value (Coproduct f g) = Either (Value f) (Value g)

instance (Coindexed f, Coindexed g) => Coindexed (Coproduct f g) where
  coindex (Coproduct (Left f)) a  = Left  $ coindex f a
  coindex (Coproduct (Right g)) a = Right $ coindex g a
