{-# LANGUAGE TypeFamilies, FlexibleContexts, FlexibleInstances #-}
{-# OPTIONS_GHC -fenable-rewrite-rules #-}

----------------------------------------------------------------------
-- |
-- Module      :  Data.Functor.Corepresentable
-- Copyright   :  (c) Edward Kmett 2011
-- License     :  BSD3
-- 
-- Maintainer  :  ekmett@gmail.com
-- Stability   :  experimental
-- 
-- Representable contravariant endofunctors over the category of Haskell 
-- types are isomorphic to @(_ -> r)@ and resemble mappings to a
-- fixed range.
----------------------------------------------------------------------

module Data.Functor.Corepresentable
  ( 
  -- * Values
    Value
  -- * Contravariant Keyed
  , Valued(..)
  -- * Contravariant Indexed
  , Coindexed(..)
  -- * Representable Contravariant Functors
  , Corepresentable(..)
  -- * Default definitions
  , contramapDefault
  , contramapWithValueDefault
  ) where

import Control.Monad.Reader
import Data.Functor.Contravariant
import Data.Functor.Product
import Data.Functor.Coproduct
import Prelude hiding (lookup)

type family Value (f :: * -> *)

-- | Dual to 'Keyed'.
class Contravariant f => Valued f where
  contramapWithValue :: (b -> Either a (Value f)) -> f a -> f b

-- | Dual to 'Indexed'.
class Coindexed f where
  coindex :: f a -> a -> Value f

-- | A 'Functor' @f@ is 'Corepresentable' if 'corep' and 'coindex' witness an isomorphism to @(_ -> Value f)@.
--
-- > tabulate . index = id
-- > index . tabulate = id
-- > tabulate . return f = return f

class (Coindexed f, Valued f) => Corepresentable f where
  -- | > contramap f (corep g) = corep (g . f)
  corep :: (a -> Value f) -> f a

{-# RULES
"corep/coindex" forall t. corep (coindex t) = t
 #-}

-- * Default definitions

contramapDefault :: Corepresentable f => (a -> b) -> f b -> f a
contramapDefault f = corep . (. f) . coindex 

contramapWithValueDefault :: Corepresentable f => (b -> Either a (Value f)) -> f a -> f b
contramapWithValueDefault f p = corep $ either (coindex p) id . f

-- * Dual arrows

type instance Value (Op r) = r

instance Valued (Op r) where
  contramapWithValue = contramapWithValueDefault

instance Coindexed (Op r) where
  coindex = getOp

instance Corepresentable (Op r) where
  corep = Op

-- * Predicates

type instance Value Predicate = Bool

instance Valued Predicate where
  contramapWithValue = contramapWithValueDefault

instance Coindexed Predicate where
  coindex = getPredicate

instance Corepresentable Predicate where
  corep = Predicate

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

instance (Corepresentable f, Corepresentable g) => Corepresentable (Product f g) where
  corep f = Pair (corep (fst . f)) (corep (snd . f))


-- * Coproducts

type instance Value (Coproduct f g) = Either (Value f) (Value g)

instance (Coindexed f, Coindexed g) => Coindexed (Coproduct f g) where
  coindex (Coproduct (Left f)) a  = Left  $ coindex f a 
  coindex (Coproduct (Right g)) a = Right $ coindex g a
