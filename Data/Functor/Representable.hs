{-# LANGUAGE TypeFamilies, FlexibleContexts, FlexibleInstances #-}
{-# OPTIONS_GHC -fenable-rewrite-rules #-}
----------------------------------------------------------------------
-- |
-- Module      :  Data.Functor.Representable
-- Copyright   :  (c) Edward Kmett 2011
-- License     :  BSD3
-- 
-- Maintainer  :  ekmett@gmail.com
-- Stability   :  experimental
-- 
-- Representable endofunctors over the category of Haskell types are 
-- isomorphic to the reader monad and so inherit a very large number
-- of properties for free.
----------------------------------------------------------------------

module Data.Functor.Representable
  ( 
  -- * Representable Functors
    Representable(..)
  -- ** Representable Lenses
  , repLens 
  -- * Default definitions
  -- ** Functor
  , fmapRep
  -- ** Distributive
  , distributeRep
  -- ** Keyed
  , mapWithKeyRep
  -- ** Apply/Applicative
  , apRep
  , pureRep
  -- ** Bind/Monad
  , bindRep
  , bindWithKeyRep
  -- ** Zip/ZipWithKey
  , zipWithRep
  , zipWithKeyRep
  -- ** MonadReader
  , askRep
  , localRep
  -- ** Extend
  , duplicateRep
  , extendRep
  -- ** Comonad
  , extractRep
  ) where

import Control.Applicative
import Control.Comonad.Trans.Traced
import Control.Monad.Trans.Identity
import Control.Monad.Reader
import Data.Distributive
import Data.Key
import Data.Functor.Bind
import Data.Functor.Identity
import Data.Functor.Compose
import Data.Functor.Product
import Data.Lens.Common
import Data.Semigroup hiding (Product)
import Prelude hiding (lookup)

-- | A 'Functor' @f@ is 'Representable' if 'tabulate' and 'index' witness an isomorphism to @(->) x@.
--
-- > tabulate . index = id
-- > index . tabulate = id
-- > tabulate . return f = return f

class (Indexable f, Distributive f, Keyed f, Apply f, Applicative f, ZipWithKey f) => Representable f where
  -- | > fmap f . tabulate = tabulate . fmap f
  tabulate :: (Key f -> a) -> f a

{-# RULES
"tabulate/index" forall t. tabulate (index t) = t
 #-}

-- * Default definitions

fmapRep :: Representable f => (a -> b) -> f a -> f b
fmapRep f = tabulate . fmap f . index 

mapWithKeyRep :: Representable f => (Key f -> a -> b) -> f a -> f b
mapWithKeyRep f = tabulate . (<*>) f . index

pureRep :: Representable f => a -> f a
pureRep = tabulate . const

bindRep :: Representable f => f a -> (a -> f b) -> f b
bindRep m f = tabulate (\a -> index (f (index m a)) a)

bindWithKeyRep :: Representable f => f a -> (Key f -> a -> f b) -> f b
bindWithKeyRep m f = tabulate (\a -> index (f a (index m a)) a)

askRep :: Representable f => f (Key f)
askRep = tabulate id

localRep :: Representable f => (Key f -> Key f) -> f a -> f a
localRep f m = tabulate (index m . f)

apRep :: Representable f => f (a -> b) -> f a -> f b
apRep f g = tabulate (index f <*> index g) 

zipWithRep :: Representable f => (a -> b -> c) -> f a -> f b -> f c
zipWithRep f g h = tabulate $ \k -> f (index g k) (index h k)

zipWithKeyRep :: Representable f => (Key f -> a -> b -> c) -> f a -> f b -> f c
zipWithKeyRep f g h = tabulate $ \k -> f k (index g k) (index h k)

distributeRep :: (Representable f, Functor w) => w (f a) -> f (w a)
distributeRep wf = tabulate (\k -> fmap (`index` k) wf)

duplicateRep :: (Representable f, Semigroup (Key f)) => f a -> f (f a)
duplicateRep w = tabulate (\m -> tabulate (index w . (<>) m))

extendRep :: (Representable f, Semigroup (Key f)) => (f a -> b) -> f a -> f b
extendRep f w = tabulate (\m -> f (tabulate (index w . (<>) m)))

extractRep :: (Indexable f, Monoid (Key f)) => f a -> a
extractRep fa = index fa mempty

-- | We extend lens across a representable functor, due to the preservation of limits.
repLens :: Representable f => Lens a b -> Lens (f a) (f b)
repLens l = lens (fmap (l ^$)) (liftA2 (l ^=))

-- * Instances

instance Representable Identity where
  tabulate f = Identity (f ())

instance Representable m => Representable (IdentityT m) where
  tabulate = IdentityT . tabulate

instance Representable ((->) e) where
  tabulate = id

instance Representable m => Representable (ReaderT e m) where
  tabulate = ReaderT . fmap tabulate . curry 

instance (Representable f, Representable g) => Representable (Compose f g) where
  tabulate = Compose . tabulate . fmap tabulate . curry

instance Representable w => Representable (TracedT s w) where
  tabulate = TracedT . collect tabulate . curry

instance (Representable f, Representable g) => Representable (Product f g) where
  tabulate f = Pair (tabulate (f . Left)) (tabulate (f . Right))

