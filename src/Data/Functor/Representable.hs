{-# LANGUAGE CPP #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# OPTIONS_GHC -fenable-rewrite-rules #-}
----------------------------------------------------------------------
-- |
-- Copyright   :  (c) Edward Kmett 2011-2013
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
  -- * Wrapped representable functors
  , Rep(..)
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
  , liftR2
  , liftR3
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
  , duplicatedRep
  , extendedRep
  -- ** Comonad
  , duplicateRep
  , extendRep
  , extractRep
  ) where

import Control.Applicative
import Control.Comonad
import Control.Comonad.Trans.Class
import Control.Comonad.Trans.Traced
import Control.Comonad.Cofree
import Control.Monad.Trans.Identity
import Control.Monad.Reader
import Data.Distributive
import Data.Key
import Data.Functor.Bind
import Data.Functor.Identity
import Data.Functor.Compose
import Data.Functor.Extend
import Data.Functor.Product
import qualified Data.Sequence as Seq
import Data.Semigroup hiding (Product)
import Prelude hiding (lookup)

-- | A 'Functor' @f@ is 'Representable' if 'tabulate' and 'index' witness an isomorphism to @(->) x@.
--
-- > tabulate . index = id
-- > index . tabulate = id
-- > tabulate . return f = return f

class (Distributive f, Indexable f) => Representable f where
  -- | > fmap f . tabulate = tabulate . fmap f
  tabulate :: (Key f -> a) -> f a

{-# RULES
"tabulate/index" forall t. tabulate (index t) = t #-}

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

duplicatedRep :: (Representable f, Semigroup (Key f)) => f a -> f (f a)
duplicatedRep w = tabulate (\m -> tabulate (index w . (<>) m))

extendedRep :: (Representable f, Semigroup (Key f)) => (f a -> b) -> f a -> f b
extendedRep f w = tabulate (\m -> f (tabulate (index w . (<>) m)))

duplicateRep :: (Representable f, Monoid (Key f)) => f a -> f (f a)
duplicateRep w = tabulate (\m -> tabulate (index w . mappend m))

extendRep :: (Representable f, Monoid (Key f)) => (f a -> b) -> f a -> f b
extendRep f w = tabulate (\m -> f (tabulate (index w . mappend m)))

extractRep :: (Indexable f, Monoid (Key f)) => f a -> a
extractRep fa = index fa mempty

{-
-- | We extend lens across a representable functor, due to the preservation of limits.
repLens :: Representable f => Lens a b -> Lens (f a) (f b)
repLens l = lens (fmapRep (l ^$)) $ \a b -> unrep $ liftA2 (l ^=) (Rep a) (Rep b)
-}

-- representing :: (Representable f, Functor g) => ((c -> g d) -> a -> g b) -> (f c -> g (f d)) -> f a -> g (f b)

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
  -- tabulate = TracedT . collect tabulate . curry
  tabulate = TracedT . unrep . collect (Rep . tabulate) . curry

instance (Representable f, Representable g) => Representable (Product f g) where
  tabulate f = Pair (tabulate (f . Left)) (tabulate (f . Right))

instance Representable f => Representable (Cofree f) where
  tabulate f = f Seq.empty :< tabulate (\k -> tabulate (f . (k Seq.<|)))


newtype Rep f a = Rep { unrep :: f a }

type instance Key (Rep f) = Key f

instance Representable f => Representable (Rep f) where
  tabulate = Rep . tabulate

instance Indexable f => Indexable (Rep f) where
  index (Rep f) i = index f i

instance Representable f => Keyed (Rep f) where
  mapWithKey = mapWithKeyRep

instance Indexable f => Lookup (Rep f) where
  lookup = lookupDefault

instance Representable f => Functor (Rep f) where
  fmap = fmapRep

instance Representable f => Apply (Rep f) where
  (<.>) = apRep

instance Representable f => Applicative (Rep f) where
  pure = pureRep
  (<*>) = apRep

instance Representable f => Distributive (Rep f) where
  distribute = distributeRep

instance Representable f => Bind (Rep f) where
  (>>-) = bindRep

instance Representable f => Monad (Rep f) where
  return = pureRep
  (>>=) = bindRep

#if __GLASGOW_HASKELL__ >= 704
instance (Representable f, Key f ~ a) => MonadReader a (Rep f) where
  ask = askRep
  local = localRep
#endif

instance Representable f => Zip (Rep f) where
  zipWith = zipWithRep

instance Representable f => ZipWithKey (Rep f) where
  zipWithKey = zipWithKeyRep

instance (Representable f, Semigroup (Key f)) => Extend (Rep f) where
  extended = extendedRep

instance (Representable f, Monoid (Key f)) => Comonad (Rep f) where
  extend = extendRep
  extract = extractRep

instance ComonadTrans Rep where
  lower (Rep f) = f

liftR2 :: Representable f => (a -> b -> c) -> f a -> f b -> f c
liftR2 f fa fb = tabulate $ \i -> f (index fa i) (index fb i)

liftR3 :: Representable f => (a -> b -> c -> d) -> f a -> f b -> f c -> f d
liftR3 f fa fb fc = tabulate $ \i -> f (index fa i) (index fb i) (index fc i)
