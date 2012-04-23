{-# LANGUAGE GADTs, TypeFamilies, TypeOperators, CPP, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, UndecidableInstances, TypeSynonymInstances #-}
{-# OPTIONS_GHC -fenable-rewrite-rules -fno-warn-orphans #-}
----------------------------------------------------------------------
-- |
-- Module      :  Control.Monad.Representable.Reader
-- Copyright   :  (c) Edward Kmett 2011,
--                (c) Conal Elliott 2008
-- License     :  BSD3
--
-- Maintainer  :  ekmett@gmail.com
-- Stability   :  experimental
--
-- Representable functors on Hask all monads, being isomorphic to
-- a reader monad.
----------------------------------------------------------------------

module Control.Monad.Representable.Reader
  (
  -- * Representable functor monad
    Reader, runReader
  -- * Monad Transformer
  , ReaderT(..), readerT, runReaderT
  , ask
  , local
  , module Data.Functor.Representable
  ) where

import Control.Applicative
import Control.Comonad
import Control.Monad.Reader.Class
import Control.Monad.Writer.Class as Writer
import Control.Monad.Trans.Class
import Control.Monad.IO.Class
import Data.Distributive
import Data.Key
import Data.Functor.Bind
import Data.Functor.Identity
import Data.Functor.Representable
import Data.Foldable
import Data.Traversable
import Data.Semigroup
import Data.Semigroup.Foldable
import Data.Semigroup.Traversable
import Prelude hiding (lookup,zipWith)

type Reader f = ReaderT f Identity

runReader :: Indexable f => Reader f b -> Key f -> b
runReader = fmap runIdentity . runReaderT

-- * This 'representable monad transformer' transforms any monad @m@ with a 'Representable' 'Monad'.
--   This monad in turn is also representable if @m@ is 'Representable'.
newtype ReaderT f m b = ReaderT { getReaderT :: f (m b) }

readerT :: Representable f => (Key f -> m b) -> ReaderT f m b
readerT = ReaderT . tabulate

runReaderT :: Indexable f => ReaderT f m b -> Key f -> m b
runReaderT = index . getReaderT

type instance Key (ReaderT f m) = (Key f, Key m)

instance (Functor f, Functor m) => Functor (ReaderT f m) where
  fmap f = ReaderT . fmap (fmap f) . getReaderT

instance (Indexable f, Indexable m) => Indexable (ReaderT f m) where
  index = uncurry . fmap index . index . getReaderT

instance (Representable f, Representable m) => Representable (ReaderT f m) where
  tabulate = ReaderT . tabulate . fmap tabulate . curry

instance (Representable f, Apply m) => Apply (ReaderT f m) where
  ReaderT ff <.> ReaderT fa = ReaderT (unrep ((<.>) <$> Rep ff <.> Rep fa))

instance (Representable f, Applicative m) => Applicative (ReaderT f m) where
  pure = ReaderT . pureRep . pure
  ReaderT ff <*> ReaderT fa = ReaderT (unrep ((<*>) <$> Rep ff <*> Rep fa))

instance (Representable f, Bind m) => Bind (ReaderT f m) where
  ReaderT fm >>- f = ReaderT $ tabulate (\a -> index fm a >>- flip index a . getReaderT . f)

instance (Representable f, Monad m) => Monad (ReaderT f m) where
  return = ReaderT . pureRep . return
  ReaderT fm >>= f = ReaderT $ tabulate (\a -> index fm a >>= flip index a . getReaderT . f)

#if __GLASGOW_HASKELL >= 704

instance (Representable f, Monad m, Key f ~ e) => MonadReader e (ReaderT f m) where
  ask = ReaderT (tabulate return)
  local f m = readerT $ \r -> runReaderT m (f r)
#if MIN_VERSION_transformers(0,3,0)
  reader = readerT . fmap return
#endif

#endif

instance Representable f => MonadTrans (ReaderT f) where
  lift = ReaderT . pureRep

instance (Representable f, Distributive m) => Distributive (ReaderT f m) where
  distribute = ReaderT . fmapRep distribute . unrep . collect (Rep . getReaderT)

instance (Representable f, Keyed m) => Keyed (ReaderT f m) where
  mapWithKey f = ReaderT . mapWithKeyRep (\k -> mapWithKey (f . (,) k)) . getReaderT

instance (Indexable f, Lookup m) => Lookup (ReaderT f m) where
  lookup (k,k') (ReaderT fm) = lookup k' (index fm k)

instance (Representable f, Representable m, Semigroup (Key f), Semigroup (Key m)) => Extend (ReaderT f m) where
  extend = extendRep
  duplicate = duplicateRep

instance (Representable f, Zip m) => Zip (ReaderT f m) where
  zipWith f (ReaderT as) (ReaderT bs) = ReaderT $ tabulate $ \i -> zipWith f (index as i) (index bs i)

instance (Representable f, ZipWithKey m) => ZipWithKey (ReaderT f m) where
  zipWithKey f (ReaderT as) (ReaderT bs) = ReaderT $ tabulate $ \i -> zipWithKey (f . (,) i) (index as i) (index bs i)

instance (Representable f, Representable m, Semigroup (Key f), Semigroup (Key m), Monoid (Key f), Monoid (Key m)) => Comonad (ReaderT f m) where
  extract = extractRep

instance (Representable f, MonadIO m) => MonadIO (ReaderT f m) where
  liftIO = lift . liftIO

instance (Representable f, MonadWriter w m) => MonadWriter w (ReaderT f m) where
  tell = lift . tell
  listen (ReaderT m) = ReaderT $ tabulate $ Writer.listen . index m
  pass (ReaderT m) = ReaderT $ tabulate $ Writer.pass . index m

-- misc. instances that can exist, but aren't particularly about representability

instance (Adjustable f, Adjustable m) => Adjustable (ReaderT f m) where
  adjust f (kf,km) = ReaderT . adjust (adjust f km) kf . getReaderT

instance (Foldable f, Foldable m) => Foldable (ReaderT f m) where
  foldMap f = foldMap (foldMap f) . getReaderT

instance (Foldable1 f, Foldable1 m) => Foldable1 (ReaderT f m) where
  foldMap1 f = foldMap1 (foldMap1 f) . getReaderT

instance (FoldableWithKey f, FoldableWithKey m) => FoldableWithKey (ReaderT f m) where
  foldMapWithKey f = foldMapWithKey (\k -> foldMapWithKey (f . (,) k)) . getReaderT

instance (FoldableWithKey1 f, FoldableWithKey1 m) => FoldableWithKey1 (ReaderT f m) where
  foldMapWithKey1 f = foldMapWithKey1 (\k -> foldMapWithKey1 (f . (,) k)) . getReaderT

instance (Traversable f, Traversable m) => Traversable (ReaderT f m) where
  traverse f = fmap ReaderT . traverse (traverse f) . getReaderT

instance (Traversable1 f, Traversable1 m) => Traversable1 (ReaderT f m) where
  traverse1 f = fmap ReaderT . traverse1 (traverse1 f) . getReaderT

instance (Representable f, TraversableWithKey f, TraversableWithKey m) => TraversableWithKey (ReaderT f m) where
  traverseWithKey f = fmap ReaderT . traverseWithKey (\k -> traverseWithKey (f . (,) k)) . getReaderT

instance (Representable f, TraversableWithKey1 f, TraversableWithKey1 m) => TraversableWithKey1 (ReaderT f m) where
  traverseWithKey1 f = fmap ReaderT . traverseWithKey1 (\k -> traverseWithKey1 (f . (,) k)) . getReaderT
