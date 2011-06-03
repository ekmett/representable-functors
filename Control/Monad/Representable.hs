{-# LANGUAGE GADTs, TypeFamilies, TypeOperators, CPP, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, UndecidableInstances, TypeSynonymInstances #-}
{-# OPTIONS_GHC -fenable-rewrite-rules -fno-warn-orphans #-}
----------------------------------------------------------------------
-- |
-- Module      :  Control.Monad.Representable
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

module Control.Monad.Representable
  ( 
  -- * Representable functor monad
    Rep, rep, runRep
  -- * Monad Transformer
  , RepT(..)
  , module Data.Functor.Representable
  ) where

import Control.Applicative
import Control.Comonad
import Control.Monad.Reader
import Control.Monad.Writer.Class as Writer
import Control.Monad.Trans.Class
import Control.Monad.IO.Class
import Data.Distributive
import Data.Key
import Data.Functor.Bind
import Data.Functor.Identity
import Data.Functor.Representable
import Data.Foldable
import Data.Monoid
import Data.Traversable
import Data.Semigroup.Foldable
import Data.Semigroup.Traversable
import Prelude hiding (lookup)

type Rep f = RepT f Identity

rep :: Functor f => f b -> Rep f b
rep = RepT . fmap Identity

runRep :: Functor f => Rep f b -> f b
runRep = fmap runIdentity . runRepT

-- * This 'tabulateresentable monad transformer' transforms any monad @m@ with a 'Representable' 'Monad'.
--   This monad in turn is also tabulateresentable if @m@ is 'Representable'.
newtype RepT f m b = RepT { runRepT :: f (m b) }

type instance Key (RepT f m) = (Key f, Key m)

instance (Functor f, Functor m) => Functor (RepT f m) where
  fmap f = RepT . fmap (fmap f) . runRepT

instance (Representable f, Apply m) => Apply (RepT f m) where
  RepT ff <.> RepT fa = RepT ((<.>) <$> ff <.> fa)

instance (Representable f, Applicative m) => Applicative (RepT f m) where
  pure = RepT . pure . pure 
  RepT ff <*> RepT fa = RepT ((<*>) <$> ff <*> fa)

instance (Representable f, Bind m) => Bind (RepT f m) where
  RepT fm >>- f = RepT $ tabulate (\a -> index fm a >>- flip index a . runRepT . f)

instance (Representable f, Monad m) => Monad (RepT f m) where
  return = RepT . pure . return
  RepT fm >>= f = RepT $ tabulate (\a -> index fm a >>= flip index a . runRepT . f)

-- instance (Representable f, Monad m) => MonadReader (Key f) (RepT f m) where ask = RepT (tabulate return)

instance Representable f => MonadTrans (RepT f) where
  lift = RepT . pure 

instance (Representable f, Distributive m) => Distributive (RepT f m) where
  distribute = RepT . fmap distribute . collect runRepT

instance (Keyed f, Keyed m) => Keyed (RepT f m) where
  mapWithKey f = RepT . mapWithKey (\k -> mapWithKey (f . (,) k)) . runRepT

instance (Indexable f, Indexable m) => Indexable (RepT f m) where
  index = uncurry . fmap index . index . runRepT

instance (Adjustable f, Adjustable m) => Adjustable (RepT f m) where
  adjust f (kf,km) = RepT . adjust (adjust f km) kf . runRepT

instance (Lookup f, Lookup m) => Lookup (RepT f m) where
  lookup (k,k') (RepT fm) = lookup k fm >>= lookup k'

instance (Representable f, Representable m) => Representable (RepT f m) where
  tabulate = RepT . tabulate . fmap tabulate . curry
  
instance (Foldable f, Foldable m) => Foldable (RepT f m) where
  foldMap f = foldMap (foldMap f) . runRepT

instance (Foldable1 f, Foldable1 m) => Foldable1 (RepT f m) where
  foldMap1 f = foldMap1 (foldMap1 f) . runRepT

instance (FoldableWithKey f, FoldableWithKey m) => FoldableWithKey (RepT f m) where
  foldMapWithKey f = foldMapWithKey (\k -> foldMapWithKey (f . (,) k)) . runRepT

instance (FoldableWithKey1 f, FoldableWithKey1 m) => FoldableWithKey1 (RepT f m) where
  foldMapWithKey1 f = foldMapWithKey1 (\k -> foldMapWithKey1 (f . (,) k)) . runRepT 

instance (Traversable f, Traversable m) => Traversable (RepT f m) where
  traverse f = fmap RepT . traverse (traverse f) . runRepT

instance (Traversable1 f, Traversable1 m) => Traversable1 (RepT f m) where
  traverse1 f = fmap RepT . traverse1 (traverse1 f) . runRepT

instance (TraversableWithKey f, TraversableWithKey m) => TraversableWithKey (RepT f m) where
  traverseWithKey f = fmap RepT . traverseWithKey (\k -> traverseWithKey (f . (,) k)) . runRepT

instance (TraversableWithKey1 f, TraversableWithKey1 m) => TraversableWithKey1 (RepT f m) where
  traverseWithKey1 f = fmap RepT . traverseWithKey1 (\k -> traverseWithKey1 (f . (,) k)) . runRepT

instance (Representable f, Representable m, Semigroup (Key f), Semigroup (Key m)) => Extend (RepT f m) where
  extend = extendRep
  duplicate = duplicateRep

instance (Representable f, Representable m, Semigroup (Key f), Semigroup (Key m), Monoid (Key f), Monoid (Key m)) => Comonad (RepT f m) where
  extract = extractRep

instance (Representable f, MonadIO m) => MonadIO (RepT f m) where
  liftIO = lift . liftIO 

instance (Representable f, MonadWriter w m) => MonadWriter w (RepT f m) where
  tell = lift . tell
  listen (RepT m) = RepT $ tabulate $ Writer.listen . index m
  pass (RepT m) = RepT $ tabulate $ Writer.pass . index m

