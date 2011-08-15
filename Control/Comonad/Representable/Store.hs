{-# LANGUAGE TypeFamilies
           , FlexibleContexts
           , FlexibleInstances
           , MultiParamTypeClasses
           , UndecidableInstances #-}
----------------------------------------------------------------------
-- |
-- Module      :  Control.Comonad.Representable.Store
-- Copyright   :  (c) Edward Kmett & Sjoerd Visscher 2011
-- License     :  BSD3
-- 
-- Maintainer  :  ekmett@gmail.com
-- Stability   :  experimental
-- 
-- A generalized Store comonad, parameterized by a Representable functor.
-- The representation of that functor serves as the index of the store.
----------------------------------------------------------------------
module Control.Comonad.Representable.Store
   ( Store
   , store
   , runStore
   , StoreT(..)
   , storeT
   , runStoreT
   , pos
   , peek
   , peeks
   , seek
   , seeks
   ) where

import Control.Comonad
import Control.Applicative
import Data.Key
import Data.Functor.Apply
import Data.Semigroup
import Control.Comonad.Hoist.Class
import Control.Comonad.Env.Class
import Control.Comonad.Traced.Class
import Control.Comonad.Cofree.Class
import Control.Comonad.Trans.Class
import Control.Comonad.Store.Class
import Control.Monad.Identity
import Data.Functor.Representable

-- | A memoized store comonad parameterized by a representable functor @g@, where 
-- the representatation of @g@, @Key g@ is the index of the store.
--
type Store g = StoreT g Identity

-- | Construct a store comonad computation from a function and a current index.
-- (The inverse of 'runStore'.)
store :: Representable g 
      => (Key g -> a)  -- ^ computation
      -> Key g         -- ^ index
      -> Store g a
store = storeT . Identity

-- | Unwrap a state monad computation as a function.
-- (The inverse of 'state'.)
runStore :: Indexable g 
         => Store g a           -- ^ a store to access
         -> (Key g -> a, Key g) -- ^ initial state
runStore (StoreT (Identity ga) k) = (index ga, k)

-- ---------------------------------------------------------------------------
-- | A store transformer comonad parameterized by:
--
--   * @g@ - A representable functor used to memoize results for an index @Key g@
--
--   * @w@ - The inner comonad.
data StoreT g w a = StoreT (w (g a)) (Key g) 

storeT :: (Functor w, Representable g) => w (Key g -> a) -> Key g -> StoreT g w a 
storeT = StoreT . fmap tabulate

runStoreT :: (Functor w, Indexable g) => StoreT g w a -> (w (Key g -> a), Key g)
runStoreT (StoreT w s) = (index <$> w, s)

instance (Comonad w, Representable g, Key g ~ s) => ComonadStore s (StoreT g w) where
  pos (StoreT _ s) = s
  peek s (StoreT w _) = extract w `index` s
  peeks f (StoreT w s) = extract w `index` f s
  seek s (StoreT w _) = StoreT w s
  seeks f (StoreT w s) = StoreT w (f s)

instance (Functor w, Functor g) => Functor (StoreT g w) where
  fmap f (StoreT w s) = StoreT (fmap (fmap f) w) s

instance (Apply w, Semigroup (Key g), Representable g) => Apply (StoreT g w) where
  StoreT ff m <.> StoreT fa n = StoreT ((<*>) <$> ff <.> fa) (m <> n)

instance (Applicative w, Semigroup (Key g), Monoid (Key g), Representable g) => Applicative (StoreT g w) where
  pure a = StoreT (pure (pure a)) mempty
  StoreT ff m <*> StoreT fa n = StoreT ((<*>) <$> ff <*> fa) (m `mappend` n)

instance (Extend w, Representable g) => Extend (StoreT g w) where
  duplicate (StoreT wf s) = StoreT (extend (tabulate . StoreT) wf) s

instance (Comonad w, Representable g) => Comonad (StoreT g w) where
  extract (StoreT wf s) = index (extract wf) s

instance Indexable g => ComonadTrans (StoreT g) where
  lower (StoreT w s) = fmap (`index` s) w

instance ComonadHoist (StoreT g) where
  cohoist (StoreT w s) = StoreT (Identity (extract w)) s

instance (ComonadTraced m w, Representable g) => ComonadTraced m (StoreT g w) where
  trace m = trace m . lower

instance (ComonadEnv m w, Representable g) => ComonadEnv m (StoreT g w) where 
  ask = ask . lower

instance (Representable g, ComonadCofree f w) => ComonadCofree f (StoreT g w) where
  unwrap (StoreT w s) = fmap (`StoreT` s) (unwrap w)
