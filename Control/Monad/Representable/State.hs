{-# LANGUAGE TypeFamilies
           , FlexibleContexts
           , FlexibleInstances
           , MultiParamTypeClasses
           , UndecidableInstances #-}
----------------------------------------------------------------------
-- |
-- Module      :  Control.Monad.Representable.State
-- Copyright   :  (c) Edward Kmett & Sjoerd Visscher 2011
-- License     :  BSD3
-- 
-- Maintainer  :  ekmett@gmail.com
-- Stability   :  experimental
-- 
-- A generalized State monad, parameterized by a Representable functor.
-- The representation of that functor serves as the state.
----------------------------------------------------------------------
module Control.Monad.Representable.State
   ( State
   , state
   , runState
   , evalState
   , execState
   , mapState
   , StateT(..)
   , stateT
   , runStateT
   , evalStateT
   , execStateT
   , mapStateT
   , liftCallCC
   , liftCallCC'
   , get
   , gets
   , put
   , modify
   ) where

import Control.Applicative
import Data.Key
import Data.Functor.Bind
import Data.Functor.Bind.Trans
-- import Control.Monad.State.Class
import Control.Monad.Cont.Class
import Control.Monad.Reader.Class
import Control.Monad.Writer.Class
import Control.Monad.Trans.Class
import Control.Monad.Identity
import Data.Functor.Representable

-- ---------------------------------------------------------------------------
-- | A memoized state monad parameterized by a representable functor @g@, where 
-- the representatation of @g@, @Key g@ is the state to carry.
--
-- The 'return' function leaves the state unchanged, while @>>=@ uses
-- the final state of the first computation as the initial state of
-- the second.
type State g = StateT g Identity

-- | Construct a state monad computation from a function.
-- (The inverse of 'runState'.)
state :: Representable g 
      => (Key g -> (a, Key g))  -- ^ pure state transformer
      -> State g a              -- ^ equivalent state-passing computation
state f = stateT (Identity . f)

-- | Unwrap a state monad computation as a function.
-- (The inverse of 'state'.)
runState :: Indexable g 
         => State g a   -- ^ state-passing computation to execute
         -> Key g       -- ^ initial state
         -> (a, Key g)  -- ^ return value and final state
runState m = runIdentity . runStateT m

-- | Evaluate a state computation with the given initial state
-- and return the final value, discarding the final state.
--
-- * @'evalState' m s = 'fst' ('runState' m s)@
evalState :: Indexable g 
          => State g a  -- ^state-passing computation to execute
          -> Key g      -- ^initial value
          -> a          -- ^return value of the state computation
evalState m s = fst (runState m s)

-- | Evaluate a state computation with the given initial state
-- and return the final state, discarding the final value.
--
-- * @'execState' m s = 'snd' ('runState' m s)@
execState :: Indexable g
          => State g a  -- ^state-passing computation to execute
          -> Key g      -- ^initial value
          -> Key g      -- ^final state
execState m s = snd (runState m s)

-- | Map both the return value and final state of a computation using
-- the given function.
--
-- * @'runState' ('mapState' f m) = f . 'runState' m@
mapState :: Functor g => ((a, Key g) -> (b, Key g)) -> State g a -> State g b
mapState f = mapStateT (Identity . f . runIdentity)

-- ---------------------------------------------------------------------------
-- | A state transformer monad parameterized by:
--
--   * @g@ - A representable functor used to memoize results for a state @Key g@
--
--   * @m@ - The inner monad.
--
-- The 'return' function leaves the state unchanged, while @>>=@ uses
-- the final state of the first computation as the initial state of
-- the second.
newtype StateT g m a = StateT { getStateT :: g (m (a, Key g)) } 

stateT :: Representable g => (Key g -> m (a, Key g)) -> StateT g m a
stateT = StateT . tabulate

runStateT :: Indexable g => StateT g m a -> Key g -> m (a, Key g)
runStateT (StateT m) = index m

mapStateT :: Functor g => (m (a, Key g) -> n (b, Key g)) -> StateT g m a -> StateT g n b
mapStateT f (StateT m) = StateT (fmap f m)

-- | Evaluate a state computation with the given initial state
-- and return the final value, discarding the final state.
--
-- * @'evalStateT' m s = 'liftM' 'fst' ('runStateT' m s)@
evalStateT :: (Indexable g, Monad m) => StateT g m a -> Key g -> m a
evalStateT m s = do
    (a, _) <- runStateT m s
    return a

-- | Evaluate a state computation with the given initial state
-- and return the final state, discarding the final value.
--
-- * @'execStateT' m s = 'liftM' 'snd' ('runStateT' m s)@
execStateT :: (Indexable g, Monad m) => StateT g m a -> Key g -> m (Key g)
execStateT m s = do
    (_, s') <- runStateT m s
    return s'

instance (Functor g, Functor m) => Functor (StateT g m) where
  fmap f = StateT . fmap (fmap (\ ~(a, s) -> (f a, s))) . getStateT

instance (Functor g, Indexable g, Bind m) => Apply (StateT g m) where
  mf <.> ma = mf >>- \f -> fmap f ma

instance (Representable g, Functor m, Monad m) => Applicative (StateT g m) where
  pure = StateT . leftAdjunctRep return
  mf <*> ma = mf >>= \f -> fmap f ma

instance (Functor g, Indexable g, Bind m) => Bind (StateT g m) where
  StateT m >>- f = StateT $ fmap (>>- rightAdjunctRep (runStateT . f)) m
   
instance (Representable g, Monad m) => Monad (StateT g m) where
  return = StateT . leftAdjunctRep return
  StateT m >>= f = StateT $ fmap (>>= rightAdjunctRep (runStateT . f)) m

instance Representable f => BindTrans (StateT f) where
  liftB m = stateT $ \s -> fmap (\a -> (a, s)) m

instance Representable f => MonadTrans (StateT f) where
  lift m = stateT $ \s -> liftM (\a -> (a, s)) m

-- instance (Representable g, Monad m) => MonadState (Key g) (StateT g m) where
get :: (Representable g, Monad m) => StateT g m (Key g)
get = stateT $ \s -> return (s, s)

put :: (Applicative g, Monad m) => Key g -> StateT g m ()
put s = StateT $ pure $ return ((),s)

gets :: (Representable g, Monad m) => (Key g -> s) -> StateT g m s
gets f = liftM f get

modify :: (Representable g, Monad m) => (Key g -> Key g) -> StateT g m ()
modify f = stateT $ \s -> return ((), f s)

instance (Representable g, MonadReader e m) => MonadReader e (StateT g m) where
  ask = lift ask
  local = mapStateT . local

instance (Representable g, MonadWriter w m) => MonadWriter w (StateT g m) where
  tell = lift . tell
  listen = mapStateT $ \ma -> do
     ((a,s'), w) <- listen ma
     return ((a,w), s')
  pass = mapStateT $ \ma -> pass $ do
    ((a, f), s') <- ma
    return ((a, s'), f)

instance (Representable g, MonadCont m) => MonadCont (StateT g m) where
    callCC = liftCallCC' callCC
  
leftAdjunctRep :: Representable u => ((a, Key u) -> b) -> a -> u b
leftAdjunctRep f a = tabulate (\s -> f (a,s))

rightAdjunctRep :: Indexable u => (a -> u b) -> (a, Key u) -> b
rightAdjunctRep f ~(a, k) = f a `index` k

-- | Uniform lifting of a @callCC@ operation to the new monad.
-- This version rolls back to the original state on entering the
-- continuation.
liftCallCC :: Representable g => ((((a,Key g) -> m (b,Key g)) -> m (a,Key g)) -> m (a,Key g)) ->
    ((a -> StateT g m b) -> StateT g m a) -> StateT g m a
liftCallCC callCC' f = stateT $ \s ->
    callCC' $ \c ->
    runStateT (f (\a -> StateT $ pure $ c (a, s))) s

-- | In-situ lifting of a @callCC@ operation to the new monad.
-- This version uses the current state on entering the continuation.
-- It does not satisfy the laws of a monad transformer.
liftCallCC' :: Representable g => ((((a,Key g) -> m (b,Key g)) -> m (a,Key g)) -> m (a,Key g)) ->
    ((a -> StateT g m b) -> StateT g m a) -> StateT g m a
liftCallCC' callCC' f = stateT $ \s ->
    callCC' $ \c ->
    runStateT (f (\a -> stateT $ \s' -> c (a, s'))) s

