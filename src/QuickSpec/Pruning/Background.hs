-- A pruning layer which automatically adds axioms about functions as they appear.
{-# OPTIONS_HADDOCK hide #-}
{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, FlexibleContexts, GeneralizedNewtypeDeriving, UndecidableInstances, TypeOperators #-}
module QuickSpec.Pruning.Background where

import QuickSpec.Term
import QuickSpec.Testing
import QuickSpec.Pruning
import QuickSpec.Prop
import QuickSpec.Terminal
import qualified Data.Set as Set
import Data.Set(Set)
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.State.Strict hiding (State)

newtype Pruner fun m a =
  Pruner (StateT (Set fun) m a)
  deriving (Functor, Applicative, Monad, MonadIO, MonadTrans, MonadTester testcase term, MonadTerminal)

class Background f where
  background :: f -> [Prop (Term f)]
  background _ = []

run :: Monad m => Pruner fun m a -> m a
run (Pruner x) =
  evalStateT x Set.empty

instance (Ord fun, Background fun, MonadPruner (Term fun) norm m) =>
  MonadPruner (Term fun) norm (Pruner fun m) where
  normaliser = lift normaliser
  add prop = do
    mapM_ addFunction (funs prop)
    lift (add prop)

addFunction :: (Ord fun, Background fun, MonadPruner (Term fun) norm m) => fun -> Pruner fun m ()
addFunction f = do
  funcs <- Pruner get
  unless (f `Set.member` funcs) $ do
    Pruner (put (Set.insert f funcs))
    mapM_ add (background f)

instance (Background fun1, Background fun2) => Background (fun1 :+: fun2) where
  background (Inl x) = map (fmap (fmap Inl)) (background x)
  background (Inr x) = map (fmap (fmap Inr)) (background x)
