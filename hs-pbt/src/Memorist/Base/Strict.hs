-- Based on original version of the Memorist Semantics as appeared in
-- Li et al. 2026 (https://doi.org/10.1007/978-3-032-22720-1_17)

{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

{-# OPTIONS_GHC -Wno-orphans #-}

module Memorist.Base.Strict where

import Memorist.Base.Thunk
import Memorist.Base.Core
import Control.Monad.Identity ( Identity, runIdentity )
import Control.Monad.State.Lazy
import Control.Monad.Writer.Lazy


type MemoristM = MemoristT Identity

-- In the basic version, the thunk name is just a natural number.
-- The state is thus of Int type.
newtype MemoristT m a = MemoristT { runMT :: MemoristBaseT Int m a }

instance Functor m => Functor (MemoristT m) where
    fmap f = MemoristT . fmap f . runMT

instance Monad m => Applicative (MemoristT m) where
    pure = MemoristT . pure
    mf <*> mx = MemoristT $ runMT mf <*> runMT mx

instance Monad m => Monad (MemoristT m) where
    m >>= k = MemoristT $ runMT m >>= runMT . k

instance Monad m => MonadState Int (MemoristT m) where
    get = MemoristT $ get
    put = MemoristT . put

instance Monad m => MonadWriter Annot (MemoristT m) where
    tell = MemoristT . tell
    listen = MemoristT . listen . runMT
    pass = MemoristT . pass . runMT

-- instance Monad m => MonadTick (MemoristT m) where
--     tick = MemoristT $ tick

instance Monad m => MonadAnnot (MemoristT m) where
    annotate x = MemoristT . annotate x
    wrapA = MemoristT . wrapA . runMT

-- This version assign names which are essentially just plain natural number
-- consecutively to every thunkable part in the same order as if
-- the evaluation is done eagerly.
instance Monad m => MonadMemorist (MemoristT m) where
    lazy m = do
        ~(Annotated x a) <- wrapA m
        n <- genName
        return $ Th n x a

instance Memorist Int (MemoristT Identity) where
    runM m = runIdentity . runMMBT (runMT m)

genName :: Monad m => MemoristT m ThName
genName = do
    n <- get
    put $ n + 1
    return $ getName n

instance MSt Int where
    initstate = 0
    getName = fromInt
