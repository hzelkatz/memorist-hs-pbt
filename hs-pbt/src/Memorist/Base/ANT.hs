-- The 

{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

module Memorist.Base.ANT where

import Memorist.Base.Thunk
import Memorist.Base.Core
import Control.Monad.Identity ( Identity, runIdentity )
import Control.Monad.State.Lazy
import Control.Monad.Writer.Lazy


type MemoristM = MemoristT Identity

newtype MemoristT m a = MemoristT { runMT :: MemoristBaseT ThName m a }

instance Functor m => Functor (MemoristT m) where
    fmap f = MemoristT . fmap f . runMT

instance Monad m => Applicative (MemoristT m) where
    pure = MemoristT . pure
    mf <*> mx = MemoristT $ runMT mf <*> runMT mx

instance Monad m => Monad (MemoristT m) where
    m >>= k = MemoristT $ runMT m >>= runMT . k

instance Monad m => MonadState ThName (MemoristT m) where
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

-- One major difference is how the `lazy` combinator works.
-- Instead of computing and assigning names to thunk consecutively,
-- we make the thunked computation run in the next level of names (`enclose`).
-- After returning from the thunked computation, we resume to the previous level,
-- from which the name of the thunk as a result of this `lazy m` is also generated.
instance Monad m => MonadMemorist (MemoristT m) where
    lazy m = do
        ~(Annotated x a) <- enclose m
        n <- genName
        return $ Th n x a

instance Memorist ThName (MemoristT Identity) where
    runM m = runIdentity . runMMBT (runMT m)

enclose :: Monad m => MemoristT m a -> MemoristT m (Annotated a)
enclose m = do
    n <- get
    put $ nshift n
    xa <- wrapA m
    put n
    return xa

genName :: Monad m => MemoristT m ThName
genName = do
    n <- get
    put $ nnext n
    return n
