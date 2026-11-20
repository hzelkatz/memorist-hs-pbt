-- The main version of the Memorist monad, based on our variant of
-- the Memorist semantics that employs the ancestral thunk naming.

{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

module Memorist.Base.ANT
    ( MemoristM
    , MemoristT
    , runMT
    )
where

import Memorist.Base.Thunk
import Memorist.Base.Core
import Control.Monad.Identity ( Identity, runIdentity )
import Control.Monad.State.Lazy
import Control.Monad.Writer.Lazy


type MemoristM = MemoristT Identity

newtype MemoristT m a = MemoristT (MemoristBaseT ThName m a)

runMT :: MemoristT m a -> MemoristBaseT ThName m a
runMT (MemoristT m) = m

instance Functor m => Functor (MemoristT m) where
    fmap f = MemoristT . fmap f . runMT

instance Monad m => Applicative (MemoristT m) where
    pure = MemoristT . pure
    mf <*> mx = MemoristT $ runMT mf <*> runMT mx

instance Monad m => Monad (MemoristT m) where
    m >>= k = MemoristT $ runMT m >>= runMT . k

instance Monad m => MonadWriter Annot (MemoristT m) where
    tell = MemoristT . tell
    listen = MemoristT . listen . runMT
    pass = MemoristT . pass . runMT

-- instance Monad m => MonadTick (MemoristT m) where
--     tick = MemoristT $ tick

instance Monad m => MonadAnnot (MemoristT m) where
    annotate x = MemoristT . annotate x
    wrapA = MemoristT . wrapA . runMT

-- In computing `lazy`, we make the thunked computation run in
-- the next level of names (`enclose`).
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
    n <- MemoristT get
    MemoristT $ put $ nshift n
    xa <- wrapA m
    MemoristT $ put n
    return xa

genName :: Monad m => MemoristT m ThName
genName = do
    n <- MemoristT get
    MemoristT $ put $ nnext n
    return n
