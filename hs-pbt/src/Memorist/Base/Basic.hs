-- Basic version.

{-# LANGUAGE MultiParamTypeClasses #-}

module Memorist.Base.Basic where

import Memorist.Base.Thunk
import Memorist.Base.Core
import Control.Monad.State.Lazy
import Control.Monad.Writer.Lazy


newtype MemoristM a = MemoristM {runM :: BaseM Int a}

instance Functor MemoristM where
    fmap f (MemoristM m) = MemoristM $ fmap f m

instance Applicative MemoristM where
    pure = MemoristM . pure
    mf <*> mx = MemoristM $ runM mf <*> runM mx

instance Monad MemoristM where
    mf >>= k = MemoristM $ runM mf >>= runM . k

instance MonadState Int MemoristM where
    get = MemoristM $ get
    put = MemoristM . put

instance MonadWriter Annot MemoristM where
    tell = MemoristM . tell
    listen = MemoristM . listen . runM
    pass = MemoristM . pass . runM

instance MonadTick MemoristM where
    tick = MemoristM $ tick

instance MonadAnnot Int MemoristM where
    returnA = MemoristM . returnA
    wrapA = MemoristM . wrapA . runM
    run = run . runM

-- While we use the `ThName` type, this version essentially uses Ints as thunk names
-- and assign names consecutively to every thunkable part in the same order as
-- if the evaluation is done eagerly.
instance Memorist Int MemoristM where
    lazy m = do
        ~(x, a) <- wrapA m
        n <- genName
        return $ Th n x a

genName :: MemoristM ThName
genName = do
    n <- get
    put $ n + 1
    return $ fromInt n

instance MSt Int where
    initstate = 0

fromInt :: Int -> ThName
fromInt n = ThName ThNameNil n
