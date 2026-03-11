-- Alternative naming scheme.

{-# LANGUAGE MultiParamTypeClasses #-}

module Memorist.Base.AltName where

import Memorist.Base.Thunk
import Memorist.Base.Core
import Control.Monad.State.Lazy
import Control.Monad.Writer.Lazy

newtype MemoristM a = MemoristM {runM :: BaseM ThName a}

instance Functor MemoristM where
    fmap f (MemoristM m) = MemoristM $ fmap f m

instance Applicative MemoristM where
    pure = MemoristM . pure
    mf <*> mx = MemoristM $ runM mf <*> runM mx

instance Monad MemoristM where
    mf >>= k = MemoristM $ runM mf >>= runM . k

instance MonadState ThName MemoristM where
    get = MemoristM $ get
    put = MemoristM . put

instance MonadWriter Annot MemoristM where
    tell = MemoristM . tell
    listen = MemoristM . listen . runM
    pass = MemoristM . pass . runM

instance MonadTick MemoristM where
    tick = MemoristM $ tick

instance MonadAnnot ThName MemoristM where
    returnA = MemoristM . returnA
    wrapA = MemoristM . wrapA . runM
    run = run . runM

-- Another major difference is how the `lazy` combinator works.
-- Instead of computing and assigning names to thunk consecutively,
-- we make the thunked computation run in the next level of namespace (`enclose`).
-- After returning from the thunked computation, we resume to the previous level,
-- from which the name of the thunk as a result of this `lazy m` is also generated.
instance Memorist ThName MemoristM where
    lazy m = do
        ~(x, a) <- enclose m
        n <- genName
        return $ Th n x a

enclose :: MemoristM a -> MemoristM (a, Annot)
enclose m = do
    n <- get
    put $ nshift n
    xa <- wrapA m
    put n
    return xa

genName :: MemoristM ThName
genName = do
    n <- get
    put $ nnext n
    return n
