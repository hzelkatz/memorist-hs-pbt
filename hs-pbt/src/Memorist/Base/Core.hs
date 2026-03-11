{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}

module Memorist.Base.Core where

import Memorist.Base.Thunk
import Control.Monad.State.Lazy
import Control.Monad.Writer.Lazy


data Annotated a = Annotated { value :: a, annot :: Annot }
    deriving (Eq, Show)

instance Functor Annotated where
    fmap f (Annotated x a) = Annotated (f x) a

instance Applicative Annotated where
    pure x = Annotated x azero
    Annotated f a <*> Annotated x a' = Annotated (f x) (a `add` a')

instance Monad Annotated where
    (Annotated x a) >>= k = let r = k x in r {annot = a `add` annot r}

instance MonadWriter Annot Annotated where
    tell a = Annotated () a
    listen (Annotated x a) = Annotated (x, a) a
    pass (Annotated (x, f) a) = Annotated x (f a)

class Monad m => MonadTick m where
    tick :: m ()

instance MonadTick Annotated where
    tick = Annotated () (fromCost onetick)

class (MSt s, MonadState s m) => MonadAnnot s m where
    returnA :: Annotated a -> m a
    -- wrapA: adds the annotation accumulated so far to the result and reset it to azero in the context
    wrapA :: m a -> m (a, Annot)
    run :: m a -> s -> (Annotated a, s)

eval :: MonadAnnot s m => m a -> s -> Annotated a
eval m = fst . run m

eval1 :: MonadAnnot s m => m a -> Annotated a
eval1 m = eval m initstate

costAnnot :: Annotated a -> Cost
costAnnot = acost . annot

usageAnnot :: Annotated a -> USet
usageAnnot = ausage . annot

-- | Class for states of the Memorist monad
class MSt a where
    initstate :: a

instance MSt ThName where
    initstate = nzero

class (MSt s, MonadAnnot s m, MonadTick m) => Memorist s m where
    lazy :: m a -> m (Th a)

    force :: Th a -> m a
    force t = let (x, u) = useThunk t in returnA $ Annotated x (fromSet u)


newtype BaseM s a = BaseM { runBM :: s -> (Annotated a, s) }

instance Functor (BaseM s) where
    fmap f (BaseM g) = BaseM $ \s -> let (xa, s') = g s in (fmap f xa, s')

instance Applicative (BaseM s) where
    pure x = BaseM $ \s -> (pure x, s)
    mf <*> mx = BaseM $ \s ->
        let (fa, s') = runBM mf s
            (xa, s'') = runBM mx s'
        in (fa <*> xa, s'')

instance Monad (BaseM s) where
    mf >>= k = BaseM $ \s -> 
        let ~(xa, s') = runBM mf s
            ~(ya, s'') = runBM (k (value xa)) s'
        in (ya {annot = annot xa `add` annot ya}, s'')
        -- FIXME: not making use of that Annotated is a monad

instance MonadState s (BaseM s) where
    get = BaseM $ \s -> (pure s, s)
    put s = BaseM $ \_ -> (pure (), s)

instance MonadWriter (Annot) (BaseM s) where
    tell a = BaseM $ \s -> (tell a, s)
    listen m = BaseM $ \s -> let (xa, s') = runBM m s in (listen xa, s')
    pass m = BaseM $ \s -> let (xa, s') = runBM m s in (pass xa, s')

instance MonadTick (BaseM s) where
    tick = BaseM $ \s -> (tick, s)

instance MSt s => MonadAnnot s (BaseM s) where
    returnA xa = BaseM $ \s -> (xa, s)
    wrapA m = BaseM $ \s -> let (xa, s') = runBM m s in (pure (value xa, annot xa), s')
    -- wrapA m = censor (\_ -> azero) $ listen m
        -- Given that BaseM is a writer monad, this is essentially `censor (\_ -> azero) $ listen m`
    run = runBM
