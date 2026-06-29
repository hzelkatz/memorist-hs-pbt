{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

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

-- annotate :: (a, Annot) -> Annotated a
-- annotate (x, a) = Annotated x a

-- unwrapAnnot :: Annotated a -> (a, Annot)
-- unwrapAnnot (Annotated x a) = (x, a)

costAnnot :: Annotated a -> Cost
costAnnot = acost . annot

usageAnnot :: Annotated a -> USet
usageAnnot = ausage . annot


newtype AnnotT m a = AnnotT { runAnnotT :: m (Annotated a) }

mapAnnotT :: (m (Annotated a) -> n (Annotated b)) -> AnnotT m a -> AnnotT n b
mapAnnotT f = AnnotT . f . runAnnotT

hoistAnnot :: Applicative m => Annotated a -> AnnotT m a
hoistAnnot = AnnotT . pure

instance Functor m => Functor (AnnotT m) where
    fmap f = mapAnnotT (fmap (fmap f))

instance Monad m => Applicative (AnnotT m) where
    pure = hoistAnnot . pure

    mf <*> mx = AnnotT $ do
        fa <- runAnnotT mf
        xa <- runAnnotT mx
        return $ fa <*> xa


instance Monad m => Monad (AnnotT m) where
    m >>= k = AnnotT $ do
        xa <- runAnnotT m
        ya <- runAnnotT $ k $ value xa
        return $ xa >> ya

instance Monad m => MonadWriter Annot (AnnotT m) where
    tell = hoistAnnot . tell

    listen m = AnnotT $ do
        xa <- runAnnotT m
        return $ listen xa

    pass m = AnnotT $ do
        xa <- runAnnotT m
        return $ pass xa

-- NOTE to self: this requires FlexibleInstances and UndecidableInstances
instance MonadState s m => MonadState s (AnnotT m) where
    get = AnnotT $ do
        s <- get
        return $ pure s

    put x = AnnotT $ do
        put x
        return $ pure ()


class Monad m => MonadAnnot m where
    -- -- unfolds the Annotated, returns the pure value and carry the annotation in output
    -- returnA :: Annotated a -> m a
    --
    -- returns the pure value in a monad and carry the annotation in the monad output
    annotate :: a -> Annot -> m a
    -- wraps the value with the annotation accumulated so far, returns
    -- the Annotated as the new value, while resetting the output annotation to azero
    wrapA :: m a -> m (Annotated a)

instance MonadAnnot Annotated where
    -- returnA = id
    annotate = Annotated
    wrapA = pure

instance Monad m => MonadAnnot (AnnotT m) where
    -- returnA = hoistAnnot
    annotate x = hoistAnnot . annotate x
    wrapA = mapAnnotT (fmap wrapA)


-- class Monad m => MonadTick m where
--     tick :: m ()

-- instance MonadTick Annotated where
--     tick = Annotated () (fromCost onetick)

-- -- NOTE to self: this helps in decl of MemoristBaseM as MonadTick
-- -- instance MonadTick m => MonadTick (StateT s m) where
-- --     tick = lift tick

-- instance Monad m => MonadTick (AnnotT m) where
--     tick = hoistAnnot tick


-- | Class for states of the Memorist monad
class MSt a where
    initstate :: a
    getName :: a -> ThName

instance MSt ThName where
    initstate = nzero
    getName = id


class MonadAnnot m => MonadMemorist m where
    lazy :: m a -> m (Th a)

    force :: Th a -> m a
    -- force t = let (x, u) = useThunk t in returnA $ Annotated x (fromSet u)
    force t = let (x, u) = useThunk t in annotate x (fromSet u)

    tick :: m ()
    -- tick = returnA $ Annotated () (fromCost onetick)
    tick = annotate () (fromCost onetick)

class (MSt s, MonadState s m, MonadMemorist m) => Memorist s m where
    runM :: m a -> s -> (Annotated a, s)


eval :: Memorist s m => m a -> s -> Annotated a
eval m = fst . runM m

eval1 :: Memorist s m => m a -> Annotated a
eval1 m = eval m initstate


newtype MemoristBaseT s m a = MemoristBaseT { runMBT :: AnnotT (StateT s m) a }

runMMBT :: MemoristBaseT s m a -> s -> m (Annotated a, s)
runMMBT = runStateT . runAnnotT . runMBT

instance Functor m => Functor (MemoristBaseT s m) where
    fmap f = MemoristBaseT . fmap f . runMBT

instance Monad m => Applicative (MemoristBaseT s m) where
    pure = MemoristBaseT . pure
    mf <*> mx = MemoristBaseT $ runMBT mf <*> runMBT mx

instance Monad m => Monad (MemoristBaseT s m) where
    m >>= k = MemoristBaseT $ runMBT m >>= runMBT . k

-- NOTE to self: this requires FlexibleInstances
instance Monad m => MonadState s (MemoristBaseT s m) where
    get = MemoristBaseT $ get
    put = MemoristBaseT . put

instance Monad m => MonadWriter Annot (MemoristBaseT s m) where
    tell = MemoristBaseT . tell
    listen = MemoristBaseT . listen . runMBT
    pass = MemoristBaseT . pass . runMBT

-- instance Monad m => MonadTick (MemoristBaseT s m) where
--     tick = MemoristBaseT $ tick

instance Monad m => MonadAnnot (MemoristBaseT s m) where
    -- returnA = MemoristBaseT . returnA
    annotate x = MemoristBaseT . annotate x
    wrapA = MemoristBaseT . wrapA . runMBT
