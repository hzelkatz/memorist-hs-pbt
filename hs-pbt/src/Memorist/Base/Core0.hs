{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}

module Memorist.Base.Core0 where

import Prelude hiding (toInteger, fromInteger)
import qualified Data.Set as Set
import Control.Monad
import Control.Monad.Identity
import Control.Monad.State.Lazy
import Control.Monad.Writer.Lazy
-- import Control.Monad.Trans.State.Lazy
-- import Control.Monad.Trans.Writer.Lazy
-- import Control.Monad.Trans.Class

class (Eq t, Ord t) => IThName t where
    nzero :: t
    nnext :: t -> t

newtype Cost = Cost Integer
    deriving (Eq, Ord, Show)

cplus :: Cost -> Cost -> Cost
cplus (Cost n) (Cost m) = Cost (n + m)

onetick :: Cost
onetick = Cost 1

toInteger :: Cost -> Integer
toInteger (Cost n) = n


data INameCost t = NameCost { ncname :: t, nccost :: Cost }
    deriving (Eq, Ord, Show)

type IUSet t = Set.Set (INameCost t)

empty :: IUSet t
empty = Set.empty

union :: IThName t => IUSet t -> IUSet t -> IUSet t
union = Set.union

insert :: IThName t => INameCost t -> IUSet t -> IUSet t
insert = Set.insert

freshFrom :: IThName t => IUSet t -> t -> IUSet t
freshFrom s n = Set.filter ((>= n) . ncname) s

sumcost :: IThName t => IUSet t -> Cost
sumcost = Set.foldr (cplus . nccost) (Cost 0)

--------------------------------------------------------------------------------

data IAnnot t = Annot { acost :: Cost, ausage :: IUSet t }
    deriving (Eq, Show)

instance IThName t => Semigroup (IAnnot t) where
    (<>) = add

instance IThName t => Monoid (IAnnot t) where
    mempty = azero

-- | The empty annotation
azero :: IAnnot t
azero = Annot (Cost 0) empty

add :: IThName t => IAnnot t -> IAnnot t -> IAnnot t
add (Annot c s) (Annot c' s') = Annot (c `cplus` c') (s `union` s')

addCost :: IThName t => IAnnot t -> Cost -> IAnnot t
addCost a c = add a $ Annot c empty

addSet :: IThName t => IAnnot t -> IUSet t -> IAnnot t
addSet a s = add a $ Annot (Cost 0) s

fromCost :: IThName t => Cost -> IAnnot t
fromCost = addCost azero

fromSet :: IThName t => IUSet t -> IAnnot t
fromSet = addSet azero

--------------------------------------------------------------------------------

data ITh t a = Th t a (IAnnot t)
    deriving (Eq, Show)

useThunk :: IThName t => ITh t a -> (a, IUSet t)
useThunk (Th n x a) = (x, insert (NameCost n (acost a)) $ ausage a)

useThunk' :: IThName t => ITh t a -> IUSet t
useThunk' = snd . useThunk

--------------------------------------------------------------------------------

newtype AnnotT t m a = AnnotT { runAT :: WriterT (IAnnot t) m a }
    deriving (Eq, Show)

type AnnotM t = AnnotT t Identity

runAnnotT :: AnnotT t m a -> m (a, IAnnot t)
runAnnotT = runWriterT . runAT

runAnnotM :: AnnotM t a -> (a, IAnnot t)
runAnnotM = runIdentity . runAnnotT

instance Functor m => Functor (AnnotT t m) where
    fmap f (AnnotT m) = AnnotT $ fmap f m

instance (IThName t, Applicative m) => Applicative (AnnotT t m) where
    pure = AnnotT . pure
    AnnotT mf <*> AnnotT mx = AnnotT $ mf <*> mx

instance (IThName t, Monad m) => Monad (AnnotT t m) where
    AnnotT m >>= k = AnnotT $ m >>= runAT . k

instance (IThName t, Monad m) => MonadWriter (IAnnot t) (AnnotT t m) where
    tell = AnnotT . tell
    listen (AnnotT m) = AnnotT $ listen m
    pass (AnnotT m) = AnnotT $ pass m

instance IThName t => MonadTrans (AnnotT t) where
    lift = AnnotT . lift

tickA :: (IThName t, Monad m) => AnnotT t m ()
tickA = AnnotT $ tell (fromCost onetick) >> return ()

value :: AnnotM t a -> a
value = fst . runAnnotM

annot :: AnnotM t a -> IAnnot t
annot = snd . runAnnotM

costAnnot :: AnnotM t a -> Cost
costAnnot = acost . annot

usageAnnot :: AnnotM t a -> IUSet t
usageAnnot = ausage . annot

--------------------------------------------------------------------------------

-- For instance:

class (IThName t, Monad m) => Memorist t m | m -> t where
    lazy :: m a -> m (ITh t a)
    force :: ITh t a -> m a
    tick :: m ()

newtype MemoristT t m a = MemoristT { runMT :: AnnotT t (StateT t m) a }

type MemoristM t = MemoristT t Identity

runMemoristT :: MemoristT t m a -> t -> m ((a, IAnnot t), t)
runMemoristT m = runStateT $ runAnnotT $ runMT m

runMemoristM :: MemoristM t a -> t -> ((a, IAnnot t), t)
runMemoristM m = runIdentity . runMemoristT m

instance Functor m => Functor (MemoristT t m) where
    fmap f (MemoristT m) = MemoristT $ fmap f m

instance (IThName t, Monad m) => Applicative (MemoristT t m) where
    pure = MemoristT . pure
    MemoristT mf <*> MemoristT mx = MemoristT $ mf <*> mx

instance (IThName t, Monad m) => Monad (MemoristT t m) where
    MemoristT m >>= k = MemoristT $ m >>= runMT . k

instance (IThName t, Monad m) => MonadState t (MemoristT t m) where
    get = MemoristT $ lift get
    put s = MemoristT $ lift $ put s

instance (IThName t, Monad m) => MonadWriter (IAnnot t) (MemoristT t m) where
    tell = MemoristT . tell
    listen (MemoristT m) = MemoristT $ listen m
    pass (MemoristT m) = MemoristT $ pass m

instance IThName t => MonadTrans (MemoristT t) where
    lift = MemoristT . lift . lift

instance (IThName t, Monad m) => Memorist t (MemoristT t m) where
    lazy m = do
        ~(x, a) <- censor (\_ -> azero) $ listen m
        -- here we use 'censor' to 'reset' the accumulated annotation,
        -- as it no longer belongs to the immediate output, but to the thunked computation
        n <- get
        put $ nnext n
        return $ Th n x a

    force t = do
        let (x, u) = useThunk t
        tell $ fromSet u
        return x

    tick = MemoristT tickA
