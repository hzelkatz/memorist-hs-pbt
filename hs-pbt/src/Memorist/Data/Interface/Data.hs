{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
-- {-# LANGUAGE GeneralisedNewtypeDeriving #-}

module Memorist.Data.Interface.Data where

import Memorist.Base.Thunk
import Memorist.Base.Core

import Control.Monad (liftM)

-- | 'Repr a' describes the translation of a datatype into its Memorist representation.
-- We define such representation type via Haskell's associated types.
class Repr a where
    type Rep a
    reprM :: Memorist s m => a -> m (Rep a)
    abstract :: Rep a -> a

instance Repr () where
    type Rep () = ()
    reprM = return
    abstract = id

instance Repr Bool where
    type Rep Bool = Bool
    reprM = return
    abstract = id

instance Repr Int where
    type Rep Int = Int
    reprM = return
    abstract = id

-- -----------------------------------------------------------------------------

-- We define Memorist representations for several more built-in datatypes.
-- In general, arguments to data constructors are thunked.
-- But depending on what is to be analyzed, we might not be interested in
-- the impact of laziness in certain data structures.
-- Therefore we define variants of representations to allow simplified analysis
-- that treats the particular thunks as if always demanded.

data MaybeT a = JustT (Th a) | NothingT
    deriving (Eq, Show)

instance Repr a => Repr (Maybe a) where
    type Rep (Maybe a) = MaybeT (Rep a)
    
    reprM (Just x) = liftM JustT $ lazy $ reprM x
    reprM _        = return NothingT

    abstract (JustT tx) = Just $ abstract (tval tx)
    abstract _          = Nothing

-- | The "strict" variant
newtype SMaybe a = SMaybe (Maybe a)
    deriving (Eq,Show)
    -- deriving (Eq,Show,Functor,Applicative,Monad)

fromSMaybe :: SMaybe a -> Maybe a
fromSMaybe (SMaybe x) = x

instance Repr a => Repr (SMaybe a) where
    type Rep (SMaybe a) = Maybe (Rep a)
    
    reprM (SMaybe (Just x)) = liftM Just $ reprM x
    reprM _                 = return Nothing

    abstract (Just x) = SMaybe $ Just $ abstract x
    abstract _        = SMaybe Nothing

data PairT a b = PairT (Th a) (Th b)
    deriving (Eq, Show)

instance (Repr a, Repr b) => Repr (a,b) where
    type Rep (a,b) = PairT (Rep a) (Rep b)

    reprM (x,y) = do
        tx <- lazy $ reprM x
        ty <- lazy $ reprM y
        return $ PairT tx ty
    
    abstract (PairT tx ty) = (abstract (tval tx), abstract (tval ty))


-- | The "strict" variant
newtype SPair a b = SPair (a,b) deriving (Eq,Show)

fromSPair :: SPair a b -> (a,b)
fromSPair (SPair p) = p

instance (Repr a, Repr b) => Repr (SPair a b) where
    type Rep (SPair a b) = (Rep a, Rep b)
    reprM (SPair (x,y)) = do { x' <- reprM x ; y' <- reprM y ; return (x',y') }
    abstract (x,y) = SPair (abstract x, abstract y)

-- =============================================================================

fromPure1 :: (Memorist s m, Repr a) => (Th (Rep a) -> m b) -> a -> m b
fromPure1 fM x = do
    tx <- lazy $ reprM x
    fM tx

fromPure2 :: (Memorist s m, Repr a, Repr b) =>
    (Th (Rep a) -> Th (Rep b) -> m c) -> a -> b -> m c
fromPure2 fM x y = do
    tx <- lazy $ reprM x
    ty <- lazy $ reprM y
    fM tx ty

fromPure2' :: (Memorist s m, Repr a, Repr b) =>
    (Th (Rep a) -> Rep b -> m c) -> a -> b -> m c
fromPure2' fM x y = do
    tx <- lazy $ reprM x
    y' <- reprM y
    fM tx y'

fromPure3 :: (Memorist s m, Repr a, Repr b, Repr c) =>
    (Th (Rep a) -> Th (Rep b) -> Th (Rep c) -> m d) -> a -> b -> c -> m d
fromPure3 fM x y z = do
    tx <- lazy $ reprM x
    ty <- lazy $ reprM y
    tz <- lazy $ reprM z
    fM tx ty tz
