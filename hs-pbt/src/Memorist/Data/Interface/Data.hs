{-# LANGUAGE TypeFamilies #-}

module Memorist.Data.Interface.Data where

import Memorist.Base.Thunk
import Memorist.Base.Core


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
