{-# LANGUAGE TypeFamilies #-}

module Memorist.Data.List where

import Memorist.Core.Annotation
import Memorist.Core.Thunk
import Memorist.Core.Semantics
import Memorist.Data.Interface
import Data.Set as S


data ListT a = NilT | ConsT (Th a) (Th (ListT a))
    deriving (Eq, Show)

reprM_ListT :: Repr a => [a] -> M (ListT (Rep a))
reprM_ListT []     = ret NilT
reprM_ListT (x:xs) =
    lazybind (reprM x) $ \tx ->
    lazybind (reprM xs) $ \txs -> ret (ConsT tx txs)

abstract_ListT :: Repr a => ListT (Rep a) -> [a]
abstract_ListT NilT = []
abstract_ListT (ConsT (Th _ x) (Th _ xs)) = abstract x : abstract_ListT xs

instance Repr a => Repr [a] where
    type Rep [a] = ListT (Rep a)
    reprM = reprM_ListT
    abstract = abstract_ListT


usageLC :: AnnotCntx -> ListT a -> Int -> USet
usageLC _ NilT _ = S.empty
usageLC ac (ConsT _ (Th i xs')) n
    | n <= 0    = S.empty
    | otherwise = mapSu ac i `union` usageLC ac xs' (n - 1)
