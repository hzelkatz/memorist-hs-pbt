{-# LANGUAGE MultiParamTypeClasses #-}

module Memorist.DataT.List where

import Memorist.Core
import Memorist.Components.Annotation
import Memorist.Components.Thunk
import Memorist.DataT.Data
import Data.Set as S


data ListT a = NilT | ConsT (Th a) (Th (ListT a))
    deriving (Eq, Show)


repM_ListT :: Rep a b => [a] -> M (ListT b)
repM_ListT []     = ret NilT
repM_ListT (x:xs) =
    lazybind (repM x) $ \tx ->
    lazybind (repM xs) $ \txs -> ret (ConsT tx txs)

abst_ListT :: Rep a b => ListT b -> [a]
abst_ListT NilT = []
abst_ListT (ConsT (Th _ x) (Th _ xs)) = abst x : abst_ListT xs

instance Rep a b => Rep [a] (ListT b) where
    repM = repM_ListT
    abst = abst_ListT


usageLC :: AnnotCntx -> ListT a -> Int -> USet
usageLC _ NilT _ = S.empty
usageLC ac (ConsT _ (Th i xs')) n
    | n <= 0    = S.empty
    | otherwise = mapSu ac i `union` usageLC ac xs' (n - 1)

