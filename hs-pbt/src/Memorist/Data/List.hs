{-# LANGUAGE TypeFamilies #-}

module Memorist.Data.List where

import Memorist.Base.Thunk
import Memorist.Base.Core
import Memorist.Data.Interface
import Test.QuickCheck as QC (Gen, Arbitrary (..), sized, chooseInt)


data ListT a = NilT | ConsT (Th a) (Th (ListT a))
    deriving (Eq, Show)

reprM_ListT :: (Memorist s m, Repr a) => [a] -> m (ListT (Rep a))
reprM_ListT []     = return NilT
reprM_ListT (x:xs) = do
    tx <- lazy $ reprM x
    txs <- lazy $ reprM_ListT xs
    return $ ConsT tx txs

abstract_ListT :: Repr a => ListT (Rep a) -> [a]
abstract_ListT NilT = []
abstract_ListT (ConsT (Th _ x _) (Th _ xs _)) = abstract x : abstract_ListT xs

instance (Repr a) => Repr [a] where
    type Rep [a] = ListT (Rep a)
    reprM = reprM_ListT
    abstract = abstract_ListT

--------------------------------------------------------------------------------

data ListD a = NilD | ConsD (ThD a) (ThD (ListD a))
    deriving (Eq, Show)

instance Demand a => Demand (ListT a) where
    type Dem (ListT a) = ListD (Dem a)

    usage NilT           _              = empty
    usage _              NilD           = empty
    usage (ConsT tx txs) (ConsD dx dxs) = usage tx dx `union` usage txs dxs


sizeD :: Int -> ListD a -> Int
sizeD n NilD               = n
sizeD n (ConsD _ (Need d)) = 1 + sizeD n d
sizeD _ (ConsD _ Skip)     = 1


-- QC generator for ListD
genListD' :: Arbitrary a => Int -> Gen (ListD a)
genListD' k
    | k <= 0 = return NilD
    | otherwise = do
        dx <- arbitrary
        xs <- genListD' (k-1)
        dxs <- arbitraryWrap xs
        return $ ConsD dx dxs

shrinkListD :: Arbitrary a => ListD a -> [ListD a]
shrinkListD NilD = []
shrinkListD (ConsD dx (Need xs)) =
    [NilD] ++
    [ConsD dx' Skip | dx' <- shrink dx] ++
    [ConsD dx' (Need xs') | (dx', xs') <- shrink (dx, xs)]
shrinkListD (ConsD dx Skip) =
    [NilD] ++ [ConsD dx' Skip | dx' <- shrink dx]

instance Arbitrary a => Arbitrary (ListD a) where
    arbitrary = QC.sized $ \n -> do
        k <- chooseInt (0, max 0 n)
        genListD' k
    shrink = shrinkListD


{-
instance DemandArb a b => DemandArb (ListT a) (ListD b) where
    arbDemandFrom NilT = return NilD
    arbDemandFrom (ConsT tx txs) = do
        dx <- arbDemandFrom tx
        dxs <- arbDemandFrom txs
        return $ ConsD dx dxs
-}
instance DemandArb a => DemandArb (ListT a) where
    arbDemandFrom NilT = return NilD
    arbDemandFrom (ConsT tx txs) = do
        dx <- arbDemandFrom tx
        dxs <- arbDemandFrom txs
        return $ ConsD dx dxs

instance ReprDemandArb a => ReprDemandArb [a]
