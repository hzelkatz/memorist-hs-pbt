{-# LANGUAGE TypeFamilies #-}
-- {-# LANGUAGE MultiParamTypeClasses #-}

module Memorist.Demand.List where

import Memorist.Core.Annotation
import Memorist.Core.Thunk
import Memorist.Core.Semantics
import Memorist.Data.Interface
import Memorist.Data.List
import Memorist.Demand.Interface
import Data.Set as S
import Test.QuickCheck as QC (Gen, Arbitrary (..), sized, chooseInt)


data ListD a = NilD | ConsD (ThD a) (ThD (ListD a))
    deriving (Eq, Show)

{-
instance Demand a b => Demand (ListT a) (ListD b) where
    usage _  NilT           _              = S.empty
    usage _  _              NilD           = S.empty
    usage ac (ConsT tx txs) (ConsD dx dxs) = usage ac tx dx `union` usage ac txs dxs

instance ReprDemand a b => ReprDemand [a] (ListD b)
-}
instance Demand a => Demand (ListT a) where
    type Dem (ListT a) = ListD (Dem a)

    usage _  NilT           _              = S.empty
    usage _  _              NilD           = S.empty
    usage ac (ConsT tx txs) (ConsD dx dxs) = usage ac tx dx `union` usage ac txs dxs


sizeD :: Int -> ListD a -> Int
sizeD n NilD               = n
sizeD n (ConsD _ (Need d)) = 1 + sizeD n d
sizeD n (ConsD _ Skip)     = 1


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
instance ArbDemand a b => ArbDemand (ListT a) (ListD b) where
    arbitraryDemandFrom NilT = return NilD
    arbitraryDemandFrom (ConsT tx txs) = do
        dx <- arbitraryDemandFrom tx
        dxs <- arbitraryDemandFrom txs
        return $ ConsD dx dxs
-}
instance ArbDemand a => ArbDemand (ListT a) where
    arbitraryDemandFrom NilT = return NilD
    arbitraryDemandFrom (ConsT tx txs) = do
        dx <- arbitraryDemandFrom tx
        dxs <- arbitraryDemandFrom txs
        return $ ConsD dx dxs

test1 = arbitraryDemandFrom $ evalValue (reprM ([1..5] :: [Int])) [] :: Gen (ListD Int)
test2 = arbitraryDemandFromRepr $ ([1..5] :: [Int]) :: Gen (ListD Int)

