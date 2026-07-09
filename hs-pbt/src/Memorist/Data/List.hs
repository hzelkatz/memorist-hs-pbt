{-# LANGUAGE TypeFamilies #-}
-- {-# LANGUAGE GeneralisedNewtypeDeriving #-}

{-# OPTIONS_GHC -Wno-orphans #-}

module Memorist.Data.List where

import Memorist.Base.Thunk
import Memorist.Base.Core
import Memorist.Data.Interface
import Test.QuickCheck as QC (Gen, Arbitrary (..), sized, chooseInt)


data ListT a = NilT | ConsT (Th a) (Th (ListT a))
    deriving (Eq, Show)

instance Repr a => Repr [a] where
    type Rep [a] = ListT (Rep a)

    reprM [] = return NilT
    reprM (x:xs) = ConsT <$> lazy (reprM x) <*> lazy (reprM xs)

    abstract NilT = []
    abstract (ConsT tx txs) = abstract (tval tx) : abstract (tval txs)

sizeT :: Int -> ListT a -> Int
sizeT n NilT = n
sizeT n (ConsT _ t) = 1 + sizeT n (tval t)

-- Demand
data ListD a = NilD | ConsD (ThD a) (ThD (ListD a))
    deriving (Eq, Show)

instance Demand a => Demand (ListT a) where
    type Dem (ListT a) = ListD (Dem a)

    fullDemand NilT = NilD
    fullDemand (ConsT tx txs) = ConsD (fullDemand tx) (fullDemand txs)

    usage (ConsT tx txs) (ConsD dx dxs) = usage tx dx `union` usage txs dxs
    usage _              _              = empty

instance Demand a => LBoundDemand (ListT a) where
    minDemand NilT        = NilD
    minDemand (ConsT _ _) = ConsD Skip Skip

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

instance ReprDemand a => ReprDemand [a]

instance ReprDemandArb a => ReprDemandArb [a]

-- =============================================================================

-- Fully strict variant

newtype SList a = SList [a]
    deriving (Eq, Show)
    -- deriving (Eq, Show, Foldable, Functor, Applicative, Monad)

fromSList :: SList a -> [a]
fromSList (SList l) = l

instance Arbitrary a => Arbitrary (SList a) where
    arbitrary = SList <$> arbitrary
    shrink = map SList . shrink . fromSList

instance Repr a => Repr (SList a) where
    type Rep (SList a) = [Rep a]
    reprM (SList l) = mapM reprM l
    abstract = SList . map abstract

instance Demand a => Demand [a] where
    type Dem [a] = [Dem a]
    fullDemand = map fullDemand
    usage xs ds = foldr union empty $ zipWith usage xs ds

instance LBoundDemand a => LBoundDemand [a] where
    minDemand = map minDemand

instance DemandArb a => DemandArb [a] where
    arbDemandFrom = mapM arbDemandFrom

instance ReprDemand a => ReprDemand (SList a)

instance ReprDemandArb a => ReprDemandArb (SList a)
