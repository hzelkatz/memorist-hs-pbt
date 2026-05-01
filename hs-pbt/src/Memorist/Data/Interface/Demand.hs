{-# LANGUAGE TypeFamilies, FlexibleContexts #-}

module Memorist.Data.Interface.Demand where

import Memorist.Base.Thunk
import Memorist.Base.Core
import Memorist.Data.Interface.Data
import Control.Monad (liftM, liftM2)
import Test.QuickCheck (Gen, Arbitrary (..), Arbitrary1 (..), Arbitrary2 (..)
                       , arbitrary1, shrink1, arbitrary2, shrink2
                       , frequency )


data ThD a = Need a | Skip
    deriving (Eq, Show)

-- Defined over Memorist transformed type (the one with named thunks)
class Demand a where
    type Dem a

    usage :: a -> Dem a -> USet
    usage _ _ = empty

instance Demand a => Demand (Th a) where
    type Dem (Th a) = ThD (Dem a)

    usage t (Need d) = let (x,s) = useThunk t in s `union` usage x d
    usage _ Skip     = empty

instance Demand () where
    type Dem () = ()

instance Demand Bool where
    type Dem Bool = Bool

instance Demand Int where
    type Dem Int = Int

-- -----------------------------------------------------------------------------

data MaybeD a = JustD (ThD a) | NothingD
    deriving (Eq, Show)

instance Demand a => Demand (MaybeT a) where
    type Dem (MaybeT a) = MaybeD (Dem a)

    fullDemand (JustT x) = JustD $ fullDemand x
    fullDemand _         = NothingD

    usage (JustT x) (JustD dx) = usage x dx
    usage _         _          = empty

instance Demand a => Demand (Maybe a) where
    type Dem (Maybe a) = Maybe (Dem a)

    fullDemand (Just x) = Just $ fullDemand x
    fullDemand _        = Nothing

    usage (Just x) (Just dx) = usage x dx
    usage _         _        = empty


data PairD a b = PairD (ThD a) (ThD b) deriving (Eq,Show)

instance (Demand a, Demand b) => Demand (PairT a b) where
    type Dem (PairT a b) = PairD (Dem a) (Dem b)

    fullDemand (PairT x y) = PairD (fullDemand x) (fullDemand y)

    usage (PairT x y) (PairD dx dy) = usage x dx `union` usage y dy

instance (Demand a, Demand b) => Demand (a,b) where
    type Dem (a,b) = (Dem a, Dem b)

    fullDemand (x,y) = (fullDemand x, fullDemand y)

    usage (x,y) (dx,dy) = usage x dx `union` usage y dy

-- =============================================================================

-- QuickCheck generator for ThD.
-- The definitions are inspired by the official defns for the Maybe type
instance Arbitrary1 ThD where
    liftArbitrary arb = frequency [(1, return Skip), (3, liftM Need arb)]

    liftShrink shr (Need x) = Skip : [ Need x' | x' <- shr x ]
    liftShrink _   Skip     = []

instance Arbitrary a => Arbitrary (ThD a) where
  arbitrary = arbitrary1
  shrink = shrink1

arbitraryWrap :: a -> Gen (ThD a)
arbitraryWrap x = do
    d <- (arbitrary :: Gen (ThD ()))
    return $ case d of
        Need _ -> Need x
        Skip   -> Skip

instance Arbitrary1 MaybeD where
    liftArbitrary arb = frequency [(1, return NothingD), (3, liftM JustD (liftArbitrary arb))]

    liftShrink shr (JustD x) = NothingD : [ JustD x' | x' <- liftShrink shr x ]
    liftShrink _   NothingD  = []

instance Arbitrary a => Arbitrary (MaybeD a) where
    arbitrary = arbitrary1
    shrink = shrink1

instance Arbitrary2 PairD where
    liftArbitrary2 arb1 arb2 = liftM2 PairD (liftArbitrary arb1) (liftArbitrary arb2)

    liftShrink2 shr1 shr2 (PairD x y) =
        [ PairD x' y | x' <- liftShrink shr1 x ] ++
        [ PairD x y' | y' <- liftShrink shr2 y ]

instance Arbitrary a => Arbitrary1 (PairD a) where
    liftArbitrary = liftArbitrary2 arbitrary
    liftShrink = liftShrink2 shrink

instance (Arbitrary a, Arbitrary b) => Arbitrary (PairD a b) where
    arbitrary = arbitrary2
    shrink = shrink2


-- Demand type with QC generators defined.
-- Defined over Memorist transformed type (the one with named thunks).
-- Requires Show typeclass since types of this class can directly interact with QC.
class (Demand a, Arbitrary (Dem a), Show (Dem a)) => DemandArb a where
    arbDemandFrom :: a -> Gen (Dem a)

instance DemandArb () where
    arbDemandFrom = return

instance DemandArb Bool where
    arbDemandFrom = return

instance DemandArb Int where
    arbDemandFrom = return

instance DemandArb a => DemandArb (MaybeT a) where
    arbDemandFrom (JustT x) = liftM JustD $ arbDemandFrom x
    arbDemandFrom _          = return NothingD

instance DemandArb a => DemandArb (Maybe a) where
    arbDemandFrom (Just x) = liftM Just $ arbDemandFrom x
    arbDemandFrom Nothing  = return Nothing

instance (DemandArb a, DemandArb b) => DemandArb (PairT a b) where
    arbDemandFrom (PairT x y) = liftM2 PairD (arbDemandFrom x) (arbDemandFrom y)

instance (DemandArb a, DemandArb b) => DemandArb (a,b) where
    arbDemandFrom (x,y) = liftM2 (,) (arbDemandFrom x) (arbDemandFrom y)

instance DemandArb a => DemandArb (Th a) where
    arbDemandFrom t = do
        x' <- arbDemandFrom $ tval t
        arbitraryWrap x'

arbDemandM :: (Memorist s m, DemandArb a) => m a -> Gen (Dem a)
arbDemandM m = arbDemandFrom $ value $ eval m $ initstate

-- Ordinary Haskell type with Memorist representation, the latter of which
-- also has an associated demand type that has QC generators defined.
class (Repr a, DemandArb (Rep a)) => ReprDemandArb a

instance ReprDemandArb ()
instance ReprDemandArb Bool
instance ReprDemandArb Int
instance ReprDemandArb a => ReprDemandArb (Maybe a)
instance ReprDemandArb a => ReprDemandArb (SMaybe a)
instance (ReprDemandArb a, ReprDemandArb b) => ReprDemandArb (a,b)
instance (ReprDemandArb a, ReprDemandArb b) => ReprDemandArb (SPair a b)


-- FIXME: not definable
--
-- arbDemandFromRepr :: ReprDemandArb a => a -> Gen (Dem (Rep a))
-- arbDemandFromRepr = arbDemandM . reprM
