{-# LANGUAGE TypeFamilies, FlexibleContexts #-}

module Memorist.Data.Interface.Demand where

import Memorist.Base.Thunk
import Memorist.Base.Core
import Memorist.Data.Interface.Data
import Control.Monad (liftM)
import Test.QuickCheck (Gen, Arbitrary (..), Arbitrary1 (..), arbitrary1, shrink1, frequency )


data ThD a = Need a | Skip
    deriving (Eq, Show)


-- Defined over Memorist transformed type (the one with named thunks)
class Demand a where
    type Dem a
    -- final context
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


-- With this approach, we need to also define generators for demand types.

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

instance DemandArb a => DemandArb (Th a) where
    arbDemandFrom (Th _ x _) = do
        x' <- arbDemandFrom x
        arbitraryWrap x'

arbDemandM :: (Memorist s m, DemandArb a) => m a -> Gen (Dem a)
arbDemandM m = arbDemandFrom $ value $ eval m $ initstate

-- Ordinary Haskell type with Memorist representation, the latter of which
-- also has an associated demand type that has QC generators defined.
class (Repr a, DemandArb (Rep a)) => ReprDemandArb a

instance ReprDemandArb ()
instance ReprDemandArb Bool
instance ReprDemandArb Int

-- FIXME: not definable
--
-- arbDemandFromRepr :: ReprDemandArb a => a -> Gen (Dem (Rep a))
-- arbDemandFromRepr = arbDemandM . reprM
