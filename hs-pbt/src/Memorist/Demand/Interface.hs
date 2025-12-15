{-# LANGUAGE TypeFamilies, FlexibleContexts #-}
-- {-# LANGUAGE MultiParamTypeClasses #-}

module Memorist.Demand.Interface where

-- import Memorist.Core.Core
import Memorist.CoreF.Core
import Memorist.Data.Interface
import Data.Set as S
import Control.Monad (liftM)
import Test.QuickCheck (Gen, Arbitrary (..), Arbitrary1 (..), arbitrary1, shrink1, frequency )


data ThD a = Need a | Skip
    deriving (Eq, Show)

{-
class Demand a b where
    -- final context
    usage :: AnnotCntx -> a -> b -> USet
    usage _ _ _ = S.empty

instance Demand a b => Demand (Th a) (ThD b) where
    usage ac (Th i x) (Need d) = mapSu ac i `union` usage ac x d
    usage _  _        Skip     = S.empty

instance Demand () ()
instance Demand Bool Bool
instance Demand Int Int

class (Repr a, Demand (Rep a) b) => ReprDemand a b where
    -- initial context
    usageR :: AnnotCntx -> a -> b -> USet
    usageR ac x = usage ac' (value r)
        where (r, ac') = run (reprM x) ac

instance ReprDemand () ()
instance ReprDemand Bool Bool
instance ReprDemand Int Int

-- instance ReprDemand a b => ReprDemand a (ThD b)
-}

-- Defined over Memorist transformed type (the one with named thunks)
class Demand a where
    type Dem a
    -- final context
    usage :: AnnotCntx -> a -> Dem a -> USet
    usage _ _ _ = S.empty

instance Demand a => Demand (Th a) where
    type Dem (Th a) = ThD (Dem a)

    usage ac (Th i x) (Need d) = mapSu ac i `union` usage ac x d
    usage _  _        Skip     = S.empty

instance Demand () where
    type Dem () = ()

instance Demand Bool where
    type Dem Bool = Bool

instance Demand Int where
    type Dem Int = Int


{-
-- Not needed atm

class (Repr a, Demand (Rep a)) => ReprDemand a where
    -- initial context
    usageR :: AnnotCntx -> a -> (Dem (Rep a)) -> USet
    usageR ac x = usage ac' (value r)
        where (r, ac') = run (reprM x) ac

instance ReprDemand ()
instance ReprDemand Bool
instance ReprDemand Int
-}


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

-- It will be useful to generate random demand on a given value

{-
class Demand a b => DemandArb a b where
    arbDemandFrom :: a -> Gen b

instance DemandArb () () where
    arbDemandFrom = return

instance DemandArb Bool Bool where
    arbDemandFrom = return

instance DemandArb Int Int where
    arbDemandFrom = return

instance DemandArb a b => DemandArb (Th a) (ThD b) where
    arbDemandFrom (Th _ x) = do
        x' <- arbDemandFrom x
        arbitraryWrap x'

-- class (ReprDemand a b, DemandArb (Rep a) b) => ArbReprDemand a b where
    -- arbDemandFromRepr :: a -> Gen b
    -- arbDemandFromRepr x = arbDemandFrom $ evalValue (reprM x) A.empty

-- instance ArbReprDemand () ()
-- instance ArbReprDemand Bool Bool
-- instance ArbReprDemand Int Int

-- Below: always run the M monad on A.empty (empty annotation context) based
-- on the assumption that the demand type abstract away names, so that
-- exact contexts do not matter.

arbDemandFromRepr :: (ReprDemand a b, DemandArb (Rep a) b) => a -> Gen b
arbDemandFromRepr x = arbDemandFrom $ evalValue (reprM x) A.empty

arbDemandM :: DemandArb a b => M a -> Gen b
arbDemandM m = arbDemandFrom $ evalValue m A.empty
-}

-- Demand type with QC generators defined.
-- Defined over Memorist transformed type (the one with named thunks).
-- Requires Show typeclass since types of this class can directly interact with QC.
class (Demand a, Show (Dem a)) => DemandArb a where
    arbDemandFrom :: a -> Gen (Dem a)

instance DemandArb () where
    arbDemandFrom = return

instance DemandArb Bool where
    arbDemandFrom = return

instance DemandArb Int where
    arbDemandFrom = return

instance DemandArb a => DemandArb (Th a) where
    arbDemandFrom (Th _ x) = do
        x' <- arbDemandFrom x
        arbitraryWrap x'

arbDemandM :: (DemandArb a) => M a -> Gen (Dem a)
arbDemandM m = arbDemandFrom $ evalValue m emptyCntx

-- Ordinary Haskell type with Memorist representation, the latter of which
-- also has an associated demand type that has QC generators defined.
class (Repr a, DemandArb (Rep a)) => ReprDemandArb a

instance ReprDemandArb ()
instance ReprDemandArb Bool
instance ReprDemandArb Int

arbDemandFromRepr :: ReprDemandArb a => a -> Gen (Dem (Rep a))
arbDemandFromRepr x = arbDemandFrom $ evalValue (reprM x) emptyCntx

