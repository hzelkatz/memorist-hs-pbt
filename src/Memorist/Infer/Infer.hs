module Memorist.Infer.Infer where

import Memorist.Base.Thunk as MT
import Memorist.Base.Core
import Memorist.Data.Interface
import qualified Test.QuickCheck as QC


infcost :: (Demand a, Memorist s m) => m a -> (a -> Dem a) -> Cost
infcost m df = calcCost r $ df $ value r
    where r = eval m initstate

infcost' :: (Demand a, Memorist s m) => m a -> Dem a -> Cost
infcost' m = calcCost $ eval m initstate

calcCost :: Demand a => Annotated a -> Dem a -> Cost
calcCost x d = sumcost s `cplus` costAnnot x
    where s = usage (value x) d `union` usageAnnot x


-- The interface allows one to specify the cost bound in terms of result and demand
-- as well.
-- But for results, one works directly with the pure type instead of the Memorist types
-- directly computed from running the monad.
forAllDemand :: (QC.Testable prop, ReprDemandArb a, Memorist s m) =>
    m (Rep a) -> (a -> Dem (Rep a) -> Cost -> prop) -> QC.Property
forAllDemand m = forAllDemandSt m initstate

forAllDemandSt :: (QC.Testable prop, ReprDemandArb a, Memorist s m) =>
    m (Rep a) -> s -> (a -> Dem (Rep a) -> Cost -> prop) -> QC.Property
forAllDemandSt m st pf = forAllDemand' res $ pf $ abstract $ value res
    where res = eval m st

forAllDemand' :: (QC.Testable prop, DemandArb a) =>
    Annotated a -> (Dem a -> Cost -> prop) -> QC.Property
forAllDemand' x pf = QC.forAll (arbDemandFrom (value x)) pf'
    where pf' d = pf d $ calcCost x d


-- We define a series of combinators and helpers that work directly on Annotated
-- values and/or concrete demand, so that we can avoid running the monad more than once.

-- | A property specifying the upper bound of cost with specific demand.
upperboundWith :: (Demand a, Real n, Show n, Memorist s m) =>
    m a -> (a -> Dem a) -> (a -> Dem a -> n) -> QC.Property
upperboundWith = compSpecWithDemandBy (<=)

-- | A property specifying the upper bound of cost under all possible demand on the resulting value.
upperboundby :: (DemandArb a, Real n, Show n, Memorist s m) =>
    m a -> (a -> Dem a -> n) -> QC.Property
upperboundby = compSpecAllDemandBy (<=)

-- | A property specifying the lower bound of cost with specific demand.
lowerboundWith :: (Demand a, Real n, Show n, Memorist s m) =>
    m a -> (a -> Dem a) -> (a -> Dem a -> n) -> QC.Property
lowerboundWith = compSpecWithDemandBy (>=)

-- | A property specifying the lower bound of cost under all possible demand on the resulting value.
lowerboundby :: (DemandArb a, Real n, Show n, Memorist s m) =>
    m a -> (a -> Dem a -> n) -> QC.Property
lowerboundby = compSpecAllDemandBy (>=)

-- | A property specifying the cost under the specific demand exactly equals to
-- the given cost description.
exactlyWith :: (Demand a, Integral n, Show n, Memorist s m) =>
    m a -> (a -> Dem a) -> (a -> Dem a -> n) -> QC.Property
exactlyWith = compSpecWithDemandBy (==)

-- | A variant of 'exactly' where the cost property is not specified in
-- terms of the output value.
exactly :: (DemandArb a, Integral n, Show n, Memorist s m) =>
    m a -> (a -> Dem a -> n) -> QC.Property
exactly = compSpecAllDemandBy (==)


-- Helpers.

compSpecWithDemandBy :: (Demand a, Memorist s m, Num n, Show n) =>
    (n -> n -> Bool) -> m a -> (a -> Dem a) -> (a -> Dem a -> n) -> QC.Property
compSpecWithDemandBy comp m df pf = compSpecWithDemandBy' comp res d $ pf v
    where res = eval m initstate
          v = value res
          d = df v

-- Given an annotated value x, a demand d on x, and a cost function pf
-- in terms of (pure) value v and the demand d,
-- compare the derived computation cost against the cost description
-- constructed using pf, using the comparator `comp`.
compSpecWithDemandBy' :: (Demand a, Num n, Show n) =>
    (n -> n -> Bool) -> Annotated a -> Dem a -> (Dem a -> n) -> QC.Property
compSpecWithDemandBy' comp x d pf = compareCostTo comp c $ pf d
    where c = calcCost x d

compSpecAllDemandBy :: (DemandArb a, Memorist s m, Num n, Show n) =>
    (n -> n -> Bool) -> m a -> (a -> Dem a -> n) -> QC.Property
compSpecAllDemandBy comp m pf = compSpecAllDemandBy' comp res $ pf $ value res
    where res = eval m initstate

-- Given an annotated value x, and a cost function pf in terms of (pure) value
-- and demand, compare the derived computation cost against the cost description
-- constructed using pf, using the comparator `comp`.
-- That is, it is a generalization of 'compSpecWithDemandBy' to
-- any possible demand on the value resluting from running the computation.
compSpecAllDemandBy' :: (DemandArb a, Num n, Show n) =>
    (n -> n -> Bool) -> Annotated a -> (Dem a -> n) -> QC.Property
compSpecAllDemandBy' comp x pf =
    forAllDemand' x $ \d c -> compareCostTo comp c $ pf d

compareCostTo :: (Num n, Show n) => (n -> n -> Bool) -> Cost -> n -> QC.Property
compareCostTo comp c pc =
    QC.counterexample ("Computed cost: " ++ showInteger c ++ "; Expected: " ++ show pc) $
    compCost comp c pc

compCost :: Num n => (n -> n -> Bool) -> Cost -> n -> Bool 
compCost comp c pc = fromIntegral (MT.toInteger c) `comp` pc


-- -----------------------------------------------------------------------------

-- | Combinator for functional correctness
correct :: (Eq a, Repr a) => Memorist s m => m (Rep a) -> a -> Bool
correct m x = abstract (value (eval m initstate)) == x
