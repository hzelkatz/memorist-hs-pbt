module Memorist.Infer.Infer where

import Memorist.Base.Thunk as MT
import Memorist.Base.Core
import Memorist.Data.Interface
import qualified Test.QuickCheck as QC


-- TODO: version that counts "freshed"; but need to fix the efficiency issue with name comparison first

infcost :: (Demand a, Memorist s m) => m a -> (a -> Dem a) -> Cost
infcost m df = calcCost r $ df $ value r
    where r = eval m initstate

infcost' :: (Demand a, Memorist s m) => m a -> Dem a -> Cost
infcost' m = calcCost $ eval m initstate

calcCost :: Demand a => Annotated a -> Dem a -> Cost
calcCost x d = sumcost s `cplus` costAnnot x
    where s = usage (value x) d `union` usageAnnot x


-- TODO: it seems we only used forAllDemand'.
-- I'm using its defintion but with the name "forAllDemand" in paper right now;
-- remove the non-used version and update the name here if confirmed.

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

-- | A property specifying the upper bound of cost with specific demand.
-- The St variant runs the monad on the given initial state.
-- upperboundWithSt :: (Demand a, Real n, Memorist s m) =>
--     m a -> s -> (a -> Dem a) -> (a -> Dem a -> n) -> Bool
-- upperboundWithSt = compSpecWithDemandBySt (<=)

-- | A property specifying the upper bound of cost under all possible demand on the resulting value.
upperboundby :: (DemandArb a, Real n, Show n, Memorist s m) =>
    m a -> (a -> Dem a -> n) -> QC.Property
upperboundby = compSpecAllDemandBy (<=)

-- upperboundbySt :: (DemandArb a, Real n, Memorist s m) =>
--     m a -> s -> (a -> Dem a -> n) -> QC.Property
-- upperboundbySt = compSpecAllDemandBySt (<=)

-- | A property specifying the lower bound of cost with specific demand.
lowerboundWith :: (Demand a, Real n, Show n, Memorist s m) =>
    m a -> (a -> Dem a) -> (a -> Dem a -> n) -> QC.Property
lowerboundWith = compSpecWithDemandBy (>=)

-- lowerboundWithSt :: (Demand a, Real n, Memorist s m) =>
--     m a -> s -> (a -> Dem a) -> (a -> Dem a -> n) -> Bool
-- lowerboundWithSt = compSpecWithDemandBySt (>=)

-- | A property specifying the lower bound of cost under all possible demand on the resulting value.
lowerboundby :: (DemandArb a, Real n, Show n, Memorist s m) =>
    m a -> (a -> Dem a -> n) -> QC.Property
lowerboundby = compSpecAllDemandBy (>=)

-- lowerboundbySt :: (DemandArb a, Real n, Memorist s m) =>
--     m a -> s -> (a -> Dem a -> n) -> QC.Property
-- lowerboundbySt = compSpecAllDemandBySt (>=)

-- | A property specifying the cost under the specific demand exactly equals to
-- the given cost description.
exactlyWith :: (Demand a, Integral n, Show n, Memorist s m) =>
    m a -> (a -> Dem a) -> (a -> Dem a -> n) -> QC.Property
exactlyWith = compSpecWithDemandBy (==)

-- exactlyWithSt :: (Demand a, Real n, Memorist s m) =>
--     m a -> s -> (a -> Dem a) -> (a -> Dem a -> n) -> Bool
-- exactlyWithSt = compSpecWithDemandBySt (==)

-- | A variant of 'exactly' where the cost property is not specified in
-- terms of the output value.
exactly :: (DemandArb a, Integral n, Show n, Memorist s m) =>
    m a -> (a -> Dem a -> n) -> QC.Property
exactly = compSpecAllDemandBy (==)

-- -- | A property specifying the cost under all possible demand on the resulting
-- -- value exactly equals to the given cost description.
-- exactlySt :: (DemandArb a, Integral n, Memorist s m) =>
--     m a -> s -> (a -> Dem a -> n) -> QC.Property
-- exactlySt = compSpecAllDemandBySt (==)


-- Only meaningful if the two programs produces the same pure value on same input.
-- Demand is generated based on the result of the first program.
compareOnSame :: (Memorist s m, DemandArb a) =>
    m a -> m a -> (Integer -> Integer -> Bool) -> QC.Property
compareOnSame m m' comp =
    compSpecAllDemandBy comp m $ \_ d -> MT.toInteger $ infcost' m' d


-- Helpers.

compSpecWithDemandBy :: (Demand a, Memorist s m, Num n, Show n) =>
    (n -> n -> Bool) -> m a -> (a -> Dem a) -> (a -> Dem a -> n) -> QC.Property
compSpecWithDemandBy comp m df pf = compSpecWithDemandBy' comp res d $ pf v
    where res = eval m initstate
          v = value res
          d = df v

-- -- Version of 'compSpecWithDemandBySt' where the cost description ignores resulting value.
-- compSpecWithDemandBySt :: (Demand a, Num n, Memorist s m) =>
--     (n -> n -> Bool) -> m a -> s -> (a -> Dem a) -> (a -> Dem a -> n) -> Bool
-- compSpecWithDemandBySt comp m st df pf = compSpecWithDemandBy' comp res d $ pf v
--     where res = eval m st
--           v = value res
--           d = df $ value res

-- compSpecWithDemandBySt' :: (Repr a, Demand a1, a1 ~ Rep a, a2 ~ Dem a1, Real n, Memorist s m) =>
--     (n -> n -> Bool) -> m a1 -> s -> (a1 -> a2) -> (a -> a2 -> n) -> Bool
-- compSpecWithDemandBySt' comp m st df pf = compSpecWithDemandBy' comp res d $ pf v
--     where res = eval m st
--           v = abstract $ value res
--           d = df $ value res

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

-- -- Version of 'compSpecAllDemandBySt' where the cost description ignores resulting value.
-- compSpecAllDemandBySt :: (DemandArb a, Real n, Memorist s m) =>
--     (n -> n -> Bool) -> m a -> s -> (a -> Dem a -> n) -> QC.Property
-- compSpecAllDemandBySt comp m st pf = compSpecAllDemandBy' comp res $ pf $ value res
--     where res = eval m st

-- -- compSpecAllDemandBySt' :: (ReprDemandArb a, Real n, Memorist s m) =>
-- --     (n -> n -> Bool) -> m (Rep a) -> s -> (a -> Dem (Rep a) -> n) -> QC.Property
-- compSpecAllDemandBySt' :: (Repr a, DemandArb a1, a1 ~ Rep a, a2 ~ Dem a1, Real n, Memorist s m) =>
--     (n -> n -> Bool) -> m a1 -> s -> (a -> a2 -> n) -> QC.Property
-- compSpecAllDemandBySt' comp m st pf = compSpecAllDemandBy' comp res $ pf v
--     where res = eval m st
--           v = abstract $ value res

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
    QC.counterexample ("Computed cost: " ++ showInteger c ++ "; Intended: " ++ show pc) $
    compCost comp c pc

compCost :: Num n => (n -> n -> Bool) -> Cost -> n -> Bool 
compCost comp c pc = fromIntegral (MT.toInteger c) `comp` pc

