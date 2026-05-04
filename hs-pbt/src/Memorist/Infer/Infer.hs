module Memorist.Infer.Infer where

import Memorist.Base.Thunk as MT
import Memorist.Base.Core
import Memorist.Data.Interface
import qualified Test.QuickCheck as QC


-- Takes the annotated value with output annotation and a usage set containing
-- names of thunks demanded in the value.
calcCost :: Annotated a -> USet -> Cost
calcCost x u = sumcost s `cplus` costAnnot x
    where s = u `union` usageAnnot x

calcCostD :: Demand a => Annotated a -> Dem a -> Cost
calcCostD x d = calcCost x $ usage (value x) d

infcost :: (Demand a, Memorist s m) => m a -> (a -> Dem a) -> Cost
infcost m = infcostSt m initstate

infcostSt :: (Demand a, Memorist s m) => m a -> s -> (a -> Dem a) -> Cost
infcostSt m st df = calcCostD r $ df $ value r
    where r = eval m st

infcostSt' :: (Demand a, Memorist s m) => m a -> s -> Dem a -> Cost
infcostSt' m st d = calcCostD (eval m st) d


{-
infcostFromPure1 :: (Memorist s m, Repr a, Demand b) =>
    (Th (Rep a) -> m b) -> a -> Dem b -> Cost
infcostFromPure1 fM x = infcost (fromPure1 fM x)

infcostFromPure1St :: (Memorist s m, Repr a, Demand b) =>
    (Th (Rep a) -> m b) -> a -> s -> Dem b -> Cost
infcostFromPure1St fM x = infcostSt (fromPure1 fM x)

infcostFromPure2' :: (Memorist s m, Repr a, Repr b, Demand c) =>
    (Th (Rep a) -> Th (Rep b) -> m c) -> a -> b -> Dem c -> Cost
infcostFromPure2' fM x y = infcost (fromPure2 fM x y)

infcostFromPure2St :: (Memorist s m, Repr a, Repr b, Demand c) =>
    (Th (Rep a) -> Th (Rep b) -> m c) -> a -> b -> s -> Dem c -> Cost
infcostFromPure2St fM x y = infcostSt (fromPure2 fM x y)
-}

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
    where pf' d = pf d $ calcCostD x d

-- We define a series of combinators and helpers that work directly on Annotated
-- values and/or concrete demand, so that we can avoid running the monad more than once.

-- | A property specifying the upper bound of cost with specific demand.
upperboundWith :: (Demand a, Real n, Memorist s m) =>
    m a -> (a -> Dem a) -> (a -> Dem a -> n) -> Bool
upperboundWith m = upperboundWithSt m initstate

-- | A property specifying the upper bound of cost with specific demand.
-- The St variant runs the monad on the given initial state.
upperboundWithSt :: (Demand a, Real n, Memorist s m) =>
    m a -> s -> (a -> Dem a) -> (a -> Dem a -> n) -> Bool
upperboundWithSt = compSpecWithDemandBySt (<=)

-- | A property specifying the upper bound of cost under all possible demand on the resulting value.
upperboundby :: (DemandArb a, Real n, Memorist s m) =>
    m a -> (a -> Dem a -> n) -> QC.Property
upperboundby m = upperboundbySt m initstate

upperboundbySt :: (DemandArb a, Real n, Memorist s m) =>
    m a -> s -> (a -> Dem a -> n) -> QC.Property
upperboundbySt = compSpecAllDemandBySt (<=)

-- | A property specifying the ;pwer bound of cost with specific demand.
lowerboundWith :: (Demand a, Real n, Memorist s m) =>
    m a -> (a -> Dem a) -> (a -> Dem a -> n) -> Bool
lowerboundWith m = lowerboundWithSt m initstate

lowerboundWithSt :: (Demand a, Real n, Memorist s m) =>
    m a -> s -> (a -> Dem a) -> (a -> Dem a -> n) -> Bool
lowerboundWithSt = compSpecWithDemandBySt (<=)

-- | A property specifying the lower bound of cost under all possible demand on the resulting value.
lowerboundby :: (DemandArb a, Real n, Memorist s m) =>
    m a -> (a -> Dem a -> n) -> QC.Property
lowerboundby m = lowerboundbySt m initstate

lowerboundbySt :: (DemandArb a, Real n, Memorist s m) =>
    m a -> s -> (a -> Dem a -> n) -> QC.Property
lowerboundbySt = compSpecAllDemandBySt (<=)

-- | A property specifying the cost under the specific demand exactly equals to
-- the given cost description.
exactlyWith :: (Demand a, Real n, Memorist s m) =>
    m a -> (a -> Dem a) -> (a ->Dem a -> n) -> Bool
exactlyWith m = exactlyWithSt m initstate

exactlyWithSt :: (Demand a, Real n, Memorist s m) =>
    m a -> s -> (a -> Dem a) -> (a -> Dem a -> n) -> Bool
exactlyWithSt = compSpecWithDemandBySt (==)

-- | A variant of 'exactly' where the cost property is not specified in
-- terms of the output value.
exactly :: (DemandArb a, Integral n, Memorist s m) =>
    m a -> (a -> Dem a -> n) -> QC.Property
exactly m = exactlySt m initstate

-- | A property specifying the cost under all possible demand on the resulting
-- value exactly equals to the given cost description.
exactlySt :: (DemandArb a, Integral n, Memorist s m) =>
    m a -> s -> (a -> Dem a -> n) -> QC.Property
exactlySt = compSpecAllDemandBySt (==)


-- The variants below take the pure output values instead of their Memorist
-- representaion as an input.
-- 
-- FIXME: do not work well in practice due to issues with typing.

-- | A variant of 'upperboundWith' where the cost property takes the pure output
-- value instead of its Memorist representation as an argument.
upperboundWith' :: (ReprDemand a, Real n, Memorist s m) =>
    m (Rep a) -> (Rep a -> Dem (Rep a)) -> (a -> Dem (Rep a) -> n) -> Bool
upperboundWith' m = upperboundWithSt' m initstate

upperboundWithSt' :: (ReprDemand a, Real n, Memorist s m) =>
    m (Rep a) -> s -> (Rep a -> Dem (Rep a)) -> (a -> Dem (Rep a) -> n) -> Bool
upperboundWithSt' = compSpecWithDemandBySt' (<=)

-- upperboundby' :: (ReprDemandArb a, Real n, Memorist s m) =>
--     m (Rep a) -> (a -> Dem (Rep a) -> n) -> QC.Property
upperboundby' :: (Repr a, DemandArb a1, a1 ~ Rep a, a2 ~ Dem a1, Real n, Memorist s m) =>
    m a1 -> (a -> a2 -> n) -> QC.Property
upperboundby' m = upperboundbySt' m initstate

-- upperboundbySt' :: (ReprDemandArb a, Real n, Memorist s m) =>
--     m (Rep a) -> s -> (a -> Dem (Rep a) -> n) -> QC.Property
upperboundbySt' :: (Repr a, DemandArb a1, a1 ~ Rep a, a2 ~ Dem a1, Real n, Memorist s m) =>
    m a1 -> s -> (a -> a2 -> n) -> QC.Property
upperboundbySt' = compSpecAllDemandBySt' (<=)

-- | A property specifying the lower bound of cost with specific demand.
lowerboundWith' :: (ReprDemand a, Real n, Memorist s m) =>
    m (Rep a) -> (Rep a -> Dem (Rep a)) -> (a -> Dem (Rep a) -> n) -> Bool
lowerboundWith' m = lowerboundWithSt' m initstate

lowerboundWithSt' :: (ReprDemand a, Real n, Memorist s m) =>
    m (Rep a) -> s -> (Rep a -> Dem (Rep a)) -> (a -> Dem (Rep a) -> n) -> Bool
lowerboundWithSt' = compSpecWithDemandBySt' (>=)

-- | A property specifying the lower bound of cost under all possible demand on the resulting value.
-- lowerboundby' :: (ReprDemandArb a, Real n, Memorist s m) =>
--     m (Rep a) -> (a -> Dem (Rep a) -> n) -> QC.Property
lowerboundby' :: (Repr a, DemandArb a1, a1 ~ Rep a, a2 ~ Dem a1, Real n, Memorist s m) =>
    m a1 -> (a -> a2 -> n) -> QC.Property
lowerboundby' m = lowerboundbySt' m initstate

-- lowerboundbySt' :: (ReprDemandArb a, Real n, Memorist s m) =>
--     m (Rep a) -> s -> (a -> Dem (Rep a) -> n) -> QC.Property
lowerboundbySt' :: (Repr a, DemandArb a1, a1 ~ Rep a, a2 ~ Dem a1, Real n, Memorist s m) =>
    m a1 -> s -> (a -> a2 -> n) -> QC.Property
lowerboundbySt' = compSpecAllDemandBySt' (>=)

-- exactlyWith' :: (ReprDemand a, Integral n, Memorist s m) =>
--     m (Rep a) -> (Rep a -> Dem (Rep a)) -> (a -> Dem (Rep a) -> n) -> Bool
exactlyWith' :: (Repr a, Demand a', a' ~ Rep a, Integral n, Memorist s m) =>
    m a' -> (a' -> Dem a') -> (a -> Dem a' -> n) -> Bool
exactlyWith' m = exactlyWithSt' m initstate

-- exactlyWithSt' :: (ReprDemand a, Integral n, Memorist s m) =>
--     m (Rep a) -> s -> (Rep a -> Dem (Rep a)) -> (a -> Dem (Rep a) -> n) -> Bool
exactlyWithSt' :: (Repr a, Demand a1, a1 ~ Rep a, a2 ~ Dem a1, Integral n, Memorist s m) =>
    m a1 -> s -> (a1 -> a2) -> (a -> a2 -> n) -> Bool
exactlyWithSt' = compSpecWithDemandBySt' (==)

exactly' :: (Repr a, DemandArb a1, a1 ~ Rep a, a2 ~ Dem a1, Integral n, Memorist s m) =>
    m a1 -> (a -> a2 -> n) -> QC.Property
exactly' m = exactlySt' m initstate

-- exactlySt' :: (ReprDemandArb a, Integral n, Memorist s m) =>
--     m (Rep a) -> s -> (a -> Dem (Rep a) -> n) -> QC.Property
exactlySt' :: (Repr a, DemandArb a1, a1 ~ Rep a, a2 ~ Dem a1, Integral n, Memorist s m) =>
    m a1 -> s -> (a -> a2 -> n) -> QC.Property
exactlySt' = compSpecAllDemandBySt' (==)


-- Only meaningful if the two programs produces the same pure value on same input.
-- Demand is generated based on the result of the first program.
compareOnSame :: (Memorist s m, DemandArb a) =>
    m a -> m a -> (Integer -> Integer -> Bool) -> QC.Property
compareOnSame m m' = compareOnSameSt m m' initstate

compareOnSameSt :: (Memorist s m, DemandArb a) =>
    m a -> m a -> s -> (Integer -> Integer -> Bool) -> QC.Property
compareOnSameSt m m' st comp =
    compSpecAllDemandBy comp (eval m st) $ \d -> MT.toInteger $ infcostSt' m' st d


-- Helpers.

-- Given an annotated value x, a demand d on x, and a cost function pf
-- in terms of (pure) value v and the demand d,
-- compare the derived computation cost against the cost description
-- constructed using pf, using the comparator `comp`.
compSpecWithDemandBy :: (Demand a, Num n) =>
    (n -> n -> Bool) -> Annotated a -> Dem a -> (Dem a -> n) -> Bool
compSpecWithDemandBy comp x d pf = compareCost' comp c $ pf d
    where c = calcCostD x d

-- Version of 'compSpecWithDemandBySt' where the cost description ignores resulting value.
compSpecWithDemandBySt :: (Demand a, Num n, Memorist s m) =>
    (n -> n -> Bool) -> m a -> s -> (a -> Dem a) -> (a -> Dem a -> n) -> Bool
compSpecWithDemandBySt comp m st df pf = compSpecWithDemandBy comp res d $ pf v
    where res = eval m st
          v = value res
          d = df $ value res

compSpecWithDemandBySt' :: (Repr a, Demand a1, a1 ~ Rep a, a2 ~ Dem a1, Real n, Memorist s m) =>
    (n -> n -> Bool) -> m a1 -> s -> (a1 -> a2) -> (a -> a2 -> n) -> Bool
compSpecWithDemandBySt' comp m st df pf = compSpecWithDemandBy comp res d $ pf v
    where res = eval m st
          v = abstract $ value res
          d = df $ value res


-- Given an annotated value x, and a cost function pf in terms of (pure) value
-- and demand, compare the derived computation cost against the cost description
-- constructed using pf, using the comparator `comp`.
-- That is, it is a generalization of 'compSpecWithDemandBy' to
-- any possible demand on the value resluting from running the computation.
compSpecAllDemandBy :: (DemandArb a, Num n) =>
    (n -> n -> Bool) -> Annotated a -> (Dem a -> n) -> QC.Property
compSpecAllDemandBy comp x pf =
    forAllDemand' x $ \d c -> compareCost' comp c $ pf d

-- Version of 'compSpecAllDemandBySt' where the cost description ignores resulting value.
compSpecAllDemandBySt :: (DemandArb a, Real n, Memorist s m) =>
    (n -> n -> Bool) -> m a -> s -> (a -> Dem a -> n) -> QC.Property
compSpecAllDemandBySt comp m st pf = compSpecAllDemandBy comp res $ pf $ value res
    where res = eval m st

-- compSpecAllDemandBySt' :: (ReprDemandArb a, Real n, Memorist s m) =>
--     (n -> n -> Bool) -> m (Rep a) -> s -> (a -> Dem (Rep a) -> n) -> QC.Property
compSpecAllDemandBySt' :: (Repr a, DemandArb a1, a1 ~ Rep a, a2 ~ Dem a1, Real n, Memorist s m) =>
    (n -> n -> Bool) -> m a1 -> s -> (a -> a2 -> n) -> QC.Property
compSpecAllDemandBySt' comp m st pf = compSpecAllDemandBy comp res $ pf v
    where res = eval m st
          v = abstract $ value res

compareCost' :: Num n => (n -> n -> Bool) -> Cost -> n -> Bool 
compareCost' comp c pc = fromIntegral (MT.toInteger c) `comp` pc

-- -----------------------------------------------------------------------------

quickCheckN :: QC.Testable prop => Int -> prop -> IO ()
quickCheckN n = QC.quickCheckWith QC.stdArgs { QC.maxSuccess = n }
