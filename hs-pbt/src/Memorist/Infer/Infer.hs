module Memorist.Infer.Infer where

import Memorist.Base.Thunk as MT
import Memorist.Base.Core
import Memorist.Data.Interface
import qualified Test.QuickCheck as QC


infcost_ :: Annotated a -> USet -> Cost
infcost_ r u = sumcost s `cplus` costAnnot r
    where s = u `union` usageAnnot r

infcost :: (Memorist s m, Demand a) => m a -> Dem a -> s -> Cost
infcost m d st = extract $ eval m st
    where extract r = infcost_ r $ usage (value r) d

infcost' :: (Memorist s m, Demand a) => m a -> Dem a -> Cost
infcost' m d = infcost m d initstate

infcostFromPure1 :: (Memorist s m, Repr a, Demand b) =>
    (Th (Rep a) -> m b) -> a -> Dem b -> s -> Cost
infcostFromPure1 fM x = infcost m where m = fromPure1 fM x

infcostFromPure1' :: (Memorist s m, Repr a, Demand b) =>
    (Th (Rep a) -> m b) -> a -> Dem b -> Cost
infcostFromPure1' fM x d = infcostFromPure1 fM x d $ initstate

infcostFromPure2 :: (Memorist s m, Repr a, Repr b, Demand c) =>
    (Th (Rep a) -> Th (Rep b) -> m c) -> a -> b -> Dem c -> s -> Cost
infcostFromPure2 fM x y = infcost m where m = fromPure2 fM x y

infcostFromPure2' :: (Memorist s m, Repr a, Repr b, Demand c) =>
    (Th (Rep a) -> Th (Rep b) -> m c) -> a -> b -> Dem c -> Cost
infcostFromPure2' fM x y d = infcostFromPure2 fM x y d $ initstate


upperboundbyR :: (Memorist s m, DemandArb a, Real n) => m a -> (Dem a -> n) -> QC.Property
upperboundbyR m f = QC.forAll (arbDemandM m) $ \d ->
     fromIntegral (MT.toInteger (infcost' m d)) <= f d

lowerboundbyR :: (Memorist s m, DemandArb a, Real n) => m a -> (Dem a -> n) -> QC.Property
lowerboundbyR m f = QC.forAll (arbDemandM m) $ \d ->
     f d <= fromIntegral (MT.toInteger (infcost' m d))

-- The two below specialize to Integral.

upperboundby :: (Memorist s m, DemandArb a, Integral n) => m a -> (Dem a -> n) -> QC.Property
upperboundby = upperboundbyR

lowerboundby :: (Memorist s m, DemandArb a, Integral n) => m a -> (Dem a -> n) -> QC.Property
lowerboundby = lowerboundbyR

exactly :: (Memorist s m, DemandArb a, Integral n) => m a -> (Dem a -> n) -> QC.Property
exactly m f = QC.forAll (arbDemandM m) $ \d ->
     fromIntegral (MT.toInteger (infcost' m d)) == f d

-- Only meaningful if the two programs produces the same pure value on same input.
-- Demand is generated based on the result of the first program.
compareOnSame :: (Memorist s m, DemandArb a) => m a -> m a -> (Integer -> Integer -> Bool) -> QC.Property
compareOnSame m m' f = QC.forAll (arbDemandM m) $ \d ->
    f (MT.toInteger (infcost' m d)) (MT.toInteger (infcost' m' d))

-- TODO: also a variant of compareOnSame but with a guard (perhaps using conjunction?)
-- to ensure that the computed values from the two programs are the same
-- modulo names? To handle potentially nonterminating computation, may be we only
-- check up to demanded portion. But this would slow down the process as we'd
-- need to do this check for every generated demand.
-- Alternatively a dedicated interface for these kinds of check.


quickCheckN :: QC.Testable prop => Int -> prop -> IO ()
quickCheckN n = QC.quickCheckWith QC.stdArgs { QC.maxSuccess = n }
