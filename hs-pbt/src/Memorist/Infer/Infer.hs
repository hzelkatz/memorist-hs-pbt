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


-- upperbound :: (DemandArb a, Integral n) => MemoristM a -> (Dem a -> n) -> QC.Property
upperbound :: (Memorist s m, DemandArb a, Integral n) => m a -> (Dem a -> n) -> QC.Property
upperbound m f = QC.forAll (arbDemandM m) $ \d ->
     MT.toInteger (infcost' m d) <= Prelude.toInteger (f d)
