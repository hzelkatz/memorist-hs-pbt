{-# LANGUAGE FlexibleContexts #-}

module Memorist.Example.Append where

import Memorist.Core.Annotation as A
import Memorist.Core.Thunk
import Memorist.Core.Semantics
import Memorist.Data.Interface
import Memorist.Demand.Interface
import Memorist.Data.List
import Memorist.Demand.List
import Memorist.Testing
import qualified Test.QuickCheck as QC


{-
    append [] ys = ys
    append (x:xs) ys = let zs = append xs ys in x:zs
-}
appendM :: Th (ListT a) -> Th (ListT a) -> M (ListT a)
appendM txs tys = do
    tick
    xs <- force txs
    case xs of
        NilT -> force tys
        ConsT tx txs' -> do
            tzs <- lazy (appendM txs' tys)
            ret $ ConsT tx tzs

appendM_fromPure :: Repr a => [a] -> [a] -> M (ListT (Rep a))
appendM_fromPure xs ys = do
    txs <- lazy (reprM xs)
    tys <- lazy (reprM ys)
    appendM txs tys


cost_appendM :: Repr a => [a] -> [a] -> Int -> Cost
-- cost_appendM xs ys n = infcost' (r, ac') u ac
--     where ac = A.empty
--           (r, ac') = run (appendM_fromPure xs ys) ac
--           u = usageLC ac' (value r) n
cost_appendM xs ys n = infcost (appendM_fromPure xs ys) usageLC n ac
    where ac = A.empty

ex_xs, ex_ys :: [Int]
ex_xs = [1,2]
ex_ys = [3,4,5]

exampleM :: M (ListT Int)
exampleM = appendM_fromPure ex_xs ex_ys

cost_ex :: Int -> Cost
cost_ex = cost_appendM ex_xs ex_ys


genResultUsage :: QC.Arbitrary a => [a] -> [a] -> QC.Gen Int
genResultUsage xs ys = QC.elements [0..len']
    where len = length xs + length ys - 1
          len' = max 0 len

prop_costbound :: (Repr a, QC.Arbitrary a) => [a] -> [a] -> QC.Property
prop_costbound xs ys = QC.forAll (genResultUsage xs ys) $ \n ->
    cost_appendM xs ys n <= min n (length xs) + 1

-- To actually QuickCheck this property we need to provide a concrete type.
-- This is due to QuickCheck itself, not an issue of the translation.
qc_example :: IO ()
qc_example = QC.quickCheck (prop_costbound :: [Int] -> [Int] -> QC.Property)


-- Despite more work to do to implement the typeclass instances,
-- using demand type has the benefit of not needing to figure out what are
-- valid demands for each function to be tested
-- (i.e. no need of functions like the `genResultUsage` above).

-- FIXME: this runs the computation twice?
prop_costbound_d :: (ReprDemandArb a, QC.Arbitrary a) => [a] -> [a] -> QC.Property
prop_costbound_d xs ys = QC.forAll (arbDemandM m) $ \d ->
    infcostD0 m d <= min (sizeD 1 d) (length xs + 1)
    where m = appendM_fromPure xs ys

prop_costbound_d' :: (ReprDemandArb a, QC.Arbitrary a) => [a] -> [a] -> QC.Property
prop_costbound_d' xs ys = QC.forAll (arbDemandFrom v) $ \d ->
    infcostD' r d ac <= min (sizeD 1 d) (length xs + 1)
    where ac = A.empty
          r = run (appendM_fromPure xs ys) ac
          v = value $ fst r

-- Testing an incorrect spec
prop_costbound_d_x :: (ReprDemandArb a, QC.Arbitrary a) => [a] -> [a] -> QC.Property
prop_costbound_d_x xs ys = QC.forAll (arbDemandM m) $ \d ->
    infcostD0 m d <= length xs
    where m = appendM_fromPure xs ys

qc_example_d :: IO ()
qc_example_d = QC.quickCheck (prop_costbound_d :: [Int] -> [Int] -> QC.Property)

qc_example_d' :: IO ()
qc_example_d' = QC.quickCheck (prop_costbound_d' :: [Int] -> [Int] -> QC.Property)

qc_example_d_x :: IO ()
qc_example_d_x = QC.quickCheck (prop_costbound_d_x :: [Int] -> [Int] -> QC.Property)
