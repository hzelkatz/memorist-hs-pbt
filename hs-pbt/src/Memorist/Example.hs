module Memorist.Example where

import Memorist.Components.Annotation
import Memorist.Components.Thunk
import Memorist.Core
import Memorist.DataT.Data
import Memorist.DataT.List
import qualified Test.QuickCheck as QC


{-
    append [] ys = ys
    append (x:xs) ys = let zs = append xs ys in x:zs
-}
appendM :: Th (ListT a) -> Th (ListT a) -> M (ListT a)
appendM txs tys =
    bind tick $ \_ -> forcing txs $ \xs ->
        case xs of
            NilT -> force tys
            ConsT tx txs' ->
                lazybind (appendM txs' tys) $ \tzs ->
                    ret (ConsT tx tzs)

appendM_fromPure :: Rep a b => [a] -> [a] -> M (ListT b)
appendM_fromPure xs ys =
    lazybind (repM xs) $ \txs -> lazybind (repM ys) $ \tys ->
        appendM txs tys

appendM_fromPure_Int :: [Int] -> [Int] -> M (ListT Int)
appendM_fromPure_Int = appendM_fromPure

-- will be generalised; but the current way of handling Rep does not work like this
-- cost :: Rep a _ => [a] -> [a] -> Int -> Cost
-- cost xs ys n = infcost' r u ac
--     where ac = []
--           r = appendM_fromPure xs ys ac
--           u = usageLC (cntx r) (value r) n

cost_IntList :: [Int] -> [Int] -> Int -> Cost
cost_IntList xs ys n = infcost' r u ac
    where ac = []
          r = appendM_fromPure_Int xs ys ac
          u = usageLC (cntx r) (value r) n

ex_xs, ex_ys :: [Int]
ex_xs = [1,2,3]
ex_ys = [4,5,6]

-- xsM, ysM :: M (ListT Int)
-- xsM = repM ([1,2,3] :: [Int])
-- ysM = repM ([4,5,6] :: [Int])

exampleM :: M (ListT Int)
exampleM = appendM_fromPure ex_xs ex_ys

cost_ex :: Int -> Cost
cost_ex = cost_IntList ex_xs ex_ys


genResultUsage :: QC.Arbitrary a => [a] -> [a] -> QC.Gen Int
genResultUsage xs ys = QC.elements [0..len']
    where len = length xs + length ys - 1
          len' = max 0 len

prop_costbound :: [Int] -> [Int] -> QC.Property
prop_costbound xs ys = QC.forAll (genResultUsage xs ys) $ \n ->
    cost_IntList xs ys n <= length xs + 1

qc_example = QC.quickCheck prop_costbound
