module Memorist.Example.Append where

import Memorist.Core.Annotation
import Memorist.Core.Thunk
import Memorist.Core.Semantics
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

appendM_fromPure :: Repr a => [a] -> [a] -> M (ListT (Rep a))
appendM_fromPure xs ys =
    lazybind (reprM xs) $ \txs ->
        lazybind (reprM ys) $ \tys ->
            appendM txs tys

cost_appendM :: Repr a => [a] -> [a] -> Int -> Cost
cost_appendM xs ys n = infcost' r u ac
    where ac = []
          r = appendM_fromPure xs ys ac
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
cost_ex = cost_appendM ex_xs ex_ys


genResultUsage :: QC.Arbitrary a => [a] -> [a] -> QC.Gen Int
genResultUsage xs ys = QC.elements [0..len']
    where len = length xs + length ys - 1
          len' = max 0 len

prop_costbound :: (Repr a, QC.Arbitrary a) => [a] -> [a] -> QC.Property
prop_costbound xs ys = QC.forAll (genResultUsage xs ys) $ \n ->
    cost_appendM xs ys n <= max n (length xs + 1)

-- To actually QuickCheck this property we need to provide a concrete type.
-- This is due to QuickCheck itself, not an issue of the translation.
qc_example :: IO ()
qc_example = QC.quickCheck (prop_costbound :: [Int] -> [Int] -> QC.Property)
