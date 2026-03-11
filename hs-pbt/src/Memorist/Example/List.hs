module Memorist.Example.List where

import Memorist.Memorist as M
import Memorist.Data.List
import qualified Test.QuickCheck as QC

import Data.List

-- head
{-
    head (x:_) = x
    head []    = error ...
-}
headM :: Th (ListT a) -> MemoristM a
headM txs = do
    tick
    xs <- force txs
    case xs of
        NilT -> error "empty list"
        ConsT tx _ -> force tx

headM_fromPure :: Repr a => [a] -> MemoristM (Rep a)
headM_fromPure = fromPure1 headM

-- input list, demand
headM_cost :: [Int] -> Int -> Cost
headM_cost = infcostFromPure1' headM

-- headM_cost [1..100000] 1
-- headM_cost [1..] 1

testM :: (Th (ListT Int)) -> (Th (ListT Int)) -> MemoristM Int
testM txs tys = do
    tick
    x <- headM txs
    y <- headM tys
    return $ x + y

testM_cost :: [Int] -> [Int] -> Int -> Cost
testM_cost = infcostFromPure2' testM

-- testM_cost [1..5] [2..6] 3

------

-- take
{-
    take n xs | 0 < n     = unsafeTake n xs
              | otherwise = []

    unsafeTake :: Int -> [a] -> [a]
    unsafeTake !_  []     = []
    unsafeTake 1   (x: _) = [x]
    unsafeTake m   (x:xs) = x : unsafeTake (m - 1) xs
-}
-- Treating Int as primitives
-- Cannot translate the lib version directly; instead look at this alternative version
{-
    take n xs =
        if 0 < n then
            case (n, xs) of
                (_, [])     -> []
                (1, (y:_))  -> [y]
                (m, (y:ys)) -> y : take (m - 1) ys
        else []
-}
takeM :: Th Int -> Th (ListT a) -> MemoristM (ListT a)
takeM tn txs = do
    tick
    n <- force tn
    if 0 < n then do  -- Ignoring < ?
        xs <- force txs
        case (n, xs) of
            (_, NilT)         -> return NilT
            (1, ConsT ty _)   -> do
                tzs <- lazy $ return NilT
                return $ ConsT ty tzs
            (m, ConsT ty tys) -> do
                tm1 <- lazy $ return $ m - 1  -- Ignoring - ?
                tzs <- lazy $ takeM tm1 tys
                return $ ConsT ty tzs
    else return NilT

takeM_fromPure :: Repr a => Int -> [a] -> MemoristM (ListT (Rep a))
takeM_fromPure = fromPure2 takeM

prop_takeM_costbound :: ReprDemandArb a => Int -> [a] -> QC.Property
prop_takeM_costbound n xs = upperbound (fromPure2 takeM n xs) $ \d -> min (max 1 (n + 1)) (sizeD 1 d)
-- prop_takeM_costbound n xs = QC.forAll (arbDemandM m) $ \d ->
--     M.toInteger (infcost' m d) <= fromIntegral (min (max 1 (n + 1)) (sizeD 1 d))
--     where m = takeM_fromPure n xs

qc_takeM_ex :: IO ()
qc_takeM_ex = QC.quickCheck (prop_takeM_costbound :: Int -> [Int] -> QC.Property)

qc_takeM_ex' :: Int -> IO ()
qc_takeM_ex' n = QC.quickCheck $ (prop_takeM_costbound :: Int -> [Int] -> QC.Property) n [1..]

---


-- repeat
{-
    repeat x = xs where xs = x : xs
  
    repeat' x = x : repeat' x
    --- (A-normalize) --->
    repeat' x = let xs = repeat' x in x : xs
-}
repeatM' :: Th a -> MemoristM (ListT a)
repeatM' tx = do
    tick
    txs <- lazy $ repeatM' tx
    return $ ConsT tx txs

-- input list, demand
repeatM'_cost :: ReprDemandArb a => a -> Dem (Rep [a]) -> Cost
repeatM'_cost = infcostFromPure1' repeatM'

-- repeatM'_cost (42::Int) $ ConsD (Need 42) $ Need $ ConsD (Need 42) Skip

prop_repeatM'_cost_bound :: ReprDemandArb a => a -> QC.Property
prop_repeatM'_cost_bound x = upperbound (fromPure1 repeatM' x) (\d -> sizeD 1 d)
-- prop_repeatM'_cost_bound x = QC.forAll (arbDemandM m) $ \d ->
--     M.toInteger (infcost' m d) <= Prelude.toInteger (sizeD 1 d)
--     where m = fromPure1 repeatM' x

prop_repeatM'_cost_bound_int :: Int -> QC.Property
prop_repeatM'_cost_bound_int = prop_repeatM'_cost_bound

qc_repeatM'_ex :: IO ()
-- qc_repeatM'_ex = QC.quickCheck (prop_repeatM'_cost_bound :: Int -> QC.Property)
qc_repeatM'_ex = QC.quickCheck prop_repeatM'_cost_bound_int


-- replicate
{-
    replicate n x  =  take n (repeat x)
-}
replicateM :: Th Int -> Th a -> MemoristM (ListT a)
replicateM tn tx = do
    tick
    txs <- lazy $ repeatM' tx
    takeM tn txs

prop_replicateM_costbound :: (ReprDemandArb a, QC.Arbitrary a) => Int -> a -> QC.Property
prop_replicateM_costbound n x = upperbound (fromPure2 replicateM n x) $ \d ->
    2 * min (max 1 (n + 1)) (sizeD 1 d) + 1

qc_replicateM_ex :: IO ()
qc_replicateM_ex = QC.quickCheck (prop_replicateM_costbound :: Int -> Bool -> QC.Property)
