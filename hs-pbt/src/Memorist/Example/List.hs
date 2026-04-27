module Memorist.Example.List where

import Memorist.Memorist as M
import Memorist.Data.List
import qualified Test.QuickCheck as QC
    ( quickCheck, Property, Arbitrary, NonEmptyList(getNonEmpty) )

-- import Data.List

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

{-
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
-}

-- prop_headM_cost :: ReprDemandArb a => [a] -> QC.Property
-- prop_headM_cost xs = xs /= [] ==> fromPure1 headM xs `exactly` \_ -> 1
prop_headM_cost :: ReprDemandArb a => QC.NonEmptyList a -> QC.Property
prop_headM_cost xs = fromPure1 headM xs' `exactly` \_ -> 1 :: Integer
    where xs' = QC.getNonEmpty xs

qc_headM_cost :: IO ()
qc_headM_cost = QC.quickCheck (prop_headM_cost :: QC.NonEmptyList Int -> QC.Property)


-- append
{-
    (++) []     ys = ys
    (++) (x:xs) ys = x : xs ++ ys
-}
appendM :: Th (ListT a) -> Th (ListT a) -> MemoristM (ListT a)
appendM txs tys = do
    tick
    xs <- force txs
    case xs of
        NilT -> force tys
        ConsT tx txs' -> do
            tzs <- lazy $ appendM txs' tys
            return $ ConsT tx tzs

prop_appendM_ub :: ReprDemandArb a => [a] -> [a] -> QC.Property
prop_appendM_ub xs ys =
    fromPure2 appendM xs ys `upperboundby` \d -> min (sizeD 1 d) (length xs + 1)

qc_appendM_ub :: IO ()
qc_appendM_ub = QC.quickCheck (prop_appendM_ub :: [Int] -> [Int] -> QC.Property)


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
-- For simplicity, we only study the number of times takeM is called during recursion,
-- ignoring the arithmetic operations. We also do not go through the full process
-- to translate these operations into the Memorist monad, although this is easy to do.
takeM :: Th Int -> Th (ListT a) -> MemoristM (ListT a)
takeM tn txs = do
    tick
    n <- force tn
    if 0 < n then do
        xs <- force txs
        case (n, xs) of
            (_, NilT)         -> return NilT
            (1, ConsT ty _)   -> do
                tzs <- lazy $ return NilT
                return $ ConsT ty tzs
            (m, ConsT ty tys) -> do
                tm1 <- lazy $ return $ m - 1
                tzs <- lazy $ takeM tm1 tys
                return $ ConsT ty tzs
    else return NilT

-- takeM_fromPure :: Repr a => Int -> [a] -> MemoristM (ListT (Rep a))
-- takeM_fromPure = fromPure2 takeM

prop_takeM_ub :: ReprDemandArb a => Int -> [a] -> QC.Property
prop_takeM_ub n xs =
    fromPure2 takeM n xs `upperboundby` \d -> min (max 1 (n + 1)) (sizeD 1 d)

qc_takeM_ub :: IO ()
qc_takeM_ub = QC.quickCheck (prop_takeM_ub :: Int -> [Int] -> QC.Property)

-- qc_takeM_ub' :: Int -> IO ()
-- qc_takeM_ub' n = QC.quickCheck $ (prop_takeM_ub :: Int -> [Int] -> QC.Property) n [1..]

--------------------------------------------------------------------------------

-- reverse
{-
    reverse l = rev l []
    where
        rev []     a = a
        rev (x:xs) a = rev xs (x:a)
-}
reverseM :: Th (ListT a) -> MemoristM (ListT a)
reverseM tl = tick >> lazy (return NilT) >>= revM tl

revM :: Th (ListT a) -> Th (ListT a) -> MemoristM (ListT a)
revM txs ta = do
    tick
    xs <- force txs
    case xs of
        NilT -> force ta
        ConsT tx txs' -> do
            ta' <- lazy $ return $ ConsT tx ta
            revM txs' ta'

-- This implementation iterates over the input list exactly once regardless of
-- the demand on value, and hence the cost specification below.
-- The 'exact' combinator specify that the cost of the program exactly
-- equals to the expression supplied as its last argument.
prop_reverseM_cost :: ReprDemandArb a => [a] -> QC.Property
prop_reverseM_cost xs = fromPure1 reverseM xs `exactly` \_ -> length xs + 2

qcN_reverseM_cost :: Int -> IO ()
qcN_reverseM_cost n = quickCheckN n (prop_reverseM_cost :: [Int] -> QC.Property)

qc_reverseM_cost :: IO ()
qc_reverseM_cost = qcN_reverseM_cost 100

-- In comparison, this is a naïve implementation of reverse
{-
    reverseSlow []     = []
    reverseSlow (x:xs) = reverseSlow xs ++ [x]
-}
reverseSlowM :: Th (ListT a) -> MemoristM (ListT a)
reverseSlowM txs = do
    tick
    xs <- force txs
    case xs of
        NilT -> return NilT
        ConsT tx txs' -> do
            tr <- lazy $ reverseSlowM txs'
            tn <- lazy $ return NilT
            ty <- lazy $ return $ ConsT tx tn
            appendM tr ty

-- The naïve implementation is known to belong to O(n^2).
-- The exact computation cost is more complicated to express since it also
-- depends on the demand on value. But it is straightforward to determine
-- the lower bound, since it needs to go through the input list at least once.

-- This is the upper bound on its computation cost
prop_reverseSlowM_ub :: ReprDemandArb a => [a] -> QC.Property
prop_reverseSlowM_ub xs =
    fromPure1 reverseSlowM xs `upperboundby` \_ -> (length xs + 1) * (length xs + 1)

qcN_reverseSlowM_ub :: Int -> IO ()
qcN_reverseSlowM_ub n = quickCheckN n (prop_reverseSlowM_ub :: [Int] -> QC.Property)

qc_reverseSlowM_ub :: IO ()
qc_reverseSlowM_ub = qcN_reverseSlowM_ub 100

-- The lower bound on its computation cost
prop_reverseSlowM_lb :: ReprDemandArb a => [a] -> QC.Property
prop_reverseSlowM_lb xs =
    fromPure1 reverseSlowM xs `lowerboundby` \_ -> length xs + 1

qcN_reverseSlowM_lb :: Int -> IO ()
qcN_reverseSlowM_lb n = quickCheckN n (prop_reverseSlowM_lb :: [Int] -> QC.Property)

qc_reverseSlowM_lb :: IO ()
qc_reverseSlowM_lb = qcN_reverseSlowM_lb 100

-- We can compare the cost incurred by the two versions of reverse
-- on the same input (and wrt the same demand on the value).
-- It happens to be the case that the naïve reverse is never faster than
-- the tail recursive version (modulo some constant difference---here because we
-- also put an extra tick when reverseM is initially unfolded to revM).
prop_compareReverse :: ReprDemandArb a => [a] -> QC.Property
prop_compareReverse xs = compareOnSame (fromPure1 reverseM xs) (fromPure1 reverseSlowM xs) $
    \cost1 cost2 -> cost1 <= cost2 + 1

qcN_compareReverse :: Int -> IO ()
qcN_compareReverse n = quickCheckN n (prop_compareReverse :: [Int] -> QC.Property)

qc_compareReverse :: IO ()
qc_compareReverse = qcN_compareReverse 100

--------------------------------------------------------------------------------

-- Examples involving potentially non-terminating computations

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

prop_repeatM'_cost :: ReprDemandArb a => a -> QC.Property
prop_repeatM'_cost x = fromPure1 repeatM' x `exactly` \d -> sizeD 1 d
-- prop_repeatM'_ub x = QC.forAll (arbDemandM m) $ \d ->
--     M.toInteger (infcost' m d) <= Prelude.toInteger (sizeD 1 d)
--     where m = fromPure1 repeatM' x

-- Computation of repeatM' itself can go on indefinitely when demanded in full:
-- try running and printing
--      eval (fromPure1 repeatM' True) initstate
-- it will keep printing the list.
-- Despite this, it is completely fine to check the above specification of
-- repeatM' directly like the one below. This is because, while the demand is
-- generated based on the value of computing repeatM', both the generator and
-- the computation of the cost inference functions underlying our framework
-- both behave lazily by default.
qcN_repeatM'_cost :: Int -> IO ()
qcN_repeatM'_cost n = quickCheckN n (prop_repeatM'_cost :: Int -> QC.Property)

qc_repeatM'_cost :: IO ()
qc_repeatM'_cost = qcN_repeatM'_cost 100

-- Obviously, it also works with the replicate function below, since the
-- 'take n' function always demand a finite portion from the result of 'repeat'
-- under lazy evaluation.

-- replicate
{-
    replicate n x  =  take n (repeat x)
-}
replicateM :: Th Int -> Th a -> MemoristM (ListT a)
replicateM tn tx = do
    tick
    txs <- lazy $ repeatM' tx
    takeM tn txs

prop_replicateM_ub :: (ReprDemandArb a, QC.Arbitrary a) => Int -> a -> QC.Property
prop_replicateM_ub n x = fromPure2 replicateM n x `upperboundby` \d ->
    2 * min (max 1 (n + 1)) (sizeD 1 d) + 1

qc_replicateM_ub :: IO ()
qc_replicateM_ub = QC.quickCheck (prop_replicateM_ub :: Int -> Bool -> QC.Property)
