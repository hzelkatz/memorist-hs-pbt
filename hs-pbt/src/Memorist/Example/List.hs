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

prop_headCost :: ReprDemandArb a => QC.NonEmptyList a -> QC.Property
prop_headCost xs = fromPure1 headM xs' `exactly` \_ _ -> 1 :: Integer
    where xs' = QC.getNonEmpty xs

qc_headCost :: IO ()
qc_headCost = QC.quickCheck (prop_headCost :: QC.NonEmptyList Int -> QC.Property)


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

prop_appendUBound :: ReprDemandArb a => [a] -> [a] -> QC.Property
prop_appendUBound xs ys =
    fromPure2 appendM xs ys `upperboundby` \_ d -> min (sizeD 1 d) (length xs + 1)

qc_appendUBound :: IO ()
qc_appendUBound = QC.quickCheck (prop_appendUBound :: [Int] -> [Int] -> QC.Property)


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

prop_takeUBound :: ReprDemandArb a => Int -> [a] -> QC.Property
prop_takeUBound n xs =
    fromPure2 takeM n xs `upperboundby` \_ d -> min (max 1 (n + 1)) (sizeD 1 d)

qc_takeUBound :: IO ()
qc_takeUBound = QC.quickCheck (prop_takeUBound :: Int -> [Int] -> QC.Property)

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
prop_reverseCost :: ReprDemandArb a => [a] -> QC.Property
prop_reverseCost xs = fromPure1 reverseM xs `exactly` \_ _ -> length xs + 2

qcN_reverseCost :: Int -> IO ()
qcN_reverseCost n = quickCheckN n (prop_reverseCost :: [Int] -> QC.Property)

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
prop_reverseSlowUBound :: ReprDemandArb a => [a] -> QC.Property
prop_reverseSlowUBound xs =
    fromPure1 reverseSlowM xs `upperboundby` \_ _ -> (length xs + 1) * (length xs + 1)

qcN_reverseSlowUBound :: Int -> IO ()
qcN_reverseSlowUBound n = quickCheckN n (prop_reverseSlowUBound :: [Int] -> QC.Property)

-- The lower bound on its computation cost
prop_reverseSlowLBound :: ReprDemandArb a => [a] -> QC.Property
prop_reverseSlowLBound xs =
    fromPure1 reverseSlowM xs `lowerboundby` \_ _ -> length xs + 1

qcN_reverseSlowLBound :: Int -> IO ()
qcN_reverseSlowLBound n = quickCheckN n (prop_reverseSlowLBound :: [Int] -> QC.Property)

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

{-
repeatM'_cost :: ReprDemandArb a => a -> Dem (Rep [a]) -> Cost
repeatM'_cost = infcostFromPure1 repeatM'

-- repeatM'_cost (42::Int) $ ConsD (Need 42) $ Need $ ConsD (Need 42) Skip
-}

prop_repeatCost :: ReprDemandArb a => a -> QC.Property
prop_repeatCost x = fromPure1 repeatM' x `exactly` \_ d -> sizeD 1 d
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
qc_repeatCost :: Int -> IO ()
qc_repeatCost n = quickCheckN n (prop_repeatCost :: Int -> QC.Property)

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

prop_replicateUBound :: (ReprDemandArb a, QC.Arbitrary a) => Int -> a -> QC.Property
prop_replicateUBound n x = fromPure2 replicateM n x `upperboundby` \_ d ->
    2 * min (max 1 (n + 1)) (sizeD 1 d) + 1

qc_replicateUBound :: IO ()
qc_replicateUBound = QC.quickCheck (prop_replicateUBound :: Int -> Bool -> QC.Property)
