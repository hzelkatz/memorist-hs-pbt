module Memorist.Example.ListSort where

import Memorist.Memorist as M
import Memorist.Data.List
import qualified Test.QuickCheck as QC ( quickCheck, Property )
import Data.List (sort)

-- insertion sort

{-
insertionSort :: Ord a => [a] -> [a]
insertionSort [] = []
insertionSort (x:xs) = insert x $ insertionSort xs

insert :: Ord a => a -> [a] -> [a]
insert x []     = [x]
insert x (y:ys) = if y <= x then y : insert x ys else x:(y:ys)
-}

insertionSortM :: (a -> a -> Ordering) -> Th (ListT a) -> MemoristM (ListT a)
insertionSortM cmp txs = do
    xs <- force txs
    case xs of
        NilT -> return NilT
        ConsT tx txs' -> do
            tys <- lazy $ insertionSortM cmp txs'
            insertM cmp tx tys

insertM :: (a -> a -> Ordering) -> Th a -> Th (ListT a) -> MemoristM (ListT a)
insertM cmp tx tys = do
    ys <- force tys
    case ys of
        NilT -> do
            tnil <- lazy $ return NilT
            return $ ConsT tx tnil
        ConsT ty tys' -> do
            x <- force tx
            y <- force ty
            tick    -- tick here to count the comparisons made
            case cmp x y of     -- y <= x equivalent to x > y
                GT -> do
                    tzs <- lazy $ insertM cmp tx tys'
                    return $ ConsT ty tzs
                _ -> return $ ConsT tx tys

-- We instantiate the types of input in the property statement directly,
-- so that we can use the 'compare' function directly here.
--
-- We could've generalize it into any 'Ord a', but because internally
-- the input is transformed into Memorist representation types ('Rep a' of a type 'a'),
-- and currently 'Rep a' is not injective, this signature
--
--      prop_insertM_ub :: (ReprDemandArb a, Ord a) => a -> [a] -> QC.Property
--
-- would not typecheck.
prop_insertM_ub :: Int -> [Int] -> QC.Property
prop_insertM_ub x xs = fromPure2 (insertM compare) x xs `upperboundby` \d -> sizeD 0 d

qc_insertM_ub :: IO ()
qc_insertM_ub = QC.quickCheck prop_insertM_ub

-- We can give, e.g., the following upper bound on the computation cost in the worst case.
-- This bound is not the tightest possible but intuitive enough.
-- In practice one might be interested in an even looser upper bound
-- like (length xs)^2, which should hold in this case as well.
-- Either way, this follows our understanding of the algorithm: its worst-case
-- performance is in O(n^2).
prop_insertionSortM_ub :: [Int] -> QC.Property
prop_insertionSortM_ub xs = fromPure1 (insertionSortM compare) xs `upperboundby`
    \d -> sizeD 0 d * length xs

qcN_insertionSortM_ub :: Int -> IO ()
qcN_insertionSortM_ub n = quickCheckN n prop_insertionSortM_ub

qc_insertionSortM_ub :: IO ()
qc_insertionSortM_ub = qcN_insertionSortM_ub 100

-- Meanwhile in the best case, we expect that each element is compare against
-- only its immediate next element (except for the last one).
-- Thus we specify the following lower bound to test.
prop_insertionSortM_lb :: [Int] -> QC.Property
prop_insertionSortM_lb xs = fromPure1 (insertionSortM compare) xs `lowerboundby`
    \_ -> max 0 (length xs - 1)

qcN_insertionSortM_lb :: Int -> IO ()
qcN_insertionSortM_lb n = quickCheckN n prop_insertionSortM_lb

qc_insertionSortM_lb :: IO ()
qc_insertionSortM_lb = qcN_insertionSortM_lb 100

-- In fact, for insertion sort, the best case should exactly be when the input
-- list is already sorted. That is, when the input list is sorted, its cost should
-- be in Θ(n), where n is length of the input.
-- 
-- There are various ways to include the sortedness in the statement.
-- In practice, an efficient way is to generate the already-sorted list to begin with.
-- We can write a QuickCheck generator to do this task. But in this case,
-- since we are interested in studying the performance of our implementation of
-- the insertion sort and do not care about the correctness of, say, Haskell's
-- built-in sorting function, for simplicity we simply sort the randomly generated
-- list using Data.List.sort before invoking our insertion sort on it.
-- Because our framework allows specifying properties on the vanilla Haskell types
-- directly which are then automatically lifted to their Memorist representations,
-- it is easy to accomplish what we want by preprocessing the generated pure lists.
prop_insertionSortM_sorted_cost :: [Int] -> QC.Property
prop_insertionSortM_sorted_cost xs = fromPure1 (insertionSortM compare) sorted
    `exactly` \_ -> max 0 (length xs - 1)
    where sorted = sort xs

qcN_insertionSortM_sorted_cost :: Int -> IO ()
qcN_insertionSortM_sorted_cost n = quickCheckN n prop_insertionSortM_sorted_cost

qc_insertionSortM_sorted_cost :: IO ()
qc_insertionSortM_sorted_cost = qcN_insertionSortM_sorted_cost 100

-- NOTE: it is also possible to test a similar statement on the worst case performance,
-- but the statement would be more complicated if we want `exactly` instead of `upperboundby`,
-- as we have to generate input list in which each element is strictly greater
-- than its next element---a slightly stronger property than being sorted in reverse order.
-- This is because, we can have an equal pair of elements in the revserely sorted list,
-- but this won't invoke more comparisons for the first element in the pair.

-- -----------------------------------------------------------------------------

-- (bottom-up) merge sort

{-
mergesort :: Ord a => [a] -> [a]
mergesort = mergeall . split

mergeall :: Ord a => [[a]] -> [a]
mergeall [] = []
mergeall [xs] = xs
mergeall xss = mergeall $ mergepairs xss

mergepairs :: Ord a => [[a]] -> [[a]]
mergepairs [] = []
mergepairs [xs] = [xs]
mergepairs (xs:ys:xss) = merge xs ys : mergepairs xss

merge :: Ord a => [a] -> [a] -> [a]
merge [] ys = ys
merge xs [] = xs
merge (x:xs) (y:ys) =
    if x <= y then x : merge xs (y:ys) else y : merge (x:xs) ys

split :: [a] -> [[a]]
split [] = []
split (x:xs) = [x] : split xs
-}

mergesortM :: (a -> a -> Ordering) -> Th (ListT a) -> MemoristM (ListT a)
mergesortM cmp txs = do
    txss <- lazy $ splitM txs
    mergeallM cmp txss

mergeallM :: (a -> a -> Ordering) -> Th (ListT (ListT a)) -> MemoristM (ListT a)
mergeallM cmp txss = do
    xss <- force txss
    case xss of
        -- case []
        NilT -> return NilT
        ConsT tys tyss -> do
            yss <- force tyss
            case yss of
                -- case [_]
                NilT -> force tys
                -- case _
                _ -> do
                    tzss <- lazy $ mergepairsM cmp txss
                    mergeallM cmp tzss

mergepairsM :: (a -> a -> Ordering) -> Th (ListT (ListT a)) -> MemoristM (ListT (ListT a))
mergepairsM cmp txss = do
    xss <- force txss
    case xss of
        -- case []
        NilT -> return NilT
        ConsT tys tyss -> do
            yss <- force tyss
            case yss of
                -- case [_]
                NilT -> return xss
                -- case (_:_:_)
                ConsT tys' tyss' -> do
                    tzs <- lazy $ mergeM cmp tys tys'
                    tzss <- lazy $ mergepairsM cmp tyss'
                    return $ ConsT tzs tzss

mergeM :: (a -> a -> Ordering) -> Th (ListT a) -> Th (ListT a) -> MemoristM (ListT a)
mergeM cmp txs tys = do
    xs <- force txs
    ys <- force tys
    case xs of
        NilT -> return ys
        ConsT tx txs' ->
            case ys of
                NilT -> return xs
                ConsT ty tys' -> do
                    x <- force tx
                    y <- force ty
                    tick    -- tick here to count the comparisons made
                    case cmp y x of   -- x <= y equivalent to y > x
                        GT -> do
                            tzs <- lazy $ mergeM cmp txs' tys
                            return $ ConsT tx tzs
                        _ -> do
                            tzs <- lazy $ mergeM cmp txs tys'
                            return $ ConsT ty tzs

splitM :: Th (ListT a) -> MemoristM (ListT (ListT a))
splitM txs = do
    xs <- force txs
    case xs of
        NilT -> return NilT
        ConsT ty tys -> do
            tnil <- lazy $ return NilT
            tzs <- lazy $ return $ ConsT ty tnil
            tzss <- lazy $ splitM tys
            return $ ConsT tzs tzss

-- NOTE however that we need to specify the bound on concrete cost, and are
-- unable to handle complexity class yet.
-- This bound happens to apply to this mergesort algorithm.
-- But in general, we might not be able to easily determine a concrete bound
-- for a function supposed to be in O(n log n) (although this is also true for
-- any complexity class).
prop_mergesortM_ub :: [Int] -> QC.Property
prop_mergesortM_ub xs = fromPure1 (mergesortM compare) xs `upperboundbyR`
    \_ -> n * logBase 2 (max 1 n)
    where n = fromIntegral (length xs) :: Double

qcN_mergesortM_ub :: Int -> IO ()
qcN_mergesortM_ub n = quickCheckN n prop_mergesortM_ub

qc_mergesortM_ub :: IO ()
qc_mergesortM_ub = qcN_mergesortM_ub 100
