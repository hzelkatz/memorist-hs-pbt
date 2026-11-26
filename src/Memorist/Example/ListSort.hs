module Memorist.Example.ListSort where

import Memorist.Memorist as M
import Memorist.Data.List
import Memorist.Example.Util
import Test.QuickCheck as QC ( Property, SortedList (..), noShrinking )

-- insertion sort

{-
insertionSort :: Ord a => [a] -> [a]
insertionSort [] = []
insertionSort (x:xs) = insert x (insertionSort xs)

insert :: Ord a => a -> [a] -> [a]
insert x []         = [x]
insert x ys@(y:ys') = if x <= y then x:ys else y : insert x ys'
-}

-- qcN_insertionSortCorrect n = quickCheckN n $ \(xs :: [Int]) ->
--     correct (fromPure1 insertionSortM xs) (insertionSort xs)

insertionSortM :: Ord a => Th (ListT a) -> MemoristM (ListT a)
insertionSortM txs = do
    xs <- force txs
    case xs of
        NilT -> pure NilT
        ConsT tx txs' -> do
            tys <- lazy (insertionSortM txs')
            insertM tx tys

insertM :: Ord a => Th a -> Th (ListT a) -> MemoristM (ListT a)
insertM tx tys = do
    ys <- force tys
    case ys of
        NilT -> do
            tnil <- lazy (pure NilT)
            pure (ConsT tx tnil)
        ConsT ty tys' -> do
            x <- force tx
            y <- force ty
            tick    -- count the number of comparisons made
            if x <= y then pure (ConsT tx tys)
            else do
                tzs <- lazy (insertM tx tys')
                pure (ConsT ty tzs)


qcN_insertUBound :: Int -> IO ()
qcN_insertUBound n = quickCheckN n $ \(x::Int) (xs::[Int]) ->
    fromPure2 insertM x xs `upperboundby` \_ d -> sizeD 0 d

-- Worst case performance of insertion sort is *not* in O(n log n).
qcN_insertionSortBoundWrong :: Int -> IO ()
qcN_insertionSortBoundWrong k = quickCheckN k $ \(xs :: [Int]) ->
    fromPure1 insertionSortM xs `upperboundby`
        \_ _ -> let n = fromIntegral (length xs) in 1 + n * logBase 2 (max 1 n) :: Double

qcN_insertionSortBoundWrong' :: Int -> IO ()
qcN_insertionSortBoundWrong' k = quickCheckN k $ noShrinking $ \(xs :: [Int]) ->
    fromPure1 insertionSortM xs `upperboundby`
        \_ _ -> let n = fromIntegral (length xs) in 1 + n * logBase 2 (max 1 n) :: Double

qcN_insertionSortBoundWrong'' :: Int -> IO ()
qcN_insertionSortBoundWrong'' k = quickCheckN k $ noShrinking $ \(xs :: [Int]) ->
    fromPure1 insertionSortM xs `upperboundWith` fullDemand $
        \_ _ -> let n = fromIntegral (length xs) in 1 + n * logBase 2 (max 1 n) :: Double

-- We can give, e.g., the following upper bound on the computation cost in the worst case.
-- This bound is not the tightest possible but intuitive enough.
-- This follows our understanding of the algorithm: its worst-case
-- performance is in O(n^2) where n is the length of the list.
qcN_insertionSortBound :: Int -> IO ()
qcN_insertionSortBound n = quickCheckN n $ \(xs::[Int]) ->
    fromPure1 insertionSortM xs `upperboundby` \_ d -> sizeD 0 d * length xs

-- In fact, for insertion sort, the best case should exactly be when the input
-- list is already sorted. That is, when the input list is sorted, its cost should
-- be in Θ(n), where n is length of the input.
-- 
-- There are various ways to include the sortedness in the statement.
-- Here we use the SortedList provided by QuickCheck library.
qcN_insertionSortSortedCost :: Int -> IO ()
qcN_insertionSortSortedCost n = quickCheckN n $ \(xs :: SortedList Int) ->
    let sorted = getSorted xs in
    fromPure1 insertionSortM sorted `exactly` \_ _ -> max 0 (length sorted - 1)

qcN_insertionSortSortedCost' :: Int -> IO ()
qcN_insertionSortSortedCost' n = quickCheckN n $ \(xs :: SortedList Int) ->
    let sorted = getSorted xs in
    fromPure1 insertionSortM sorted `upperboundby` \_ _ -> length sorted

-- But it cannot do better (fewer comparisons than number of elements in the list)
-- for already-sorted list with less demand on the final result.
-- The test below will likely provide an example illustrating this.
-- This is intuitive, since we still have to check every element in the list once
-- even if we are only need just the head from the sorted list.
qcN_insertionSortSortedCostWrong :: Int -> IO ()
qcN_insertionSortSortedCostWrong n = quickCheckN n $ \(xs :: SortedList Int) ->
    let sorted = getSorted xs in
    fromPure1 insertionSortM sorted `upperboundby` \_ d -> sizeD 0 d

-- -----------------------------------------------------------------------------

-- (bottom-up) merge sort

{-
mergesort :: Ord a => [a] -> [a]
mergesort = mergeall (split xs)

mergeall :: Ord a => [[a]] -> [a]
mergeall [] = []
mergeall [xs] = xs
mergeall xss = mergeall (mergepairs xss)

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

-- qcN_mergesortCorrect n = quickCheckN n $ \(xs :: [Int]) ->
--     correct (fromPure1 mergesortM xs) (mergesort xs)

mergesortM :: Ord a => Th (ListT a) -> MemoristM (ListT a)
mergesortM txs = do
    t <- lazy (splitM txs)
    mergeallM t
{-
The above is produced by the automated translator after prettifying and removing tick.
We can have a more concise version as below which resembles the source definition even more:

    mergesortM txs = mergeallM =<< lazy (splitM txs)
-}

mergeallM :: Ord a => Th (ListT (ListT a)) -> MemoristM (ListT a)
mergeallM txss = do
    xss <- force txss
    case xss of
        NilT -> pure NilT
        ConsT tys tyss -> do
            yss <- force tyss
            case yss of
                NilT -> force tys
                _ -> do
                    tzss <- lazy (mergepairsM txss)
                    mergeallM tzss

mergepairsM :: Ord a => Th (ListT (ListT a)) -> MemoristM (ListT (ListT a))
mergepairsM txss = do
    xss <- force txss
    case xss of
        NilT -> pure NilT
        ConsT tys tyss -> do
            yss <- force tyss
            case yss of
                NilT -> pure xss
                ConsT tys' tyss' -> do
                    tzs <- lazy (mergeM tys tys')
                    tzss <- lazy (mergepairsM tyss')
                    pure (ConsT tzs tzss)

mergeM :: Ord a => Th (ListT a) -> Th (ListT a) -> MemoristM (ListT a)
mergeM txs tys = do
    xs <- force txs
    case xs of
        NilT -> force tys
        ConsT tx txs' -> do
            ys <- force tys
            case ys of
                NilT -> pure xs
                ConsT ty tys' -> do
                    x <- force tx
                    y <- force ty
                    tick    -- tick here to count the comparisons made
                    if x <= y then do
                        tzs <- lazy $ mergeM txs' tys
                        pure $ ConsT tx tzs
                    else do
                        tzs <- lazy $ mergeM txs tys'
                        pure $ ConsT ty tzs
{-
-- For `mergeM`, we have used a manually restructured version to reduce overhead
-- of repeated forcing (which does not otherwise alter the cost derivation since
-- repeatedly forcing the same thunk does not incur duplicated usage and cost in
-- the our framework).
-- The translator actually produces the following (after prettifying and moving the tick).
-- The more complicated structure is due to how the translator process pattern-matching
-- in this specific case. We belive this should be further optimizable.

mergeM txs tys = do
    xs <- force txs
    case xs of
        NilT -> force tys
        _ -> do
            ys <- force tys
            case ys of
                NilT -> force txs
                _ -> do
                    xs <- force txs
                    case xs of
                        ConsT tx txs' -> do
                            ys <- force tys
                            case ys of
                                ConsT ty tys' -> do
                                    x <- force tx
                                    y <- force ty
                                    tick    -- manually insert tick
                                    if x <= y then do
                                        tzs <- lazy (mergeM txs' tys)
                                        pure (ConsT tx tzs)
                                    else do
                                        tzs <- lazy (mergeM txs tys')
                                        pure (ConsT ty tzs)
                                _ -> error "source pattern match failure"
                        _ -> error "source pattern match failure"
-}

splitM :: Th (ListT a) -> MemoristM (ListT (ListT a))
splitM txs = do
    xs <- force txs
    case xs of
        NilT -> pure NilT
        ConsT ty tys -> do
            tz <- lazy (do
                tn <- lazy (pure NilT)
                pure (ConsT ty tn))
            tzs <- lazy (splitM tys)
            pure (ConsT tz tzs)

-- We need to specify the bound on concrete cost, which is different from
-- what it appears in specifications using complexity class.
-- This bound happens to apply to this mergesort algorithm.
-- But in general, we might not be able to easily determine a concrete bound
-- for a function supposed to be in O(n log n) (although this is also true for
-- any complexity class).
prop_mergesortUBound :: [Int] -> Property
prop_mergesortUBound xs = fromPure1 mergesortM xs `upperboundby`
    \_ _ -> n * logBase 2 (max 1 n)
    where n = fromIntegral (length xs) :: Double

qcN_mergesortUBound :: Int -> IO ()
qcN_mergesortUBound n = quickCheckN n prop_mergesortUBound

-- If we want to consider demand...
qcN_mergesortUBound' :: Int -> IO ()
qcN_mergesortUBound' k = quickCheckN k $ \(xs :: [Int]) ->
    let n = fromIntegral (length xs) :: Double in
    fromPure1 mergesortM xs `upperboundby`
        \_ d -> n * logBase 2 (max 1 (fromIntegral (sizeD 0 d + 1)))

qcN_mergesortSortedWrong :: Int -> IO ()
qcN_mergesortSortedWrong n = quickCheckN n $ \(xs :: SortedList Int) ->
    let sorted = getSorted xs in
    fromPure1 mergesortM sorted `upperboundby` \_ _ -> length sorted
