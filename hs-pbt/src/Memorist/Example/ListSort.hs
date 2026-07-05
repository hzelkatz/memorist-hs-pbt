-- {-# OPTIONS_GHC -Wno-type-defaults #-}
module Memorist.Example.ListSort where

import Memorist.Memorist as M
import Memorist.Data.List
import Memorist.Example.Util
import Test.QuickCheck as QC ( quickCheck, Property, SortedList (..) )
import Data.List (sort)

-- insertion sort

{-
insertionSort :: Ord a => [a] -> [a]
insertionSort [] = []
insertionSort (x:xs) = insert x $ insertionSort xs

insert :: Ord a => a -> [a] -> [a]
insert x []     = [x]
insert x (y:ys) = if x <= y then x:(y:ys) else y : insert x ys
-}

insertionSortM :: Ord a => Th (ListT a) -> MemoristM (ListT a)
insertionSortM txs = do
    xs <- force txs
    case xs of
        NilT -> return NilT
        ConsT tx txs' -> do
            tys <- lazy $ insertionSortM txs'
            insertM tx tys

insertM :: Ord a => Th a -> Th (ListT a) -> MemoristM (ListT a)
insertM tx tys = do
    ys <- force tys
    case ys of
        NilT -> do
            tnil <- lazy $ return NilT
            return $ ConsT tx tnil
        ConsT ty tys' -> do
            x <- force tx
            y <- force ty
            tick    -- count the number of comparisons made
            if x <= y then return $ ConsT tx tys
            else do
                tzs <- lazy $ insertM tx tys'
                return $ ConsT ty tzs

qcN_insertUBound :: Int -> IO ()
qcN_insertUBound n = quickCheckN n $ \(x::Int) (xs::[Int]) ->
    fromPure2 insertM x xs `upperboundby` \_ d -> sizeD 0 d

-- Worst case performance of insertion sort is *not* in O(n log n).
qcN_insertionSortBoundWrong :: Int -> IO ()
qcN_insertionSortBoundWrong k = quickCheckN k $ \(xs :: [Int]) ->
    fromPure1 insertionSortM xs `upperboundby`
        \_ _ -> let n = fromIntegral (length xs) in n * logBase 2 (max 1 n)

-- We can give, e.g., the following upper bound on the computation cost in the worst case.
-- This bound is not the tightest possible but intuitive enough.
-- This follows our understanding of the algorithm: its worst-case
-- performance is in O(n^2) where n is the length of the list.
qcN_insertionSortBound :: Int -> IO ()
qcN_insertionSortBound n = quickCheckN n $ \(xs::[Int]) ->
    fromPure1 insertionSortM xs `upperboundby` \_ d -> sizeD 0 d * length xs

{-
-- Meanwhile in the best case, we expect that each element is compared against
-- only its immediate next element (except for the last one).
-- Thus we specify the following lower bound to test.
qcN_insertionSortLBound :: Int -> IO ()
qcN_insertionSortLBound n = quickCheckN n $ \(xs::[Int]) ->
    fromPure1 insertionSortM xs `lowerboundby` \_ _ -> max 0 (length xs - 1)
-}

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

-- NOTE: it is also possible to test a similar statement on the worst case performance,
-- but we need to be careful if we want `exactly` instead of `upperboundby`.
-- We have to generate input list in which each element is strictly greater
-- than its next element---a slightly stronger property than being sorted in reverse order.
-- This is because, we can have an equal pair of elements in the revserely sorted list,
-- but this may not invoke more comparisons for the first element in the pair.

-- TODO: multiple of `take n sorted`

{-
-- Note that, internally the input is transformed into Memorist representation
-- types ('Rep a' of a type 'a'); and currently, 'Rep a' is not injective.
-- Thus a signature like
--      (ReprDemandArb a, Ord a) => a -> [a] -> Property
-- would not typecheck.
-- 
-- An alternative is to not use Ord class in the translations, but
-- pass in the comparator directly, that is:
    
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
                case cmp y x of     -- x <= y equivalent to y > x
                    GT -> return $ ConsT tx tys
                    _ -> do
                        tzs <- lazy $ insertM cmp tx tys'
                        return $ ConsT ty tzs

-- although in practice it does not seem much difference so far because
-- the internal transformation so far means we almost always need to
-- manually provide the types of input when actually passing the property to
-- the quickCheck function.
--
-- Also, in order to supply the correct comparator, we often need to specialize
-- the input type anyway. For instance, we instantiate the type directly to Int
-- so we can use its 'compare' function directly. Memorist representation of Int
-- is Int itself, which saves many troubles in general.
-- 
--      quickCheckN n $ \(xs :: [Int]) ->
--          fromPure1 (insertionSortM compare) xs `upperboundby` \_ d -> ...
--
-- Another possible workaround (not tested yet) is to use the `~` operator on types
-- to allow asserting the `Rep a` type to belong to Ord class.
-}

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
prop_mergesortUBound :: [Int] -> QC.Property
prop_mergesortUBound xs = fromPure1 (mergesortM compare) xs `upperboundby`
    \_ _ -> n * logBase 2 (max 1 n)
    where n = fromIntegral (length xs) :: Double

qcN_mergesortUBound :: Int -> IO ()
qcN_mergesortUBound n = quickCheckN n prop_mergesortUBound

-- NOTE: since the bound is not specified in terms of the demand,
-- we can alternatively always test against full demand on the resulting list.
-- But the test will be much slower to run, due to having to generate the demand
-- as well as collect and comupte cost agaist the full result list which takes
-- more time in general, and forcing the computation to be fully performed as well.
--
prop_mergesortUBound' :: [Int] -> Bool
prop_mergesortUBound' xs = fromPure1 (mergesortM compare) xs `upperboundWith` fullDemand
    $ \_ _ -> n * logBase 2 (max 1 n)
    where n = fromIntegral (length xs) :: Double

qcN_mergesortUBound' :: Int -> IO ()
qcN_mergesortUBound' n = quickCheckN n prop_mergesortUBound'
