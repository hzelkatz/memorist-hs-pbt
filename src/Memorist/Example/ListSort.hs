-- {-# OPTIONS_GHC -Wno-type-defaults #-}

module Memorist.Example.ListSort where

import Memorist.Memorist as M
import Memorist.Data.List
import Memorist.Example.Util
import Memorist.Example.List (takeM , mapMM)
import Test.QuickCheck as QC ( Property, SortedList (..), NonNegative (..)
                             , noShrinking, arbitrary, forAll, suchThat )

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
        \_ _ -> let n = fromIntegral (length xs) in 1 + n * logBase 2 (max 1 n)

qcN_insertionSortBoundWrong' :: Int -> IO ()
qcN_insertionSortBoundWrong' k = quickCheckN k $ noShrinking $ \(xs :: [Int]) ->
    fromPure1 insertionSortM xs `upperboundby`
        \_ _ -> let n = fromIntegral (length xs) in 1 + n * logBase 2 (max 1 n)

qcN_insertionSortBoundWrong'' :: Int -> IO ()
qcN_insertionSortBoundWrong'' k = quickCheckN k $ noShrinking $ \(xs :: [Int]) ->
    fromPure1 insertionSortM xs `upperboundWith` fullDemand $
        \_ _ -> let n = fromIntegral (length xs) in 1 + n * logBase 2 (max 1 n)

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

-- NOTE to self: the multiple `take n sorted` examples may use higher-order functions;
-- hof's are not used otherwise in insertion or merge sort per se.

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
        -- case []
        NilT -> pure NilT
        ConsT tys tyss -> do
            yss <- force tyss
            case yss of
                -- case [_]
                NilT -> force tys
                -- case _
                _ -> do
                    tzss <- lazy (mergepairsM txss)
                    mergeallM tzss

mergepairsM :: Ord a => Th (ListT (ListT a)) -> MemoristM (ListT (ListT a))
mergepairsM txss = do
    xss <- force txss
    case xss of
        -- case []
        NilT -> pure NilT
        ConsT tys tyss -> do
            yss <- force tyss
            case yss of
                -- case [_]
                NilT -> pure xss
                -- case (_:_:_)
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

-- NOTE: since the bound is not specified in terms of the demand,
-- we can alternatively always test against full demand on the resulting list.
-- But the test will be much slower to run, due to having to generate the demand
-- as well as collect and comupte cost agaist the full result list which takes
-- more time in general, and forcing the computation to be fully performed as well.
qcN_mergesortUBound' :: Int -> IO ()
qcN_mergesortUBound' k = quickCheckN k $ \(xs :: [Int]) ->
    let n = fromIntegral (length xs) :: Double in
    fromPure1 mergesortM xs `upperboundWith` fullDemand $
        \_ _ -> n * logBase 2 (max 1 n)

-- If we want to consider demand...
qcN_mergesortUBound'' :: Int -> IO ()
qcN_mergesortUBound'' k = quickCheckN k $ \(xs :: [Int]) ->
    let n = fromIntegral (length xs) :: Double in
    fromPure1 mergesortM xs `upperboundby`
        \_ d -> n * logBase 2 (max 1 (fromIntegral (sizeD 0 d + 1)))

qcN_mergesortSortedWrong :: Int -> IO ()
qcN_mergesortSortedWrong n = quickCheckN n $ \(xs :: SortedList Int) ->
    let sorted = getSorted xs in
    fromPure1 mergesortM sorted `upperboundby` \_ _ -> length sorted
