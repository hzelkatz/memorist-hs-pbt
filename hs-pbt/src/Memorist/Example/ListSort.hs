module Memorist.Example.ListSort where

import Memorist.Memorist as M
import Memorist.Data.List
import qualified Test.QuickCheck as QC ( quickCheck, Property )


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

prop_insertionSortM_ub :: [Int] -> QC.Property
prop_insertionSortM_ub xs = fromPure1 (insertionSortM compare) xs `upperboundby`
    \_ -> length xs * length xs

qcN_insertionSortM_ub :: Int -> IO ()
qcN_insertionSortM_ub n = quickCheckN n prop_insertionSortM_ub

qc_insertionSortM_ub :: IO ()
qc_insertionSortM_ub = qcN_insertionSortM_ub 100



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
    where n = fromIntegral (length xs)

qcN_mergesortM_ub :: Int -> IO ()
qcN_mergesortM_ub n = quickCheckN n prop_mergesortM_ub

qc_mergesortM_ub :: IO ()
qc_mergesortM_ub = qcN_mergesortM_ub 100
