module Memorist.Example.List where

import Memorist.Memorist as M
import Memorist.Data.List
import Memorist.Example.Util
import Test.QuickCheck as QC
    ( quickCheck, Property, Arbitrary, NonEmptyList(getNonEmpty), (.&&.) )

import Prelude hiding (mapM)

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

qc_headCost :: IO ()
qc_headCost = quickCheck $ \(xs :: NonEmptyList Int) ->
    fromPure1 headM (getNonEmpty xs) `exactly` \_ _ -> 1 :: Integer

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

{-
prop_appendBoundAttempt :: ReprDemandArb a => [a] -> [a] -> Property
prop_appendBoundAttempt xs ys =
    (m `upperboundby` \_ _ -> length xs) .&&.
    (m `upperboundby` \_ d -> sizeD 0 d)
    where m = fromPure2 appendM xs ys

qc_appendBoundAttempt :: IO ()
qc_appendBoundAttempt = quickCheck (prop_appendBoundAttempt :: [Int] -> [Int] -> Property)
-}

prop_appendBound :: ReprDemandArb a => [a] -> [a] -> Property
prop_appendBound xs ys =
    (m `upperboundby` \_ _ -> length xs + 1) .&&.
    (m `upperboundby` \_ d -> sizeD 1 d)
    where m = fromPure2 appendM xs ys

qcN_appendBound :: Int -> IO ()
qcN_appendBound n = quickCheckN n (prop_appendBound :: [Int] -> [Int] -> Property)

-- A more exact specification
qc_appendCost :: IO ()
qc_appendCost = quickCheck $ \(xs :: [Int]) (ys :: [Int]) ->
    fromPure2 appendM xs ys `exactly` \_ d -> min (sizeD 1 d) (length xs + 1)

-- One must be cautious that, even though the Memorist interface is lazy,
-- one might accidentally forces infinite computations in other places,
-- such as when specifying bounds.
-- For instance, this test hangs if one tries to run it:
--
-- qc_appendInfBad :: IO ()
-- qc_appendInfBad = quickCheck (prop_appendBound ([1,2..]::[Int]) ([1,2..]::[Int]))
--
-- but the issue is because the bound is specified with `length` (which is
-- strict in its argument) on the first input list to the appending function.
-- If we consider a looser bound such as the one below, it works perfectly fine.
qc_appendInfOk :: IO ()
qc_appendInfOk = quickCheck $
    fromPure2 appendM xs ys `upperboundby` \_ d -> sizeD 1 d
    where (xs, ys) = ([1,2..]::[Int], [1,2..]::[Int])

{-
-- Other test examples
tttt1= fullDemand $ value $ eval (reprM [True,True,True] :: MemoristM (ListT Bool)) initstate
tttt2 = eval (fromPure2 appendM [True,True] ([]::[Bool])) initstate
tttt3 = eval (fromPure2 appendM [True,True,True] ([]::[Bool])) initstate
tttt3v = value tttt3
tttt3d = fullDemand tttt3v
tttt3c = calcCost tttt3 tttt3d
tttt3c1 = infcost (fromPure2 appendM [True,True,True] ([]::[Bool])) fullDemand

appendM_test :: Cost
appendM_test = infcost (fromPure2 appendM ([1,2..]::[Int]) ([1,2..]::[Int])) minDemand
-}


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
            case xs of
                []     -> []
                (y:ys) -> y : take (m - 1) ys
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
        case xs of
            NilT         -> return NilT
            ConsT ty tys -> do
                tn1 <- lazy $ return $ n - 1
                tzs <- lazy $ takeM tn1 tys
                return $ ConsT ty tzs
    else return NilT

qc_takeBound :: IO ()
qc_takeBound = quickCheck (prop :: Int -> [Int] -> QC.Property)
    where prop n xs = fromPure2 takeM n xs `upperboundby` \_ _ -> max 1 (n + 1)

qc_takeBound' :: IO ()
qc_takeBound' = quickCheck $ \n (xs :: [Int]) ->
    fromPure2 takeM n xs `upperboundby` \_ d -> min (max 1 (n + 1)) (sizeD 1 d)

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

-- NOTE: compact version
qc_reverseCost :: IO ()
qc_reverseCost = quickCheck $ \(xs :: [Int]) ->
    fromPure1 reverseM xs `exactly` \_ _ -> length xs + 2

-- In comparison, this is a naïve implementation of reverse
{-
    reverseNaive []     = []
    reverseNaive (x:xs) = reverseNaive xs ++ [x]
-}
reverseNaiveM :: Th (ListT a) -> MemoristM (ListT a)
reverseNaiveM txs = do
    tick
    xs <- force txs
    case xs of
        NilT -> return NilT
        ConsT tx txs' -> do
            tr <- lazy $ reverseNaiveM txs'
            tn <- lazy $ return NilT
            ty <- lazy $ return $ ConsT tx tn
            appendM tr ty

-- rc1 :: [Int] -> ListD Int -> (Cost, Int, Annotated (ListT Int))
-- rc1 x d = (infcost m (\_ -> d), c, v)
--     where m = fromPure1 reverseNaiveM x
--           v = eval m initstate
--           c = 2 * (length x + 1)
--         --   c = (sizeD 0 d + 1) * (length x + 1)

-- The naïve implementation is known to belong to O(n^2).

prop_reverseNaiveCostFail :: ReprDemandArb a => [a] -> QC.Property
prop_reverseNaiveCostFail xs =
    fromPure1 reverseNaiveM xs `upperboundby` \_ _ -> 2 * (length xs + 1)

qcN_reverseNaiveCostFail :: Int -> IO ()
qcN_reverseNaiveCostFail n = quickCheckN n (prop_reverseNaiveCostFail :: [Int] -> QC.Property)

-- NOTE: compact version
qc_reverseNaiveCostFail :: IO ()
qc_reverseNaiveCostFail = quickCheck $ \(xs :: [Int]) ->
    fromPure1 reverseNaiveM xs `upperboundby` \_ _ -> 2 * (length xs + 1)

-- This is the upper bound on its computation cost
qcN_reverseNaiveUBound :: Int -> IO ()
qcN_reverseNaiveUBound n = quickCheckN n $ \(xs :: [Int]) ->
    fromPure1 reverseNaiveM xs `upperboundby` \_ _ -> (length xs + 1) * (length xs + 1)

-- A tighter bound expressed using demand
qcN_reverseNaiveUBound1 :: Int -> IO ()
qcN_reverseNaiveUBound1 n = quickCheckN n $ \(xs :: [Int]) ->
    fromPure1 reverseNaiveM xs `upperboundby` \_ d -> (sizeD 0 d + 1) * (length xs + 1)

-- The lower bound on its computation cost
qcN_reverseNaiveLBound :: Int -> IO ()
qcN_reverseNaiveLBound n = quickCheckN n $ \(xs :: [Int]) ->
    fromPure1 reverseNaiveM xs `lowerboundby` \_ _ -> length xs + 1

{-
-- We can compare the cost incurred by the two versions of reverse
-- on the same input (and wrt the same demand on the value).
--
-- NOTE: while this property likely holds, we have to take into account that
-- the Naive version has additional overhead since reverse itself and append both
-- contribute to the final cost. This will inflates the cost of the naive reverse
-- but it is more than what we are actually interested.
-- A better comparison would be to *not* tick in the reverseNaiveM (ie counting
-- only ticks of append), in which case the one below likely still holds.
prop_compareReverse :: ReprDemandArb a => [a] -> QC.Property
prop_compareReverse xs = compareOnSame (fromPure1 reverseM xs) (fromPure1 reverseNaiveM xs) $
    \cost1 cost2 -> cost1 <= cost2 + 2

qcN_compareReverse :: Int -> IO ()
qcN_compareReverse n = quickCheckN n (prop_compareReverse :: [Int] -> QC.Property)
-}

--------------------------------------------------------------------------------

-- Examples involving potentially non-terminating computations

-- repeat
{-
    repeat x = xs where xs = x : xs
    --- (alternatively) --->
    repeat x = x : repeat x
    --- (A-normalize) --->
    repeat x = let xs = repeat x in x : xs
-}
repeatM :: Th a -> MemoristM (ListT a)
repeatM tx = do
    tick
    txs <- lazy $ repeatM tx
    return $ ConsT tx txs

-- repeatM_cost :: ReprDemandArb a => a -> Dem (Rep [a]) -> Cost
-- repeatM_cost = infcostFromPure1 repeatM'
--
-- repeatM_cost (42::Int) $ ConsD (Need 42) $ Need $ ConsD (Need 42) Skip

prop_repeatCost :: ReprDemandArb a => a -> QC.Property
prop_repeatCost x = fromPure1 repeatM x `exactly` \_ d -> sizeD 1 d

-- Computation of repeatM itself can go on indefinitely when demanded in full:
-- try running and printing
--      eval (fromPure1 repeatM True) initstate
-- it will keep printing the list.
-- Despite this, it is generally fine to check the above specification of
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
    txs <- lazy $ repeatM tx
    takeM tn txs

qcN_replicateBound :: Int -> IO ()
qcN_replicateBound n = quickCheckN n $ \(m :: Int) (x :: Int) ->
    fromPure2 replicateM m x `upperboundby` \_ _ -> 2 * max 1 (n + 1)

qc_replicateBound :: IO ()
qc_replicateBound = quickCheck $ \(n :: Int) (x :: Int) ->
    fromPure2 replicateM n x `upperboundby` \_ _ -> 2 * max 1 (n + 1)

-- The two below also work though not very interesting

qcN_replicateBound1 :: Int -> IO ()
qcN_replicateBound1 n = quickCheckN n $ \(x :: Int) ->
    fromPure2 replicateM n x `upperboundWith` fullDemand $ \_ _ -> 2 * max 1 (n + 1)

qcN_replicateBound' :: Int -> IO ()
qcN_replicateBound' n = quickCheckN n $ \(x :: Int) ->
    fromPure2 replicateM n x `upperboundby` \_ d ->
        2 * min (max 1 (n + 1)) ((sizeD 0 d) + 1)

--------------------------------------------------------------------------------

-- Examples involving higher-order functions

{-
    map :: (a -> b) -> [a] -> [b]
    map _ []     = []
    map f (x:xs) = f x : map f xs
-}
mapM :: (Th a -> MemoristM b) -> Th (ListT a) -> MemoristM (ListT b)
mapM fM txs = do
    tick
    xs <- force txs
    case xs of
        NilT -> return NilT
        ConsT ty tys -> do
            tz <- lazy $ fM ty
            tzs <- lazy $ mapM fM tys
            return $ ConsT tz tzs

{-
    foldr :: (a -> b -> b) -> b -> [a] -> b
    foldr k z = go
          where
            go []     = z
            go (y:ys) = y `k` go ys

    --> 
    foldr k z [] = z
    foldr k z (x:xs) = let acc = foldr k z xs in x `k` acc

-}
foldrM :: (Th a -> Th b -> MemoristM b) -> Th b -> Th (ListT a) -> MemoristM b
foldrM kM tz txs = do
    tick
    xs <- force txs
    case xs of
        NilT -> force tz
        ConsT ty tys -> do
            ta <- lazy $ foldrM kM tz tys
            kM ty ta

{-
-- foldl classical implementation

    foldl :: (b -> a -> b) -> b -> [a] -> b
    foldl k z [] = z
    foldl k z (x:xs) = let z' = z `k` x in foldl k z' xs
-}
foldlM :: (Th b -> Th a -> MemoristM b) -> Th b -> Th (ListT a) -> MemoristM b
foldlM kM tz txs = do
    tick
    xs <- force txs
    case xs of
        NilT -> force tz
        ConsT ty tys -> do
            tz' <- lazy $ kM tz ty
            foldlM kM tz' tys

{-
    concat :: [[a]] -> [a]
    concat = foldr (++) []
-}
concatM :: Th (ListT (ListT a)) -> MemoristM (ListT a)
concatM txs = do
    tick
    tz <- lazy $ return NilT
    foldrM appendM tz txs

prop_concatMUBound :: (ReprDemandArb a, QC.Arbitrary a) => [[a]] -> QC.Property
prop_concatMUBound xss = fromPure1 concatM xss `upperboundby` \_ _ ->
    -- 2 * (sizeD 1 d + length xss) + 1
    2 * length xss + length (concat xss) + 2

qcN_concatMUBound :: Int -> IO ()
qcN_concatMUBound n = quickCheckN n (prop_concatMUBound :: [[Int]] -> QC.Property)

-- prop_concatMUBound' :: (ReprDemandArb a, QC.Arbitrary a) => [[a]] -> Bool
-- prop_concatMUBound' xss = fromPure1 concatM xss `upperboundWith` fullDemand $ \_ d ->
--     2 * (sizeD 1 d + length xss) + 1

-- qcN_concatMUBound' :: Int -> IO ()
-- qcN_concatMUBound' n = quickCheckN n (prop_concatMUBound' :: [[Int]] -> Bool)

cost_concatM :: ReprDemand a => [[a]] -> (Rep [a] -> Dem (Rep [a])) -> Cost
cost_concatM xss = infcost (fromPure1 concatM xss)

concatM' :: Th (ListT (ListT a)) -> MemoristM (ListT a)
concatM' txs = do
    tick
    tz <- lazy $ return NilT
    foldlM appendM tz txs

prop_concatM'UBound :: (ReprDemandArb a, QC.Arbitrary a) => [[a]] -> QC.Property
prop_concatM'UBound xss = fromPure1 concatM' xss `upperboundby` \_ _ ->
    2 * length xss + length (concat xss) + 10

qcN_concatM'UBound :: Int -> IO ()
qcN_concatM'UBound n = quickCheckN n (prop_concatM'UBound :: [[Int]] -> QC.Property)
-- *** Failed! Falsified (after 105 tests and 6 shrinks):     
-- [[0],[],[]]
-- ConsD (Need 0) (Need NilD)

cost_concatM' :: ReprDemand a => [[a]] -> (Rep [a] -> Dem (Rep [a])) -> Cost
cost_concatM' xss = infcost (fromPure1 concatM' xss)

-- ttt1 = (cost_concatM' xss (\_ -> d), 2 * length xss + length (concat xss) + 2)
--     where xss = [[0],[],[]] :: [[Int]]
--           d = ConsD (Need 0) (Need NilD)
-- -- 10, 9

-- The example is not very informative though!

-- NOTE: Testing with larger constants;
-- Eg. 2 * (length xss + length (concat xss)) + 8
--
-- ghci> qcN_concatM'UBound 1000
-- *** Failed! Falsified (after 12 tests and 19 shrinks):    
-- [[0],[0,0,0],[],[],[]]
-- ConsD (Need 0) (Need (ConsD (Need 0) (Need (ConsD (Need 0) (Need (ConsD (Need 0) (Need NilD)))))))
--
-- ttt2 = (cost_concatM' xss (\_ -> d), 2 * length xss + length (concat xss) + 2)
--     where xss = [[0],[0,0,0],[],[],[]] :: [[Int]]
--           d = ConsD (Need 0) (Need (ConsD (Need 0) (Need (ConsD (Need 0) (Need (ConsD (Need 0) (Need NilD)))))))
-- -- (25, 16)
-- Slightly bigger difference but...
-- 

-- For comparison, a handpicked example
-- let xss = ([[1..20],[2..16],[3..12],[4..8],[5]]::[[Int]]) in (cost_concatM' xss fullDemand, 2 * length xss + length (concat xss) + 2)
-- -- (162,63)
