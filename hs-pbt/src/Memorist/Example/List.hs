module Memorist.Example.List where

import Memorist.Memorist as M
import Memorist.Data.List
import Memorist.Example.Util
import Test.QuickCheck as QC
    ( quickCheck, Property, Arbitrary, NonEmptyList(getNonEmpty), (.&&.), (.||.), (==>), noShrinking )

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

-- An incorrect attempt (off by 1)
prop_appendBoundAttempt :: ReprDemandArb a => [a] -> [a] -> Property
prop_appendBoundAttempt xs ys =
    (m `upperboundby` \_ _ -> length xs) .&&.
    (m `upperboundby` \_ d -> sizeD 0 d)
    where m = fromPure2 appendM xs ys

qc_appendBoundAttempt :: IO ()
qc_appendBoundAttempt = quickCheck (prop_appendBoundAttempt :: [Int] -> [Int] -> Property)

-- Correctly specified
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

-- We try the linear bound first, which should usually be falsified
qcN_reverseNaiveCostFail :: Int -> IO ()
qcN_reverseNaiveCostFail n = quickCheckN n $ \(xs :: [Int]) ->
    fromPure1 reverseNaiveM xs `upperboundby` \_ _ -> 5 * (length xs + 10)

-- Tests without shrinking sometimes provide more interesting counterexamples
qcN_reverseNaiveCostFail' :: Int -> IO ()
qcN_reverseNaiveCostFail' n = quickCheckN n $ noShrinking $ \(xs :: [Int]) ->
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
    foldr :: (a -> b -> b) -> b -> [a] -> b
    foldr k z = go
          where
            go []     = z
            go (y:ys) = y `k` go ys
    ---(ANF)--->
    foldr k z [] = z
    foldr k z (x:xs) = let acc = foldr k z xs in x `k` acc
-}
foldrM :: Th (Th a -> Th b -> MemoristM b) -> Th b -> Th (ListT a) -> MemoristM b
foldrM tk tz txs = do
    tick
    xs <- force txs
    case xs of
        NilT -> force tz
        ConsT ty tys -> do
            k <- force tk
            ta <- lazy $ foldrM tk tz tys
            k ty ta

{-
-- foldl classical implementation

    foldl :: (b -> a -> b) -> b -> [a] -> b
    foldl k z [] = z
    foldl k z (x:xs) = let z' = z `k` x in foldl k z' xs
-}
foldlM :: Th (Th b -> Th a -> MemoristM b) -> Th b -> Th (ListT a) -> MemoristM b
foldlM tk tz txs = do
    tick
    xs <- force txs
    case xs of
        NilT -> force tz
        ConsT ty tys -> do
            k <- force tk
            tz' <- lazy $ k tz ty
            foldlM tk tz' tys

{-
    concat :: [[a]] -> [a]
    concat = foldr (++) []
-}
concatM :: Th (ListT (ListT a)) -> MemoristM (ListT a)
concatM txs = do
    tick
    ta <- lazy $ return appendM
    tz <- lazy $ return NilT
    foldrM ta tz txs

cost_concatM :: ReprDemand a => [[a]] -> (Rep [a] -> Dem (Rep [a])) -> Cost
cost_concatM xss = infcost (fromPure1 concatM xss)

qcN_concatMBound :: Int -> IO ()
qcN_concatMBound n = quickCheckN n $ \(xss :: [[Int]]) ->
    fromPure1 concatM xss `upperboundby` \_ d -> 2 * (sizeD 1 d + length xss) + 1

-- NOTE: alternative specification not in paper
qcN_concatMBound' :: Int -> IO ()
qcN_concatMBound' n = quickCheckN n $ \(xss :: [[Int]]) ->
    fromPure1 concatM xss `upperboundby` \_ _ -> 2 * length xss + length (concat xss) + 2

concatM' :: Th (ListT (ListT a)) -> MemoristM (ListT a)
concatM' txs = do
    tick
    ta <- lazy $ return appendM
    tz <- lazy $ return NilT
    foldlM ta tz txs

cost_concatM' :: ReprDemand a => [[a]] -> (Rep [a] -> Dem (Rep [a])) -> Cost
cost_concatM' xss = infcost (fromPure1 concatM' xss)

ttt1a = cost_concatM ([[0,0],[],[0,0],[0,0]]::[[Int]]) $ \_ -> ConsD (Need 0) (Need (ConsD Skip (Need (ConsD (Need 0) Skip))))
ttt1b = cost_concatM' ([[0,0],[],[0,0],[0,0]]::[[Int]]) $ \_ -> ConsD (Need 0) (Need (ConsD Skip (Need (ConsD (Need 0) Skip))))
ttt2a = cost_concatM ([[0,0,0,0],[0,0,0,0],[0],[0,0]]::[[Int]]) $ \_ -> ConsD (Need 0) (Need (ConsD (Need 0) (Need (ConsD (Need 0) (Need (ConsD (Need 0) Skip))))))
ttt2b = cost_concatM' ([[0,0,0,0],[0,0,0,0],[0],[0,0]]::[[Int]]) $ \_ -> ConsD (Need 0) (Need (ConsD (Need 0) (Need (ConsD (Need 0) (Need (ConsD (Need 0) Skip))))))

-- this will likely be falsified: the fold version of concat is nonlinear.
qcN_concatM'BoundWrong :: Int -> IO ()
qcN_concatM'BoundWrong n = quickCheckN n $ \(xss :: [[Int]]) ->
    fromPure1 concatM' xss `upperboundby` \_ d -> 2 * (sizeD 1 d + length xss) + 1

-- NOTE: alternative bound not in paper; also falsified
qcN_concatM'BoundWrong' :: Int -> IO ()
qcN_concatM'BoundWrong' n = quickCheckN n $ \(xss :: [[Int]]) ->
    fromPure1 concatM' xss `upperboundby` \_ _ -> 2 * length xss + length (concat xss) + 2

qcN_concatM'Bound :: Int -> IO ()
qcN_concatM'Bound n = quickCheckN n $ \(xss :: [[Int]]) ->
    fromPure1 concatM' xss `upperboundby` \_ d -> (sizeD 1 d + 1) * (length xss + 1)

-- qcN_concatM'LBound :: Int -> IO ()
-- qcN_concatM'LBound n = quickCheckN n $ \(xss :: [[Int]]) ->
--     disjoin $ replicate 10 $
--     fromPure1 concatM' xss `lowerboundby` \_ d -> sizeD 1 d * sizeD 1 d

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


{-
    map :: (a -> b) -> [a] -> [b]
    map _ []     = []
    map f (x:xs) = f x : map f xs
-}
mapM :: Th (Th a -> MemoristM b) -> Th (ListT a) -> MemoristM (ListT b)
mapM tf txs = do
    tick
    xs <- force txs
    case xs of
        NilT -> return NilT
        ConsT ty tys -> do
            f <- force tf
            tz <- lazy $ f ty
            tzs <- lazy $ mapM tf tys
            return $ ConsT tz tzs

-- NOTE: fusion examples including the mapSucc one should all work even
-- after -O2 optimized compilation since the optimization does not
-- optimize through monadic definitions afaik.
-- This means we can actually use this framework to compare fused vs unfused directly,
-- although obviously the underlying program (the unfused version) will
-- be less efficient to actually execute.

-- A fusion example: mapSucc
--      map succ . mapp succ     vs    map (succ . succ)
-- The former need one more pass over the input list.

mapSuccM1 :: Th (ListT Int) -> MemoristM (ListT Int)
mapSuccM1 txs = do
    tick
    tf <- lazy $ return succM
    tzs <- lazy $ mapM tf txs
    mapM tf tzs

mapSuccM2 :: Th (ListT Int) -> MemoristM (ListT Int)
mapSuccM2 txs = do
    tick
    tf <- lazy $ composeM succM succM
    mapM tf txs

succM :: Th Int -> MemoristM Int
succM tn = do
    tick
    n <- force tn
    return $ n + 1

-- mapSuccCost :: [Int] -> (Cost,Cost)
-- mapSuccCost xs = (infcost (fromPure1 mapSuccM1 xs) fullDemand, infcost (fromPure1 mapSuccM2 xs) fullDemand)

{-
    concatMap :: (a -> [b]) -> [a] -> [b]
    concatMap f = foldr ((++) . f) []
-}
concatMapM :: Th (Th a -> MemoristM (ListT b)) -> Th (ListT a) -> MemoristM (ListT b)
concatMapM tf txs = do
    tick
    f <- force tf
    g <- return $ curryKM $ appendM
    k <- composeM g f
    tk <- lazy $ return $ uncurryKM k
    tn <- lazy $ return NilT
    foldrM tk tn txs

{-
    concatMap' :: (a -> [b]) -> [a] -> [b]
    concatMap' f xs = concat $ map f xs
-}
concatMapM' :: Th (Th a -> MemoristM (ListT b)) -> Th (ListT a) -> MemoristM (ListT b)
concatMapM' tf txs = do
    tick
    tys <- lazy $ mapM tf txs
    concatM tys

singletonM :: Th a -> MemoristM (ListT a)
singletonM tx = do
    tick
    tn <- lazy $ return NilT
    return $ ConsT tx tn

cmsM1 :: Th (ListT a) -> MemoristM (ListT a)
cmsM1 txs = do
    tf <- lazy $ return singletonM
    concatMapM tf txs

cmsM2 :: Th (ListT a) -> MemoristM (ListT a)
cmsM2 txs = do
    tf <- lazy $ return singletonM
    concatMapM' tf txs

cmsCost :: [Int] -> (Cost,Cost)
cmsCost xs = (infcost (fromPure1 cmsM1 xs) fullDemand, infcost (fromPure1 cmsM2 xs) fullDemand)

{-
    NOTE on the two cms cost:
    For cmsM1:
    concat over list of n singletons is ~3n when demanding in full:
        - foldr over n element lists,
        - append actually 2n, each elemment in the element list takes 1,
            but each ([] ++ _) also takes 1, and there happens to
            be n elements inside inner lists in total *and* n inner lists (thus n of []++_)
    These above all get "truncated" proportionally if demanded less.
    Additionally consider applying f (the singleton function) to each element.
    So ~4n in total; with 1 constant cost to outermost concatMap.

    For cmsM2:
    Similar, but one additional pass. So ~5n in total.
-} 

qcN_cmsM1Bound :: Int -> IO ()
qcN_cmsM1Bound n = quickCheckN n $ \(xs :: [Int]) ->
    fromPure1 cmsM1 xs `upperboundby` \_ d -> 4 * sizeD 1 d + 1

-- If we test for slightly larger input, we can hope for a more informative counterexample.
qcN_cmsM2BoundWrong :: Int -> IO ()
qcN_cmsM2BoundWrong n = quickCheckN n $ \(xs :: [Int]) -> length xs > 10 ==>
    fromPure1 cmsM2 xs `upperboundby` \_ d -> 4 * sizeD 1 d + 1

qcN_cmsM2Bound :: Int -> IO ()
qcN_cmsM2Bound n = quickCheckN n $ \(xs :: [Int]) ->
    fromPure1 cmsM2 xs `upperboundby` \_ d -> 5 * sizeD 1 d + 1

{-
    filter _ []    = []
    filter pred (x:xs)
        | pred x         = x : filter pred xs
        | otherwise      = filter pred xs
-}
filterM :: Th (Th a -> MemoristM Bool) -> Th (ListT a) -> MemoristM (ListT a)
filterM tf txs = do
    xs <- force txs
    case xs of
        NilT -> return NilT
        ConsT ty tys -> do
            f <- force tf
            zs <- filterM tf tys
            b <- f ty
            if b then do
                tzs <- lazy $ return zs
                return $ ConsT ty tzs
            else return zs

{-
    zipWith :: (a->b->c) -> [a]->[b]->[c]
    zipWith f = go
    where
        go [] _ = []
        go _ [] = []
        go (x:xs) (y:ys) = f x y : go xs ys
    
    ------>
    
    zipWith f [] _ = []
    zipWith f _ [] = []
    zipWith f (x:xs) (y:ys) = f x y : zipWith f xs ys
-}
zipWithM :: Th (Th a -> Th b -> MemoristM c) -> Th (ListT a) -> Th (ListT b) -> MemoristM (ListT c)
zipWithM tf txs tys = do
    xs <- force txs
    case xs of
        NilT -> return NilT
        ConsT tx txs' -> do
            ys <- force tys
            case ys of
                NilT -> return NilT
                ConsT ty tys' -> do
                    f <- force tf
                    tz <- lazy $ f tx ty
                    tzs <- lazy $ zipWithM tf txs' tys'
                    return $ ConsT tz tzs

-- TODO: move the functions below elsewhere

{-
    (.) :: (b -> c) -> (a -> b) -> a -> c
    (.) f g = \x -> f (g x)
-}
-- No ticks for simplicity. Function composition is often inlined anyway.
composeM :: Memorist s m => (Th b -> m c) -> (Th a -> m b) -> m (Th a -> m c)
-- composeM f g = return $ \tx -> do
--     tz <- lazy $ g tx
--     f tz
composeM f g = return $ \tx -> lazy (g tx) >>= f

-- A variant that works on thunked functions.
composeTM :: Memorist s m => Th (Th b -> m c) -> Th (Th a -> m b) -> m (Th a -> m c)
composeTM tf tg = return $ \tx -> do
    g <- force tg
    tz <- lazy $ g tx
    f <- force tf
    f tz

curryKM :: Memorist s m => (Th a -> Th b -> m c) -> Th a -> m (Th b -> m c)
curryKM f = return . f

uncurryKM :: Memorist s m => (Th a -> m (Th b -> m c)) -> Th a -> Th b -> m c
uncurryKM f = \tx ty -> f tx >>= \g -> g ty
