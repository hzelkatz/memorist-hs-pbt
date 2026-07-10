{-# LANGUAGE TypeFamilies #-}

module Memorist.Example.Queue.Batched where

import Memorist.Memorist as M
import Memorist.Data.List
import Memorist.Example.Queue.Base as Q
import Memorist.Example.Util

import Test.QuickCheck as QC


data Batched a = Batched (SList a) (SList a)
    deriving (Eq,Show)

instance Queue Batched where
    empty = Batched (SList []) (SList [])

    enqueue (Batched f r) x = check $ Batched f $ SList (x : fromSList r)

    dequeue (Batched (SList []) _) = SMaybe Nothing
    dequeue (Batched (SList (x:f)) r) =
        SMaybe $ Just $ SPair (x, check (Batched (SList f) r))

check :: Batched a -> Batched a
check (Batched (SList []) (SList r)) = Batched (SList (reverse r)) (SList [])
check q = q

instance Arbitrary a => Arbitrary (Batched a) where
    arbitrary = do
        f <- arbitrary
        case f of
            [] -> return $ Batched (SList []) (SList [])
            _ -> return . Batched (SList f) =<< arbitrary

    shrink =
        filter valid . shrinkMap wrap unwrap
        where unwrap (Batched (SList f) (SList r)) = (f,r)
              wrap (f,r) = Batched (SList f) (SList r)
              valid (Batched (SList []) (SList (_:_))) = False
              valid _                                       = True

data BatchedT a = BatchedT [a] [a]
    deriving (Eq,Show)

instance Repr a => Repr (Batched a) where
    type Rep (Batched a) = BatchedT (Rep a)
    reprM (Batched f r) = liftA2 BatchedT (reprM f) (reprM r)
    abstract (BatchedT f r) = Batched (abstract f) (abstract r)

instance QueueT BatchedT where
    emptyM = liftA2 BatchedT tn tn where tn = return []

    enqueueM tq tx = do
        tick
        ~(BatchedT f r) <- force tq
        x <- force tx
        checkM $ BatchedT f (x:r)

    dequeueM tq = do
        tick
        ~(BatchedT f r) <- force tq
        case f of
            [] -> return Nothing
            x:f' -> do
                q' <- checkM $ BatchedT f' r
                return $ Just (x, q')

checkM :: BatchedT a -> MemoristM (BatchedT a)
checkM (BatchedT [] r) = do
    r' <- reverseM r
    return (BatchedT r' [])
checkM q = return q

-- -- Correctness:
-- qcN_batchedEnqCorrect n = quickCheckN n $ \(q :: Batched Int) (x :: Int) ->
--     correct (fromPure2 enqueueM q x) (enqueue q x)
-- qcN_batchedDeqCorrect n = quickCheckN n $ \(q :: Batched Int) ->
--     correct (fromPure1 dequeueM q) (dequeue q)

-- We need a Memorist translation of reverse on the strict variant.
reverseM :: [a] -> MemoristM [a]
reverseM xs = tick >> revM xs []

revM :: [a] -> [a] -> MemoristM [a]
revM xs ys = do
    tick
    case xs of
        []   -> return ys
        x:xs' -> revM xs' (x:ys)

instance Demand a => Demand (BatchedT a) where
    type Dem (BatchedT a) = ([Dem a], [Dem a])
    fullDemand (BatchedT f r) = (fullDemand f, fullDemand r)
    usage (BatchedT f r) (df, dr) = usage f df `union` usage r dr

instance LBoundDemand a => LBoundDemand (BatchedT a) where
    minDemand (BatchedT f r) = (minDemand f, minDemand r)

instance DemandArb a => DemandArb (BatchedT a) where
    arbDemandFrom (BatchedT f r) = do
        df <- arbDemandFrom f
        dr <- arbDemandFrom r
        return $ (df, dr)


instance HasPotential (Batched)  where
    potential (Batched _ (SList r)) = length r

instance HasPotential (BatchedT) where
    potential (BatchedT _ r) = length r


-- | Traditionally, amortized analysis considers credits.
-- Cheap operations save up credits while expensive ones spend them.
-- When analyzed using the physicist's method, potentials measure how much
-- credits can be saved at the least (i.e. an lower bound).
-- Correspondingly, the amortized cost is computed by
--      amortized cost = actual cost + potential change.
-- Equivalently, we want to assert that
--      actual cost <= k - potential change
-- for some constant k that is an upper bound on the amortized cost.
prop_batchedAmortized :: ReprDemandArb a => Batched a -> Op a -> Int -> Property
prop_batchedAmortized q op k =
    runOpFromPure q op `upperboundby` \v _ -> k - delta v
    where delta (Just q') = potential q' - potential q
          delta _         = 0

-- | Usually enqueue does not trigger a rotation but increases potential by 1.
-- The amortized cost should be 1+1 = 2.
-- The only case when it does is when both lists are empty to start with,
-- in which case the rotation always reverse a list of 1 element.
-- Reversal takes O(n) cost in terms of length of the rear list.
-- Because we ticks at every step of reverse and its auxiliary function,
-- the reversal cost is n + 2 more specifically.
-- The amortized cost should then be 1 + (1+2) = 4.
qcN_batchedEnqAmortized :: Int -> IO ()
qcN_batchedEnqAmortized n = quickCheckN n $ \q -> prop_batchedAmortized q (Enq 42 :: Op Int) 4

-- | Dequeue that does not trigger a rotation does not change potential either.
-- Dequeue that triggers a rotation has to invoke reverse which has O(n) cost
-- where n is the length of the rear list (more specifically n + 2),
-- but it also decreases the potential by n.
-- The amortized cost should at most be 1+(n+2)-n = 3.
qcN_batchedDeqAmortized :: Int -> IO ()
qcN_batchedDeqAmortized n = quickCheckN n $ \q -> prop_batchedAmortized q (Deq :: Op Int) 3


prop_batchedRunTraceCost :: (ReprDemandArb a, LBoundDemand (Rep a), Trace t) => t a -> Property
prop_batchedRunTraceCost t =
    runTraceFromPure (Q.empty :: Batched a) t `upperboundWith` minDemand $ \_ _ -> 4 * traceSize t

-- This should hold: it is a nonbranching sequence of operators (i.e. no persistent usage).
qcN_batchedRunSeqCost :: Int -> IO ()
qcN_batchedRunSeqCost n = quickCheckN n (prop_batchedRunTraceCost :: SeqTrace Int -> Property)

-- In principle this does not hold. This trace generator tends to work better with
-- finding counterexamples for batched queue.
qcN_batchedRunLSTraceCost :: Int -> IO ()
qcN_batchedRunLSTraceCost n = quickCheckN n (prop_batchedRunTraceCost :: LSTrace Int -> Property)

-- This trace generator seems less effective in finding counterexamples.
qcN_batchedRunRanTraceCost :: Int -> IO ()
qcN_batchedRunRanTraceCost n = quickCheckN n (prop_batchedRunTraceCost :: RanTrace Int -> Property)
