{-# LANGUAGE TypeFamilies #-}

module Memorist.Example.Queue.Batched where

import Memorist.Memorist as M
import Memorist.Data.List
import Memorist.Example.Queue.Base as Q

import Test.QuickCheck as QC

-- Only for internal testing
import Data.Tree
import Control.Monad (replicateM_)


data BatchedQueue a = BatchedQueue (SList a) (SList a)
    deriving (Eq,Show)

instance Queue BatchedQueue where
    empty = BatchedQueue (SList []) (SList [])

    enqueue (BatchedQueue f r) x = check $ BatchedQueue f $ SList (x : fromSList r)

    -- dequeue (BatchedQueue [] _) = Nothing
    -- dequeue (BatchedQueue (x:f) r) = Just (x, check (BatchedQueue f r))
    dequeue (BatchedQueue (SList []) _) = SMaybe Nothing
    dequeue (BatchedQueue (SList (x:f)) r) =
        SMaybe $ Just $ SPair (x, check (BatchedQueue (SList f) r))

check :: BatchedQueue a -> BatchedQueue a
check (BatchedQueue (SList []) (SList r)) = BatchedQueue (SList (reverse r)) (SList [])
check q = q

instance Arbitrary a => Arbitrary (BatchedQueue a) where
    arbitrary = do
        f <- arbitrary
        case f of
            [] -> return $ BatchedQueue (SList []) (SList [])
            _ -> do
                r <- arbitrary
                return $ BatchedQueue (SList f) r

    shrink =
        filter valid . shrinkMap wrap unwrap
        where unwrap (BatchedQueue (SList f) (SList r)) = (f,r)
              wrap (f,r) = BatchedQueue (SList f) (SList r)
              valid (BatchedQueue (SList []) (SList (_:_))) = False
              valid _                                       = True


data BatchedQueueT a = BatchedQueueT [a] [a]
    deriving (Eq,Show)

instance Repr a => Repr (BatchedQueue a) where
    type Rep (BatchedQueue a) = BatchedQueueT (Rep a)
    reprM (BatchedQueue f r) = liftA2 BatchedQueueT (reprM f) (reprM r)
    abstract (BatchedQueueT f r) = BatchedQueue (abstract f) (abstract r)

instance QueueT BatchedQueueT where
    emptyM = liftA2 BatchedQueueT tn tn where tn = return []

    enqueueM tq tx = do
        tick
        ~(BatchedQueueT f r) <- force tq
        x <- force tx
        checkM $ BatchedQueueT f (x:r)

    dequeueM tq = do
        tick
        ~(BatchedQueueT f r) <- force tq
        case f of
            [] -> return Nothing
            x:f' -> do
                q' <- checkM $ BatchedQueueT f' r
                return $ Just (x, q')

checkM :: BatchedQueueT a -> MemoristM (BatchedQueueT a)
checkM (BatchedQueueT [] r) = do
    r' <- reverseM r
    return $ BatchedQueueT r' []
checkM q = return q

-- We need a Memorist translation of reverse on the strict variant.
reverseM :: [a] -> MemoristM [a]
reverseM xs = tick >> revM xs []

revM :: [a] -> [a] -> MemoristM [a]
revM xs ys = do
    tick
    case xs of
        []   -> return ys
        x:xs' -> revM xs' (x:ys)

-- prop_rev :: [Int] -> Property
-- prop_rev l = reverseM l `exactly` \_ _ -> length l + 2

instance Demand a => Demand (BatchedQueueT a) where
    type Dem (BatchedQueueT a) = ([Dem a], [Dem a])
    fullDemand (BatchedQueueT f r) = (fullDemand f, fullDemand r)
    usage (BatchedQueueT f r) (df, dr) = usage f df `union` usage r dr

-- instance LBoundDemand a => LBoundDemand (BatchedQueueT a) where
--     minDemand (BatchedQueueT f r) = (minDemand f, minDemand r)

instance DemandArb a => DemandArb (BatchedQueueT a) where
    arbDemandFrom (BatchedQueueT f r) = do
        df <- arbDemandFrom f
        dr <- arbDemandFrom r
        return $ (df, dr)


instance HasPotential (BatchedQueue)  where
    potential (BatchedQueue _ (SList r)) = length r

instance HasPotential (BatchedQueueT) where
    potential (BatchedQueueT _ r) = length r


-- | Traditionally, amortized analysis considers credits.
-- Cheap operations save up credits while expensive ones spend them.
-- When analyzed using the physicist's method, potentials measure how much
-- credits can be saved at the least (i.e. an lower bound).
-- Correspondingly, the amortized cost is computed by
--      amortized cost = actual cost + potential change.
-- Equivalently, we want to assert that
--      actual cost <= k - potential change
-- for some constant k that is an upper bound on the amortized cost.
prop_batchedAmortized :: ReprDemandArb a => BatchedQueue a -> Op a -> Int -> Property
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


prop_batchedRunTraceCost' :: (ReprDemandArb a, Trace t) => t a -> Property
prop_batchedRunTraceCost' t =
    runTraceFromPure (Q.empty :: BatchedQueue a) t `upperboundby` \_ _ -> 4 * traceSize t

prop_batchedRunSeqCost :: ReprDemandArb a => SeqTrace a -> Property
prop_batchedRunSeqCost = prop_batchedRunTraceCost'

prop_batchedRunTraceCost :: ReprDemandArb a => LSTrace a -> Property
prop_batchedRunTraceCost = prop_batchedRunTraceCost'

prop_batchedRunTraceCost1 :: ReprDemandArb a => RanTrace a -> Property
prop_batchedRunTraceCost1 = prop_batchedRunTraceCost'

qcN_batchedRunSeqCost :: Int -> IO ()
qcN_batchedRunSeqCost n = quickCheckN n (prop_batchedRunSeqCost :: SeqTrace Int -> Property)

qcN_batchedRunTraceCost :: Int -> IO ()
qcN_batchedRunTraceCost n = quickCheckN n (prop_batchedRunTraceCost :: LSTrace Int -> Property)

qcN_batchedRunTraceCost1 :: Int -> IO ()
qcN_batchedRunTraceCost1 n = quickCheckN n (prop_batchedRunTraceCost1 :: RanTrace Int -> Property)

-- -----------------------------------------------------------------------------

batch_batched :: Int -> Int -> IO ()
batch_batched k j = replicateM_ j $
    putStrLn "qcN_batchedEnqAmortized" >> qcN_batchedEnqAmortized k
    >>
    putStrLn "qcN_batchedDeqAmortized" >> qcN_batchedDeqAmortized k
    >>
    putStrLn "qcN_batchedRunSeqCost" >> qcN_batchedRunSeqCost k
    -- >>
    -- putStrLn "qcN_batchedRunTraceCost" >> qcN_batchedRunTraceCost k  -- expected failure


qctesttracebatched :: Trace t => t Int -> IO ()
qctesttracebatched t = quickCheckN 1 $ prop_batchedRunTraceCost' t

tracecostbatched :: Trace t => BatchedQueue Int -> t Int -> Cost
tracecostbatched q t = infcost (runTraceFromPure q t) fullDemand

q0 :: BatchedQueue Int
q0 = Q.empty

t10a :: RanTrace Int
t10a = RanTrace $ Node (Enq 1) [Node (Enq 2) [ Node (Enq 3) [Node (Enq 4) [Node (Enq 5) [Node (Enq 6) [
        Node Deq [ ] ]]]]]]
-- size = 7; actual cost = 17
-- Initial enqueue+rot = 1+(1+2)=4; then 5 enqueues; next deq triggers rot, 1+(5+2)=8
-- So total should be 4+5+8=17.

t10a2 :: RanTrace Int
t10a2 = RanTrace $ Node (Enq 1) [Node (Enq 2) [ Node (Enq 3) [Node (Enq 4) [Node (Enq 5) [Node (Enq 6) [
        Node Deq [],
        Node Deq [] ]]]]]]
-- size = 8; actual cost = 25, exactly one more copy of rot-triggering deq cost of 8.
-- This is already problematic (duplicating the work of reversal), but the cost
-- is too small to violate the bound 4 * traceSize.

t10a5 :: RanTrace Int
t10a5 = RanTrace $ Node (Enq 1) [Node (Enq 2) [ Node (Enq 3) [Node (Enq 4) [Node (Enq 5) [Node (Enq 6) [
        Node Deq [],
        Node Deq [],
        Node Deq [],
        Node Deq [],
        Node Deq [] ]]]]]]
-- size = 11, actual cost = 49 == 17+4*8
-- This fails the trace test as expected.
-- But the default generator for trace (RanTrace) often cannot discover counter example like this.
