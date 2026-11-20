{-# LANGUAGE TypeFamilies #-}

-- A 'lazy' variant of the batched queue in which we use lazy lists
-- (similar to banker's queue) internally.
-- In fact, if we write the definitions using ordinary lists in Haskell,
-- it is actually a lazy-list variant that we model here,
-- not the version analysed in Okasaki's book (which is fully strict).

module Memorist.Example.Queue.BatchedLazy where

import Memorist.Memorist as M
import Memorist.Data.List
import Memorist.Example.Queue.Base as Q
import Memorist.Example.List ( reverseM )
import Memorist.Example.Util

import Test.QuickCheck as QC

-- Only for internal testing
import Data.Tree
import Control.Monad (replicateM_)

data Batched a = Batched [a] [a]
    deriving (Eq,Show)

instance Queue Batched where
    empty = Batched [] []

    enqueue (Batched f r) x = check $ Batched f $ (x : r)

    dequeue (Batched [] _) = SMaybe Nothing
    dequeue (Batched (x:f) r) =
        SMaybe $ Just $ SPair (x, check (Batched f r))

check :: Batched a -> Batched a
check (Batched [] r) = Batched (reverse r) []
check q = q

instance Arbitrary a => Arbitrary (Batched a) where
    arbitrary = do
        f <- arbitrary
        case f of
            [] -> return $ Q.empty
            _ -> return . Batched f =<< arbitrary

    shrink =
        filter valid . shrinkMap wrap unwrap
        where unwrap (Batched f r) = (f,r)
              wrap (f,r) = Batched f r
              valid (Batched [] (_:_)) = False
              valid _                     = True


data BatchedT a = BatchedT (Th (ListT a)) (Th (ListT a))
    deriving (Eq,Show)

instance Repr a => Repr (Batched a) where
    type Rep (Batched a) = BatchedT (Rep a)
    reprM (Batched f r) = liftA2 BatchedT (lazy (reprM f)) (lazy (reprM r))
    abstract (BatchedT f r) = Batched (abstract (tval f)) (abstract (tval r))

instance QueueT BatchedT where
    emptyM = liftA2 BatchedT tn tn where tn = lazy $ return NilT

    enqueueM tq tx = do
        tick
        ~(BatchedT tf tr) <- force tq
        tr' <- lazy $ return $ ConsT tx tr
        checkM $ BatchedT tf tr'

    dequeueM tq = do
        tick
        ~(BatchedT tf tr) <- force tq
        f <- force tf
        case f of
            NilT -> return Nothing
            ConsT tx tf' -> do
                q <- checkM $ BatchedT tf' tr
                x <- force tx
                return $ Just (x, q)

checkM :: BatchedT a -> MemoristM (BatchedT a)
checkM q@(BatchedT tf tr) = do
    f <- force tf
    case f of
        NilT -> do
            tr' <- lazy $ reverseM tr
            tn <- lazy $ return NilT
            return $ BatchedT tr' tn
        _ -> return q

-- -- Correctness:
-- qcN_batchedEnqCorrect n = quickCheckN n $ \(q :: Batched Int) (x :: Int) ->
--     correct (fromPure2 enqueueM q x) (enqueue q x)
-- qcN_batchedDeqCorrect n = quickCheckN n $ \(q :: Batched Int) ->
--     correct (fromPure1 dequeueM q) (dequeue q)

instance Demand a => Demand (BatchedT a) where
    type Dem (BatchedT a) = (ThD (ListD (Dem a)), ThD (ListD (Dem a)))
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
    potential (Batched _ r) = length r

instance HasPotential (BatchedT) where
    potential (BatchedT _ r) = sizeT 0 (tval r)


-- | Traditionally, amortized analysis considers credits.
-- Cheap operations save up credits while expensive ones spend them.
-- When analyzed using the physicist's method, potentials measure how much
-- credits can be saved at the least (i.e. an lower bound).
-- Correspondingly, the amortized cost is computed by
--      amortized cost = actual cost + potential change.
-- Equivalently, we want to assert that
--      actual cost <= k - potential change
-- for some constant k that is an upper bound on the amortized cost.
prop_batchedlAmortized :: ReprDemandArb a => Batched a -> Op a -> Int -> Property
prop_batchedlAmortized q op k =
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
qcN_batchedlEnqAmortized :: Int -> IO ()
qcN_batchedlEnqAmortized n = quickCheckN n $ \q x -> prop_batchedlAmortized q (Enq x :: Op Int) 4

-- | Dequeue that does not trigger a rotation does not change potential either.
-- Dequeue that triggers a rotation has to invoke reverse which has O(n) cost
-- where n is the length of the rear list (more specifically n + 2),
-- but it also decreases the potential by n.
-- The amortized cost should at most be 1+(n+2)-n = 3.
qcN_batchedlDeqAmortized :: Int -> IO ()
qcN_batchedlDeqAmortized n = quickCheckN n $ \q -> prop_batchedlAmortized q (Deq :: Op Int) 3


-- NOTE: using 5* instead rarely produces any counterexample, though there still are some.
-- One example is found after 20499 tests with a condition `traceSize t > 100`.
-- Using implication results in too many discarded tests; we might want a customized generator.
-- I doubt that using this method, we probably need very large trace,
-- unless there are indeed smaller examples and effective generators.
prop_batchedlRunTraceCost :: (ReprDemandArb a, LBoundDemand (Rep a), Trace t) => t a -> Property
prop_batchedlRunTraceCost t =
    runTraceFromPure (Q.empty :: Batched a) t `upperboundWith` minDemand $ \_ _ -> 4 * traceSize t

-- This should hold: it is a nonbranching sequence of operators (i.e. no persistent usage).
qcN_batchedlRunSeqCost :: Int -> IO ()
qcN_batchedlRunSeqCost n = quickCheckN n (prop_batchedlRunTraceCost :: SeqTrace Int -> Property)

-- In principle this does not hold. This trace generator tends to work better with
-- finding counterexamples for batched queue.
-- That said, for this version, is much harder to find counterexamples in general.
qcN_batchedlRunLSTraceCost :: Int -> IO ()
qcN_batchedlRunLSTraceCost n = quickCheckN n (prop_batchedlRunTraceCost :: LSTrace Int -> Property)

-- This trace generator generates potentially branching traces, but is much less
-- effective at finding counterexamples.
qcN_batchedlRunRanTraceCost :: Int -> IO ()
qcN_batchedlRunRanTraceCost n = quickCheckN n (prop_batchedlRunTraceCost :: RanTrace Int -> Property)

-- -----------------------------------------------------------------------------

batch_batched :: Int -> Int -> IO ()
batch_batched k j = replicateM_ j $
    putStrLn "qcN_batchedEnqAmortized" >> qcN_batchedlEnqAmortized k
    >>
    putStrLn "qcN_batchedDeqAmortized" >> qcN_batchedlDeqAmortized k
    >>
    putStrLn "qcN_batchedRunSeqCost" >> qcN_batchedlRunSeqCost k
    -- >>
    -- putStrLn "qcN_batchedRunLSTraceCost" >> qcN_batchedRunLSTraceCost k 
