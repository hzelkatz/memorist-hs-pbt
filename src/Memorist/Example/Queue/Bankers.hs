{-# LANGUAGE TypeFamilies #-}

module Memorist.Example.Queue.Bankers where

import Memorist.Memorist as M
import Memorist.Data.List
import Memorist.Example.Queue.Base as Q
import Memorist.Example.List ( appendM, reverseM )
import Memorist.Example.Util ( quickCheckN )

import Test.QuickCheck as QC


data Bankers a = Bankers !Int [a] !Int [a]
    deriving (Eq,Show)

instance Queue Bankers where

    empty = Bankers 0 [] 0 []

    enqueue (Bankers nf f nr r) x = check $ Bankers nf f (nr + 1) (x:r)

    dequeue (Bankers nf (x:f) nr r) =
        SMaybe $ Just $ SPair (x, check (Bankers (nf - 1) f nr r))
    dequeue _ = SMaybe Nothing

check :: Bankers a -> Bankers a
check q@(Bankers nf f nr r) =
    if nf < nr then Bankers (nf + nr) (f ++ reverse r) 0 [] else q

nfront :: Bankers a -> Int
nfront (Bankers nf _ _ _) = nf

nrear :: Bankers a -> Int
nrear (Bankers _ _ nr _) = nr

instance Arbitrary a => Arbitrary (Bankers a) where
    arbitrary = genBankers arbitrary

genBankers :: Gen a -> Gen (Bankers a)
genBankers gen = sized $ \n -> do
    k1 <- chooseInt (0,n)
    l1 <- vectorOf k1 gen
    let k2 = n - k1
    l2 <- vectorOf k2 gen
    -- invariant is nf >= nr
    if k1 >= k2 then return $ Bankers k1 l1 k2 l2
    else return $ Bankers k2 l2 k1 l1

data BankersT a = BankersT Int (Th (ListT a)) Int (Th (ListT a))
    deriving (Eq,Show)

instance Repr a => Repr (Bankers a) where
    type Rep (Bankers a) = BankersT (Rep a)

    reprM (Bankers nf f nr r) = do
        tf <- lazy $ reprM f
        tr <- lazy $ reprM r
        return $ BankersT nf tf nr tr

    abstract (BankersT nf tf nr tr) =
        Bankers nf (abstract (tval tf)) nr (abstract (tval tr))

instance QueueT BankersT where
    emptyM = do
        t1 <- lazy $ return NilT
        t2 <- lazy $ return NilT
        return $ BankersT 0 t1 0 t2
    
    enqueueM tq tx = do
        tick
        ~(BankersT nf tf nr tr) <- force tq
        tr' <- lazy $ return $ ConsT tx tr
        checkM $ BankersT nf tf (nr + 1) tr'
    
    dequeueM tq = do
        tick
        ~(BankersT nf tf nr tr) <- force tq
        f <- force tf
        case f of
            ConsT tx tf' -> do
                q <- checkM $ BankersT (nf - 1) tf' nr tr
                x <- force tx
                return $ Just (x,q)
            _ -> return Nothing

checkM :: BankersT a -> MemoristM (BankersT a)
checkM q@(BankersT nf tf nr tr) =
    if nf < nr then do
        t <- lazy $ reverseM tr
        tf' <- lazy $ appendM tf t
        tr' <- lazy $ return NilT
        return $ BankersT (nf + nr) tf' 0 tr'
    else return q

-- -- Correctness:
-- qcN_BankqEnqCorrect n = quickCheckN n $ \(q :: Bankers Int) (x :: Int) ->
--     correct (fromPure2 enqueueM q x) (enqueue q x)
-- qcN_BankqDeqCorrect n = quickCheckN n $ \(q :: Bankers Int) ->
--     correct (fromPure1 dequeueM q) (dequeue q)

instance Demand a => Demand (BankersT a) where
    type Dem (BankersT a) = (ThD (ListD (Dem a)), ThD (ListD (Dem a)))
    fullDemand (BankersT _ tf _ tr) = (fullDemand tf, fullDemand tr)
    usage (BankersT _ tf _ tr) (df, dr) = usage tf df `union` usage tr dr

instance Demand a => LBoundDemand (BankersT a) where minDemand _ = (Skip,Skip)

instance DemandArb a => DemandArb (BankersT a) where
    arbDemandFrom (BankersT _ tf _ tr) = do
        df <- arbDemandFrom tf
        dr <- arbDemandFrom tr
        return $ (df, dr)


instance HasPotential Bankers where
    potential (Bankers nf _ nr _) = max 0 (nf - nr)

instance HasPotential BankersT where
    potential (BankersT nf _ nr _) = max 0 (nf - nr)

-- We test specifically with 'fullDemand', i.e., demanding every portion of the queue.
-- Incidentally, the cost deriving using full demand correponds to what Okasaki
-- called "complete cost" in his book, i.e. cost of an operation if every thunk
-- created by it is evaluated, which is also the cost he used to calculate
-- the amortized cost in persistent usage case (along with potential changes).
--
-- But we cannot in general assert the cost under full demand is "exactly"
-- amortized cost + potential change, because in different case
-- (e.g. rotation-triggering or not) the exact amortized cost for the operation
-- can be slightly different.
prop_bankersAmortized :: ReprDemand a => Bankers a -> Op a -> Int -> Property
prop_bankersAmortized q op k =
    runOpFromPure q op `upperboundWith` fullDemand $ \v _ -> k + delta v
    where delta (Just q') = potential q' - potential q
          delta _         = 0

qcN_bankersEnqAmortized :: Int -> IO ()
qcN_bankersEnqAmortized n = quickCheckN n $ \q x -> prop_bankersAmortized q (Enq x :: Op Int) 4

qcN_bankersDeqAmortized :: Int -> IO ()
qcN_bankersDeqAmortized n = quickCheckN n $ \q -> prop_bankersAmortized q (Deq :: Op Int) 4

prop_bankersAmortized' :: ReprDemandArb a => Bankers a -> Op a -> Int -> Property
prop_bankersAmortized' q op k =
    runOpFromPure q op `upperboundby` \v _ -> k + delta v
    where delta (Just q') = potential q' - potential q
          delta _         = 0

qcN_bankersEnqAmortized' :: Int -> IO ()
qcN_bankersEnqAmortized' n = quickCheckN n $ \q x -> prop_bankersAmortized' q (Enq x :: Op Int) 4

qcN_bankersDeqAmortized' :: Int -> IO ()
qcN_bankersDeqAmortized' n = quickCheckN n $ \q -> prop_bankersAmortized' q (Deq :: Op Int) 4


-- A simple test that the cost is constant if amortized over the entire trace.
prop_bankersRunTraceCost :: ReprDemandArb a => Trace1 a -> Property
prop_bankersRunTraceCost t = runTraceFromPure (Q.empty :: Bankers a) t
    `upperboundWith` minDemand $ \_ _ -> 4 * traceSize t

qcN_bankersRunTraceCost :: Int -> IO ()
qcN_bankersRunTraceCost n = quickCheckN n (prop_bankersRunTraceCost :: Trace1 Int -> Property)

-- Variant that starts with arbitrary queue.
prop_bankersRunTraceCost' :: ReprDemandArb a => Bankers a -> Trace1 a -> Property
prop_bankersRunTraceCost' q t =
    runTraceFromPure q t `upperboundWith` minDemand $ \_ _ -> 4 * traceSize t

qcN_bankersRunTraceCost' :: Int -> IO ()
qcN_bankersRunTraceCost' n = quickCheckN n (prop_bankersRunTraceCost' :: Bankers Int -> Trace1 Int -> Property)
