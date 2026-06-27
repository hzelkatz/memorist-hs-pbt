{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

{-# LANGUAGE AllowAmbiguousTypes #-}

module Memorist.Example.Queue.Bankers where

import Memorist.Memorist as M
import Memorist.Data.List
import Memorist.Example.Queue.Base as Q
import Memorist.Example.List ( appendM, reverseM )
import Memorist.Example.Util

import Test.QuickCheck as QC

-- NOTE: only for internal testing
import Data.Tree
import Control.Monad (replicateM_)


data BankersQueue a = BankersQueue !Int [a] !Int [a]
    deriving (Eq,Show)

instance Queue BankersQueue where

    empty = BankersQueue 0 [] 0 []

    enqueue (BankersQueue nf f nr r) x = check $ BankersQueue nf f (nr + 1) (x:r)

    -- dequeue (BankersQueue nf (x:f) nr r) =
    --     Just (x, check (BankersQueue (nf - 1) f nr r))
    -- dequeue _ = Nothing
    dequeue (BankersQueue nf (x:f) nr r) =
        SMaybe $ Just $ SPair (x, check (BankersQueue (nf - 1) f nr r))
    dequeue _ = SMaybe Nothing

check :: BankersQueue a -> BankersQueue a
check q@(BankersQueue nf f nr r) =
    if nf < nr then BankersQueue (nf + nr) (f ++ reverse r) 0 [] else q

nfront :: BankersQueue a -> Int
nfront (BankersQueue nf _ _ _) = nf

nrear :: BankersQueue a -> Int
nrear (BankersQueue _ _ nr _) = nr

instance Arbitrary a => Arbitrary (BankersQueue a) where
    arbitrary = genBankers arbitrary

    {- -- We could've defined a shrinker but it doesn't seem to be helpful
       -- in practice?

        shrink (BankersQueue nf f _ r) =
            [ BankersQueue 0 [] 0 [] ] ++
            [ BankersQueue nf f 0 [] ] ++
            filter valid [ BankersQueue (length f') f' (length r') r'
                        | (f', r') <- shrink (f, r) ]
            where valid (BankersQueue nf' _ nr' _) = nf' >= nr'
    -}

genBankers :: Gen a -> Gen (BankersQueue a)
genBankers gen = sized $ \n -> do
    k1 <- chooseInt (0,n)
    l1 <- vectorOf k1 gen
    let k2 = n - k1
    l2 <- vectorOf k2 gen
    -- invariant is nf >= nr
    if k1 >= k2 then return $ BankersQueue k1 l1 k2 l2
    else return $ BankersQueue k2 l2 k1 l1

data BankersQueueT a = BankersQueueT Int (Th (ListT a)) Int (Th (ListT a))
    deriving (Eq,Show)

instance Repr a => Repr (BankersQueue a) where
    type Rep (BankersQueue a) = BankersQueueT (Rep a)

    reprM (BankersQueue nf f nr r) = do
        tf <- lazy $ reprM f
        tr <- lazy $ reprM r
        return $ BankersQueueT nf tf nr tr

    abstract (BankersQueueT nf tf nr tr) =
        BankersQueue nf (abstract (tval tf)) nr (abstract (tval tr))

instance QueueT BankersQueueT where
    emptyM = do
        t1 <- lazy $ return NilT
        t2 <- lazy $ return NilT
        return $ BankersQueueT 0 t1 0 t2
    
    enqueueM tq tx = do
        tick
        ~(BankersQueueT nf tf nr tr) <- force tq
        tr' <- lazy $ return $ ConsT tx tr
        checkM $ BankersQueueT nf tf (nr + 1) tr'
    
    dequeueM tq = do
        tick
        ~(BankersQueueT nf tf nr tr) <- force tq
        f <- force tf
        case f of
            ConsT tx tf' -> do
                q <- checkM $ BankersQueueT (nf - 1) tf' nr tr
                x <- force tx
                return $ Just (x,q)
            _ -> return Nothing

checkM :: BankersQueueT a -> MemoristM (BankersQueueT a)
checkM q@(BankersQueueT nf tf nr tr) =
    if nf < nr then do
        t <- lazy $ reverseM tr
        tf' <- lazy $ appendM tf t
        tr' <- lazy $ return NilT
        return $ BankersQueueT (nf + nr) tf' 0 tr'
    else return q


instance Demand a => Demand (BankersQueueT a) where
    type Dem (BankersQueueT a) = (ThD (ListD (Dem a)), ThD (ListD (Dem a)))
    fullDemand (BankersQueueT _ tf _ tr) = (fullDemand tf, fullDemand tr)
    usage (BankersQueueT _ tf _ tr) (df, dr) = usage tf df `union` usage tr dr

instance Demand a => LBoundDemand (BankersQueueT a) where minDemand _ = (Skip,Skip)

instance DemandArb a => DemandArb (BankersQueueT a) where
    arbDemandFrom (BankersQueueT _ tf _ tr) = do
        df <- arbDemandFrom tf
        dr <- arbDemandFrom tr
        return $ (df, dr)


instance HasPotential BankersQueue where
    potential (BankersQueue nf _ nr _) = max 0 (nf - nr)

instance HasPotential BankersQueueT where
    potential (BankersQueueT nf _ nr _) = max 0 (nf - nr)


-- NOTE to self: using the interface that specify cost bounds based on pure values
-- causes some issues. If we generalize enough it doesn't typecheck because of
-- ambiguous types (possibly related to type family injectivity).
-- I think it might be becoz we essentially have (ReprDemand a, a1 ~ Rep a, a2 ~ Dem a1)
-- declared in the context, but during type inference, Haskell can only infer up
-- to this shape of chain (so sth like ReprDemand b, b1 ~ Rep b, b2 ~ Dem b1)
-- but cannot unify them with the a type, because the family is noninejctive
-- and there is no guarantee that if a2 = b2 then it must be a = b?
-- Because if we look at the version using `exactlyWith` which only works on `Demand a`,
-- Then its fine even with polymorphic types.
-- 
-- If we instantiate to concrete type with no args, it typechecks but only if we also
-- write out the instantiated type for exactlyWith'.
--
-- prop_bankersAmortized :: (Repr a, a1 ~ Rep a, Demand a1, a2 ~ Dem a1) => BankersQueue a -> Op a -> Int -> Bool
-- prop_bankersAmortized q op k =
--     -- exactlyWith'
--     -- (exactlyWith' :: MemoristM (Maybe (BankersQueueT (Rep a))) -> (Maybe (BankersQueueT (Rep a)) -> Maybe (ThD (ListD (Dem (Rep a))), ThD (ListD (Dem (Rep a))))) -> (SMaybe (BankersQueue a) -> Maybe (ThD (ListD (Dem (Rep a))), ThD (ListD (Dem (Rep a)))) -> Int) -> Bool)
--     (exactlyWith' :: MemoristM (Maybe (BankersQueueT a1)) -> (Maybe (BankersQueueT a1) -> Maybe (ThD (ListD a2), ThD (ListD a2))) -> (SMaybe (BankersQueue a) -> Maybe (ThD (ListD a2), ThD (ListD a2)) -> Int) -> Bool)
--         m fullDemand $ \v _ -> k -- + delta v
--     where m = runOpFromPure q op
--
-- prop_bankersAmortized :: BankersQueue Int -> Op Int -> Int -> Bool
-- prop_bankersAmortized q op k =
--     -- exactlyWith'
--     (exactlyWith' :: MemoristM (Maybe (BankersQueueT Int)) -> (Maybe (BankersQueueT Int) -> Maybe (ThD (ListD Int), ThD (ListD Int))) -> (SMaybe (BankersQueue Int) -> Maybe (ThD (ListD Int), ThD (ListD Int)) -> Int) -> Bool)
--         m fullDemand $ \v _ -> k -- + delta v
--     where m = runOpFromPure q op

-- amortized cost = complete cost - potential change
prop_bankersAmortized :: ReprDemandArb a => BankersQueue a -> Op a -> Int -> Property
prop_bankersAmortized q op k =
    runOpFromPure q op `upperboundby` \v _ -> k + delta v
    where delta (Just q') = potential q' - potential q
          delta _         = 0

qcN_bankersEnqAmortized :: Int -> IO ()
qcN_bankersEnqAmortized n = quickCheckN n $ \q -> prop_bankersAmortized q (Enq 42 :: Op Int) 4
-- before [] [], pot = 0, then r=1, rot []++r' [] takes 1 for append + 3 for rev, pot = 1
-- cost = 1+1+3=5, delta=1, amort = 5-1=4

qcN_bankersDeqAmortized :: Int -> IO ()
qcN_bankersDeqAmortized n = quickCheckN n $ \q -> prop_bankersAmortized q (Deq :: Op Int) 4
-- before f = r, pot = 0, then f-1, rot f-1++r' [], takes f for append + r+2 for rev, pot = f-1+r
-- cost = 1+f+r+2=f+r+3, delta=f+r-1-0, amort=f+r+3-(f+r-1)=4

-- NOTE: alternatively we specify to always test with 'fullDemand', i.e.,
-- demanding every portion of the queue.
-- Incidentally, the cost deriving using full demand correponds to what Okasaki
-- called "complete cost" in his book, i.e. cost of an operation if every thunk
-- created by it is evaluated, which is also the cost he used to calculate
-- the amortized cost in persistent usage case (along with potential changes).
--
-- But we cannot in general assert the cost under full demand is "exactly"
-- amortized cost + potential change, because in different case
-- (e.g. rotation-triggering or not) the exact amortized cost for the operation
-- can be slightly different.
-- 
-- One slight issue with using fullDemand: it is much slower than using QuickCheck's
-- 'forAll' combinator on all possible demand generated based on resulting value.

prop_bankersAmortized1 :: ReprDemand a => BankersQueue a -> Op a -> Int -> Bool
prop_bankersAmortized1 q op k =
    runOpFromPure q op `upperboundWith` fullDemand $ \v _ -> k + delta v
    where delta (Just q') = potential q' - potential q
          delta _         = 0

qcN_bankersEnqAmortized1 :: Int -> IO ()
qcN_bankersEnqAmortized1 n = quickCheckN n $ \q -> prop_bankersAmortized1 q (Enq 42 :: Op Int) 4

qcN_bankersDeqAmortized1 :: Int -> IO ()
qcN_bankersDeqAmortized1 n = quickCheckN n $ \q -> prop_bankersAmortized1 q (Deq :: Op Int) 4


-- A simple test that the cost is constant if amortized over the entire trace.
prop_bankersRunTraceCost :: ReprDemandArb a => Trace1 a -> Bool
prop_bankersRunTraceCost t =
    runTraceFromPure (Q.empty :: BankersQueue a) t `upperboundWith` minDemand $ \_ _ -> 4 * traceSize t

qcN_bankersRunTraceCost :: Int -> IO ()
qcN_bankersRunTraceCost n = quickCheckN n (prop_bankersRunTraceCost :: Trace1 Int -> Bool)

-- Variant that starts with arbitrary queue.
prop_bankersRunTraceCost' :: ReprDemandArb a => BankersQueue a -> Trace1 a -> Bool
prop_bankersRunTraceCost' q t =
    runTraceFromPure q t `upperboundWith` minDemand $ \_ _ -> 4 * traceSize t

qcN_bankersRunTraceCost' :: Int -> IO ()
qcN_bankersRunTraceCost' n = quickCheckN n (prop_bankersRunTraceCost' :: BankersQueue Int -> Trace1 Int -> Bool)

-- Fixed to full demand. NOTE: just for experiment; this does not hold in general.
prop_bankersRunTraceCost1 :: ReprDemandArb a => Trace1 a -> Bool
prop_bankersRunTraceCost1 t =
    runTraceFromPure (Q.empty :: BankersQueue a) t `upperboundWith` fullDemand $
        \_ _ -> 4 * traceSize t

qcN_bankersRunTraceCost1 :: Int -> IO ()
qcN_bankersRunTraceCost1 n = quickCheckN n (prop_bankersRunTraceCost1 :: Trace1 Int -> Bool)

-- -----------------------------------------------------------------------------

batch_bankers :: Int -> Int -> IO ()
batch_bankers k j = replicateM_ j $
    putStrLn "qcN_bankersEnqAmortized" >> qcN_bankersEnqAmortized k
    >>
    putStrLn "qcN_bankersDeqAmortized" >> qcN_bankersDeqAmortized k
    >>
    -- putStrLn "qcN_bankersEnqAmortized1" >> qcN_bankersEnqAmortized1 k
    -- >>
    -- putStrLn "qcN_bankersDeqAmortized1" >> qcN_bankersDeqAmortized1 k
    -- >>
    putStrLn "qcN_bankersRunTraceCost" >> qcN_bankersRunTraceCost k
    -- >>
    -- putStrLn "qcN_bankersRunTraceCost'" >> qcN_bankersRunTraceCost' k

qctestop :: BankersQueue Int -> Op Int -> Int -> IO ()
qctestop q op k = quickCheckN 1 $ prop_bankersAmortized q op k

qctesttrace :: Trace1 Int -> IO ()
qctesttrace t = quickCheckN 1 $ prop_bankersRunTraceCost t

qctesttrace' :: BankersQueue Int -> Trace1 Int -> IO ()
qctesttrace' q t = quickCheckN 1 $ prop_bankersRunTraceCost' q t

qctesttrace1 :: Trace1 Int -> IO ()
qctesttrace1 t = quickCheckN 1 $ prop_bankersRunTraceCost1 t

tracecost :: BankersQueue Int -> Trace1 Int -> Cost
tracecost q t = infcost (runTraceFromPure q t) minDemand

{-
q1 :: BankersQueue Int
q1 = BankersQueue 14 [3,-1,-18,9,14,9,18,7,-12,8,7,14,16,11] 2 [18,17]
t1 :: RanTrace Int
t1 = RanTrace $ Node Deq [Node (Enq (-5)) [Node Deq [Node (Enq 3) [Node (Enq (-7))[Node (Enq 0) []]]]]]

q2 :: BankersQueue Int
q2 = BankersQueue 14 [-9,0,6,-9,-10,5,-1,17,10,1,-6,-6,7,-5] 14 [-11,10,2,8,-12,7,-5,0,15,8,-12,11,5,-17]
t2 :: RanTrace Int
t2 = RanTrace $ Node (Enq 5) []
-- ^ This will fails RunTraceCost if we do not fix the demand to minDemand

q3 :: BankersQueue Int
q3 = BankersQueue 1 [1] 1 [2]
t3 :: RanTrace Int
t3 = RanTrace $ Node Deq [Node Deq []]
-}
