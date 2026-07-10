{-# LANGUAGE TypeFamilies #-}

module Memorist.Example.Queue.Bankers where

import Memorist.Memorist as M
import Memorist.Data.List
import Memorist.Example.Queue.Base as Q
import Memorist.Example.List ( appendM, reverseM )
import Memorist.Example.Util

import Test.QuickCheck as QC

-- NOTE: only for internal testing
import Control.Monad (replicateM_)


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

    {- -- We could've defined a shrinker but it doesn't seem to be helpful
       -- in practice?

        shrink (Bankers nf f _ r) =
            [ Bankers 0 [] 0 [] ] ++
            [ Bankers nf f 0 [] ] ++
            filter valid [ Bankers (length f') f' (length r') r'
                        | (f', r') <- shrink (f, r) ]
            where valid (Bankers nf' _ nr' _) = nf' >= nr'
    -}

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
-- prop_bankersAmortized :: (Repr a, a1 ~ Rep a, Demand a1, a2 ~ Dem a1) => Bankers a -> Op a -> Int -> Bool
-- prop_bankersAmortized q op k =
--     -- exactlyWith'
--     -- (exactlyWith' :: MemoristM (Maybe (BankersT (Rep a))) -> (Maybe (BankersT (Rep a)) -> Maybe (ThD (ListD (Dem (Rep a))), ThD (ListD (Dem (Rep a))))) -> (SMaybe (Bankers a) -> Maybe (ThD (ListD (Dem (Rep a))), ThD (ListD (Dem (Rep a)))) -> Int) -> Bool)
--     (exactlyWith' :: MemoristM (Maybe (BankersT a1)) -> (Maybe (BankersT a1) -> Maybe (ThD (ListD a2), ThD (ListD a2))) -> (SMaybe (Bankers a) -> Maybe (ThD (ListD a2), ThD (ListD a2)) -> Int) -> Bool)
--         m fullDemand $ \v _ -> k -- + delta v
--     where m = runOpFromPure q op
--
-- prop_bankersAmortized :: Bankers Int -> Op Int -> Int -> Bool
-- prop_bankersAmortized q op k =
--     -- exactlyWith'
--     (exactlyWith' :: MemoristM (Maybe (BankersT Int)) -> (Maybe (BankersT Int) -> Maybe (ThD (ListD Int), ThD (ListD Int))) -> (SMaybe (Bankers Int) -> Maybe (ThD (ListD Int), ThD (ListD Int)) -> Int) -> Bool)
--         m fullDemand $ \v _ -> k -- + delta v
--     where m = runOpFromPure q op

-- Recall:
--    amortized cost = complete cost - potential change

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
-- 
-- NOTE: One slight issue with using fullDemand: it may be slower than using QuickCheck's
-- 'forAll' combinator on all possible demand generated based on resulting value.
prop_bankersAmortized :: ReprDemand a => Bankers a -> Op a -> Int -> Property
prop_bankersAmortized q op k =
    runOpFromPure q op `upperboundWith` fullDemand $ \v _ -> k + delta v
    where delta (Just q') = potential q' - potential q
          delta _         = 0

qcN_bankersEnqAmortized :: Int -> IO ()
qcN_bankersEnqAmortized n = quickCheckN n $ \q x -> prop_bankersAmortized q (Enq x :: Op Int) 4
-- before [] [], pot = 0, then r=1, rot []++r' [] takes 1 for append + 3 for rev, pot = 1
-- cost = 1+1+3=5, delta=1, amort = 5-1=4

qcN_bankersDeqAmortized :: Int -> IO ()
qcN_bankersDeqAmortized n = quickCheckN n $ \q -> prop_bankersAmortized q (Deq :: Op Int) 4
-- before f = r, pot = 0, then f-1, rot f-1++r' [], takes f for append + r+2 for rev, pot = f-1+r
-- cost = 1+f+r+2=f+r+3, delta=f+r-1-0, amort=f+r+3-(f+r-1)=4

-- The property below is somewhat loose in that we do not fix the demand.
-- NOTE: this is generally faster than the fullDemand version
--  since the demand might sometimes be small
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

-- Fixed to full demand. NOTE: just for experiment; this does not hold in general.
-- Asking for "full demand" actually violates the queue interface where elements
-- are only accessed via dequque operation.
prop_bankersRunTraceCost1 :: ReprDemandArb a => Trace1 a -> Property
prop_bankersRunTraceCost1 t =
    runTraceFromPure (Q.empty :: Bankers a) t `upperboundWith` fullDemand $
        \_ _ -> 4 * traceSize t

qcN_bankersRunTraceCost1 :: Int -> IO ()
qcN_bankersRunTraceCost1 n = quickCheckN n (prop_bankersRunTraceCost1 :: Trace1 Int -> Property)

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

qctestop :: Bankers Int -> Op Int -> Int -> IO ()
qctestop q op k = quickCheckN 1 $ prop_bankersAmortized q op k

qctesttrace :: Trace1 Int -> IO ()
qctesttrace t = quickCheckN 1 $ prop_bankersRunTraceCost t

qctesttrace' :: Bankers Int -> Trace1 Int -> IO ()
qctesttrace' q t = quickCheckN 1 $ prop_bankersRunTraceCost' q t

qctesttrace1 :: Trace1 Int -> IO ()
qctesttrace1 t = quickCheckN 1 $ prop_bankersRunTraceCost1 t

tracecost :: Bankers Int -> Trace1 Int -> Cost
tracecost q t = infcost (runTraceFromPure q t) minDemand

{-
q1 :: Bankers Int
q1 = Bankers 14 [3,-1,-18,9,14,9,18,7,-12,8,7,14,16,11] 2 [18,17]
t1 :: RanTrace Int
t1 = RanTrace $ Node Deq [Node (Enq (-5)) [Node Deq [Node (Enq 3) [Node (Enq (-7))[Node (Enq 0) []]]]]]

q2 :: Bankers Int
q2 = Bankers 14 [-9,0,6,-9,-10,5,-1,17,10,1,-6,-6,7,-5] 14 [-11,10,2,8,-12,7,-5,0,15,8,-12,11,5,-17]
t2 :: RanTrace Int
t2 = RanTrace $ Node (Enq 5) []
-- ^ This will fails RunTraceCost if we do not fix the demand to minDemand

q3 :: Bankers Int
q3 = Bankers 1 [1] 1 [2]
t3 :: RanTrace Int
t3 = RanTrace $ Node Deq [Node Deq []]
-}
