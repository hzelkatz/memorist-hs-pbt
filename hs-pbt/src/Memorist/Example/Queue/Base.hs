{-# LANGUAGE TypeFamilies #-}
-- {-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}

{-# OPTIONS_GHC -Wno-orphans #-}

module Memorist.Example.Queue.Base where

import Memorist.Memorist as M

import Data.List.NonEmpty ( NonEmpty(..) )
import Data.Tree
import Control.Monad (liftM)
import Test.QuickCheck as QC 

-- | Interface of pure queues
--
-- A queue has an enqueue and an dequeue operation. The enqueue operation adds
-- an element and the dequeue operation removes an element, in FIFO order.
-- Successful dequeue returns a pair consisting of the removed element and
-- the remaining queue wrapped in 'Just', while dequeuing the empty queue
-- should return 'Nothing'.
-- Given that it does not impact the analysis in any substantial way whether
-- the returned Maybe values and pairs are lazy or not, for simplicity we just
-- treat them as strict. We use the wrapper types SMaybe and SPair to represent this.
class Queue t where
    empty :: t a
    enqueue :: t a -> a -> t a
    -- dequeue :: t a -> Maybe (a, t a)
    dequeue :: t a -> SMaybe (SPair a (t a))

-- | Interface of Memorist representations of queues
class QueueT t where
    emptyM :: MemoristM (t a)
    enqueueM :: Th (t a) -> Th a -> MemoristM (t a)
    dequeueM :: Th (t a) -> MemoristM (Maybe (a, t a))

-- -----------------------------------------------------------------------------

class HasPotential t where
    potential :: t a -> Int

data Op a = Enq a | Deq deriving (Eq,Show)

liftOp :: Repr a => Op a -> MemoristM (Op (Rep a))
liftOp (Enq x) = liftM Enq $ reprM x
liftOp Deq     = return Deq

liftTree :: Repr a => Tree (Op a) -> MemoristM (Tree (Op (Rep a)))
liftTree (Node op t) = Node <$> liftOp op <*> mapM liftTree t

instance Arbitrary a => Arbitrary (Op a) where
    arbitrary = frequency [ (3, Enq <$> arbitrary), (1, return Deq) ]

class Trace t where
    toTree :: t a -> Tree (Op a)
    fromTree :: Tree (Op a) -> t a

    traceSize :: t a -> Int
    traceSize = treesize . toTree

    liftTrace :: Repr a => t a -> MemoristM (t (Rep a))
    liftTrace = liftM fromTree . liftTree . toTree

    runTrace :: QueueT t1 => Th (t1 a) -> t a -> MemoristM [t1 a]
    runTrace tq = runTree tq . toTree

-- We are interested in running a series of operations on queues, and not on
-- the particular elements inside. To simplify a bit, we make runTrace and runOp
-- to return only the queue but not the head element when dequeueing.

runOp :: QueueT t => Th (t a) -> Op a -> MemoristM (Maybe (t a))
runOp tq (Enq x) = Just <$> (enqueueM tq =<< lazy (return x))
runOp tq Deq = liftM snd <$> dequeueM tq

runTree :: QueueT t => Th (t a) -> Tree (Op a) -> MemoristM [t a]
runTree tq (Node op ts) = do
    mq <- runOp tq op
    case mq of
        Just q -> do
            tq' <- lazy $ return q
            (q:) <$> runBranch tq' ts
        _ -> return []

-- Branches ending up with Nothing are removed
runBranch :: QueueT t => Th (t a) -> [Tree (Op a)] -> MemoristM [t a]
runBranch tq = liftM concat . mapM (runTree tq)

runTraceFromPure :: (Trace t, Queue t0, QueueT t1, Repr a, Repr (t0 a), Rep (t0 a) ~ t1 (Rep a)) =>
    t0 a -> t a -> MemoristM [t1 (Rep a)]
runTraceFromPure q t = do
    t' <- liftTrace t
    fromPure1 (flip runTrace t') q

runOpFromPure :: (Queue t, QueueT t1, Repr a, Repr (t a), Rep (t a) ~ t1 (Rep a)) =>
    t a -> Op a -> MemoristM (Maybe (t1 (Rep a)))
runOpFromPure q op = do
    op' <- liftOp op
    fromPure1 (flip runOp op') q


-- A sequence is just a special case of a trace that has only 1 branch.
newtype SeqTrace a = SeqTrace (NonEmpty (Op a)) deriving (Show,Eq)

newtype RanTrace a = RanTrace (Tree (Op a)) deriving (Show,Eq)

-- linear-then-split
newtype LSTrace a = LSTrace (Tree (Op a)) deriving (Show,Eq)

type Trace1 = LSTrace

instance Trace SeqTrace where
  toTree (SeqTrace l) = fromNonEmpty l
  -- Warning: fromTree to SeqTrace will flatten any forest into a single list.
  -- It is intended to be used on trees of operations that is "linear"
  -- (i.e. that has at most one child at each node).
  fromTree (Node x ts) = SeqTrace $ x :| concatMap flattenToList ts
  traceSize (SeqTrace (_ :| xs)) = 1 + length xs

instance Trace RanTrace where
    toTree (RanTrace t) = t
    fromTree = RanTrace

instance Trace LSTrace where
    toTree (LSTrace t) = t
    fromTree = LSTrace

fromNonEmpty :: NonEmpty (Op a) -> Tree (Op a)
fromNonEmpty (op :| ops) = Node op $ foldr f [] ops
    where f op1 tt = [Node op1 tt]

flattenToList :: Tree (Op a) -> [Op a]
flattenToList (Node x ts) = x : concatMap flattenToList ts

instance Arbitrary a => Arbitrary (SeqTrace a) where
    arbitrary = SeqTrace <$> arbNonEmpty arbitrary

instance Arbitrary a => Arbitrary (RanTrace a) where
    arbitrary = RanTrace <$> arbitrary

instance Arbitrary a => Arbitrary (LSTrace a) where
    arbitrary = LSTrace <$> sized arbTreeLS

arbNonEmpty :: Gen a -> Gen (NonEmpty a)
arbNonEmpty gen = (:|) <$> gen <*> listOf gen

arbTreePath :: Arbitrary a => Int -> Tree a -> Gen (Tree a)
arbTreePath n t | n <= 0 = return t
arbTreePath n t          = Node <$> arbitrary <*> ((:[]) <$> arbTreePath (n-1) t)

arbTreeLS :: Arbitrary a => Int -> Gen (Tree (Op a))
arbTreeLS n = do
    m <- chooseInt (0, n)   -- # of nodes since branching
    k <- chooseInt (0, m)   -- # of branches; still possible to not branch though
    ts <- mapM (\_ -> arbTreeLS (m `div` k)) [1..k]  -- build subtree for each branch
    arbTreePath (n - m) =<< Node <$> arbitrary <*> return ts

treesize :: Tree a -> Int
treesize (Node _ trees) = 1 + sum (map treesize trees)
