module Memorist.Base.Thunk where

import Prelude hiding (toInteger, fromInteger)
import qualified Data.Set as Set


-- | A thunk name under this scheme is either constructed using only a number,
-- or has other other names nested in addition to a number.
-- In fact, a name is essentially just a nonempty sequence of numbers.
data ThName = ThName1 Int | ThName2 ThName Int
    deriving (Eq, Ord, Show)
-- ^ TODO: default ord is actually wrong semantically

-- TODO: implement a better structure for efficient comparison as well
-- instance Ord ThName where
--     compare (ThName1 i) (ThName1 j) = compare i j
--     compare n1@(ThName1 _) (ThName2 n2 _) =
--         case compare n1 n2 of
--             EQ -> LT    -- n1 < (n1,x)
--             ord -> ord
--     compare (ThName2 n1 _) n2@(ThName1 _) =
--         case compare n1 n2 of
--             EQ -> GT    -- (n2,x) > n2
--             ord -> ord
--     compare (ThName2 n1 i) (ThName2 n2 j) =
--         case compare n1 n2 of
--             EQ -> compare i j
--             ord -> ord

-- | The 0 name
nzero :: ThName
nzero = ThName1 0

-- | The next name at the same level
nnext :: ThName -> ThName
nnext (ThName1 i) = ThName1 (i + 1)
nnext (ThName2 ns i) = ThName2 ns (i + 1)

-- | Produce the first name at the next level
nshift :: ThName -> ThName
nshift n = ThName2 n 0

newtype Cost = Cost Integer
    deriving (Eq, Ord, Show)

cplus :: Cost -> Cost -> Cost
cplus (Cost n) (Cost m) = Cost (n + m)

onetick :: Cost
onetick = Cost 1

toInteger :: Cost -> Integer
toInteger (Cost n) = n


data NameCost = NameCost { ncname :: ThName, nccost :: Cost }
    deriving (Eq, Ord, Show)

type USet = Set.Set NameCost

empty :: USet
empty = Set.empty

union :: USet -> USet -> USet
union = Set.union

insert :: NameCost -> USet -> USet
insert = Set.insert

freshFrom :: USet -> ThName -> USet
freshFrom s n = Set.filter ((>= n) . ncname) s

-- sumcost :: USet -> Cost
-- sumcost = Set.foldr (cplus . nccost) (Cost 0)

sumcost :: USet -> Cost
sumcost = sumcost' (const True)

sumcostFresh :: ThName -> USet -> Cost
sumcostFresh firstfresh = sumcost' (>= firstfresh)

sumcost' :: (ThName -> Bool) -> USet -> Cost
sumcost' f = Set.foldr ncplus (Cost 0)
    where ncplus n c = if f (ncname n) then nccost n `cplus` c else c

--------------------------------------------------------------------------------

data Annot = Annot { acost :: Cost, ausage :: USet }
    deriving (Eq, Show)

instance Semigroup Annot where
    (<>) = add

instance Monoid Annot where
    mempty = azero

-- | The empty annotation
azero :: Annot
azero = Annot (Cost 0) empty

add :: Annot -> Annot -> Annot
add (Annot c s) (Annot c' s') = Annot (c `cplus` c') (s `union` s')

addCost :: Annot -> Cost -> Annot
addCost a c = add a $ Annot c empty

addSet :: Annot -> USet -> Annot
addSet a s = add a $ Annot (Cost 0) s

fromCost :: Cost -> Annot
fromCost = addCost azero

fromSet :: USet -> Annot
fromSet = addSet azero

--------------------------------------------------------------------------------

data Th a = Th ThName a Annot
    deriving (Eq, Show)

tname :: Th a -> ThName
tname (Th n _ _) = n

tval :: Th a -> a
tval (Th _ x _) = x

tannot :: Th a -> Annot
tannot (Th _ _ a) = a

useThunk :: Th a -> (a, USet)
useThunk (Th n x a) = (x, insert (NameCost n (acost a)) $ ausage a)

useThunk' :: Th a -> USet
useThunk' = snd . useThunk

-- not used yet
datasize :: (a -> Int) -> Th a -> Int
datasize f (Th _ x _) = f x
