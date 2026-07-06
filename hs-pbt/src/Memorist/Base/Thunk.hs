module Memorist.Base.Thunk where

import Prelude hiding (toInteger, fromInteger)
import Data.List.NonEmpty (NonEmpty(..), (<|))
import qualified Data.Set as Set


-- TODO: this version has performance issue in terms of name comparison.
-- Use Data.Sequence.Seq instead?

-- | A thunk name is essentially just a nonempty sequence of numbers.
data ThName = ThName (NonEmpty Int)
    deriving (Eq, Ord, Show)

-- | The 0 name
nzero :: ThName
nzero = ThName (0 :| [])

-- | The next name at the same level
nnext :: ThName -> ThName
nnext (ThName (n :| ns)) = ThName $ (n + 1) :| ns

-- | Produce the first name at the next level
nshift :: ThName -> ThName
nshift (ThName n) = ThName (0 <| n)

fromInt :: Int -> ThName
fromInt i = ThName (i :| [])

newtype Cost = Cost Integer
    deriving (Eq, Ord, Show)

cplus :: Cost -> Cost -> Cost
cplus (Cost n) (Cost m) = Cost (n + m)

onetick :: Cost
onetick = Cost 1

toInteger :: Cost -> Integer
toInteger (Cost n) = n

showInteger :: Cost -> String
showInteger = show . toInteger

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
