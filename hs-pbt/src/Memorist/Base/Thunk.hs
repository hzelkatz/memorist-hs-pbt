module Memorist.Base.Thunk where

import Prelude hiding (toInteger, fromInteger)
import qualified Data.Set as Set


-- ThNameNil essentially serves as a special marker indicating an yet unavailable level.
-- We don't treat ThNameNil alone as a valid name.
data ThName = ThNameNil | ThName ThName Int 
    deriving (Eq, Ord, Show)

nzero :: ThName
nzero = ThName ThNameNil 0

nnext :: ThName -> ThName
nnext (ThName ns i) = ThName ns (i + 1)
nnext ThNameNil = ThNameNil

nshift :: ThName -> ThName
nshift ThNameNil = nzero
nshift n         = ThName n 0

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

sumcost :: USet -> Cost
sumcost = Set.foldr (cplus . nccost) (Cost 0)

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

data Th a = Th ThName a (Annot)
    deriving (Eq, Show)

useThunk :: Th a -> (a, USet)
useThunk (Th n x a) = (x, insert (NameCost n (acost a)) $ ausage a)

useThunk' :: Th a -> USet
useThunk' = snd . useThunk
