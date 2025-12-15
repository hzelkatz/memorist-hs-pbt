module Memorist.CoreF.Annotation where

import Memorist.CoreF.Thunk
import Data.Maybe (fromMaybe)
import Data.Set as S (Set, empty, union, insert, foldr)

type USet = Set ThName
type Cost = Integer
type Annot = (Cost, USet)


-- | The empty annotation
zero :: Annot
zero = (0, S.empty)

add :: Annot -> Annot -> Annot
add (c,s) (c',s') = (c + c', s `union` s')

addCost :: Annot -> Cost -> Annot
addCost a c = add a (c, S.empty)

addSet :: Annot -> USet -> Annot
addSet a s = add a (0, s)

fromCost :: Cost -> Annot
fromCost = addCost zero

fromSet :: USet -> Annot
fromSet = addSet zero


type AnnotMap = ThName -> Maybe Annot

-- Initially map everything to Nothing
emptyMap :: AnnotMap
emptyMap = \_ -> Nothing

update :: AnnotMap -> ThName -> Annot -> AnnotMap
update am i a = update' am i $ Just a

update' :: AnnotMap -> ThName -> Maybe Annot -> AnnotMap
update' am i a = \j -> if j == i then a else am j

{-
-- shiftUps_ am n : shift every mapping in am by n, so that
-- a mapping i ↦ a in am becomes (i + n) ↦ a.
-- Intended as a helper for extending an annotation context with another
-- (i.e. 'glueing' them together), not to be otherwise used directly.
--
-- Assumption: n is nonnegative.
--
-- The mappings for names from the initial name to n-1 after shifting up
-- are essentially treated as unspecified.
shiftUps_ :: AnnotMap -> ThName -> AnnotMap
shiftUps_ am n = \i -> am $ i `shiftDown` n

-- -- Similar to shiftUps_ but downwards, so that
-- -- a mapping i ↦ a in am becomes (i - n) ↦ a.
shiftDowns_ :: AnnotMap -> ThName -> AnnotMap
shiftDowns_ am n = \i -> am $ i `shiftUp` n
-}

mapmC :: AnnotMap -> ThName -> Maybe Cost
mapmC am i = fst <$> am i

mapmS :: AnnotMap -> ThName -> Maybe USet
mapmS am i = snd <$> am i

mapmSu :: AnnotMap -> ThName -> Maybe USet
mapmSu am i = insert i <$> mapmS am i

-- sumcostm :: AnnotMap -> USet -> Maybe Cost
-- sumcostm am = S.foldr (\i -> liftA2 (+) (mapmC am i)) (Just 0)

-- Variants with default

mapd :: AnnotMap -> ThName -> Annot
mapd am = (fromMaybe zero) . am

mapdC :: AnnotMap -> ThName -> Cost
mapdC am = fromMaybe 0 . mapmC am

mapdS :: AnnotMap -> ThName -> USet
mapdS am = fromMaybe S.empty . mapmS am

mapdSu :: AnnotMap -> ThName -> USet
mapdSu am = fromMaybe S.empty . mapmSu am

sumcostd :: AnnotMap -> USet -> Cost
sumcostd am = S.foldr ((+) . (mapdC am)) 0
