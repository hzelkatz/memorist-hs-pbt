module Memorist.Core.Annotation where

import Data.List as L (foldr)
import Data.Set as S (Set, empty, union, insert, fromList, foldr, filter)
import Memorist.Core.Thunk

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


-- NOTE: implemented as lists in the Rocq ver for easier proofs,
-- but otherwise it is probably better to implement it as a function?
type AnnotCntx = [Annot]

emptyCntx :: AnnotCntx
emptyCntx = []

nextIdx :: AnnotCntx -> ThName
nextIdx = length

ext :: AnnotCntx -> Annot -> AnnotCntx
ext ac a = ac ++ [a]

-- Unsafe versions: errors when index (thunk name) invalid
unsafeMap :: AnnotCntx -> ThName -> Annot
unsafeMap = (!!)

-- Version 1: using Maybe type (the '!?' operator in newer version of Haskell)
mapm :: AnnotCntx -> ThName -> Maybe Annot
mapm ac i
    | i < 0     = Nothing
    | otherwise = L.foldr (\x r k -> case k of
                                        0 -> Just x
                                        _ -> r (k - 1)) (const Nothing) ac i

mapmC :: AnnotCntx -> ThName -> Maybe Cost
mapmC ac i = fst <$> mapm ac i

mapmS :: AnnotCntx -> ThName -> Maybe USet
mapmS ac i = snd <$> mapm ac i

-- Version 2: invalid thunk name results in a default value, which is the empty annotation
mapd :: AnnotCntx -> ThName -> Annot
mapd ac i
    | i < 0     = zero
    | otherwise = L.foldr (\x r k -> case k of
                                        0 -> x
                                        _ -> r (k - 1)) (const zero) ac i

mapdC :: AnnotCntx -> ThName -> Cost
mapdC ac i = fst $ mapd ac i

mapdS :: AnnotCntx -> ThName -> USet
mapdS ac i = snd $ mapd ac i


-- So far, version 2 has been used
mapC :: AnnotCntx -> ThName -> Cost
mapC = mapdC

mapS :: AnnotCntx -> ThName -> USet
mapS = mapdS

mapSu :: AnnotCntx -> ThName -> USet
mapSu ac i = insert i $ mapS ac i


-- This was used to sanity check thunk names in proofs and to remove old names,
-- but we probably don't need it here but use the 'freshFrom' below
dom :: AnnotCntx -> USet
dom ac = S.fromList [0..length ac - 1]

freshFrom :: USet -> AnnotCntx -> USet
freshFrom s ac = S.filter (>= nextIdx ac) s

sumcost :: AnnotCntx -> USet -> Cost
sumcost ac = S.foldr (\i -> (mapC ac i +)) 0
