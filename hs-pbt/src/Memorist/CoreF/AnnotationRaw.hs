module Memorist.CoreF.AnnotationRaw where

import Data.Set as S (Set, empty, union, insert, fromList, foldr, filter)
import Memorist.CoreF.Thunk

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

-- TODO: it might be better to impl it as a monad?

-- Alternative implementation as a function instead of a list
type AnnotCntx = ThName -> Annot

-- Initially map everything to the zero annotation
empty :: AnnotCntx
empty = \_ -> zero

-- Takes the last assigned name
newName :: ThName -> ThName
newName = (+1)

ext :: AnnotCntx -> ThName -> Annot -> AnnotCntx
ext ac i a = \j -> if j == i then a else ac j

mapC :: AnnotCntx -> ThName -> Cost
mapC ac i = fst $ ac i

mapS :: AnnotCntx -> ThName -> USet
mapS ac i = snd $ ac i

mapSu :: AnnotCntx -> ThName -> USet
mapSu ac i = insert i $ mapS ac i


-- We no longer have access to the domain directly from AnnotCntx.
-- These will be handled by the monad instead.
-- dom :: AnnotCntx -> USet
-- freshFrom :: USet -> AnnotCntx -> USet

sumcost :: AnnotCntx -> USet -> Cost
sumcost ac = S.foldr (\i -> (mapC ac i +)) 0


{-
-- Strictly speaking, should map names to `Maybe Annot`.

type AnnotCntx = ThName -> Maybe Annot

-- Initially map everything to Nothing
empty :: AnnotCntx
empty = \_ -> Nothing

ext :: AnnotCntx -> ThName -> Annot -> AnnotCntx
ext ac i a = \j -> if j == i then Just a else ac j

mapC :: AnnotCntx -> ThName -> Maybe Cost
mapC ac i = fst <$> ac i

mapS :: AnnotCntx -> ThName -> Maybe USet
mapS ac i = snd <$> ac i

mapSu :: AnnotCntx -> ThName -> Maybe USet
mapSu ac i = insert i <$> mapS ac i

sumcost :: AnnotCntx -> USet -> Maybe Cost
sumcost ac = S.foldr (\i -> liftA2 (+) (mapC ac i)) (Just 0)
-}
