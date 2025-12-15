module Memorist.CoreF.Semantics where

import Data.Set as S (filter)
import Control.Monad
import Memorist.CoreF.Thunk as T
import Memorist.CoreF.Annotation as A


data AnnotCntx = AnnotCntx {annotMap :: AnnotMap, lastName :: ThName}

instance Semigroup AnnotCntx where
    (<>) = exts

instance Monoid AnnotCntx where
    mempty = emptyCntx

-- Initially map everything to the zero annotation
emptyCntx :: AnnotCntx
emptyCntx = AnnotCntx A.emptyMap nzero

ext :: AnnotCntx -> Annot -> AnnotCntx
ext ac a = ext' ac $ Just a

ext' :: AnnotCntx -> Maybe Annot -> AnnotCntx
ext' ac a = let i = lastName ac in AnnotCntx (A.update' (annotMap ac) i a) (nnext i)

-- NOTE: This is here so we can declare AnnotCntx as Monoid.
-- But we might not actually want to use this in practice,
-- since we'd have to rename everything in values as well.
exts :: AnnotCntx -> AnnotCntx -> AnnotCntx
exts ac ac' = f (nnext nzero) ac
    where f i ac0 = if i > (lastName ac') then ac0 else f (nnext i) $ ext' ac0 ((annotMap ac) i)

freshFrom :: USet -> AnnotCntx -> USet
freshFrom s ac = S.filter (> lastName ac) s

-- Shortcut for accessing the mapping

map :: AnnotCntx -> ThName -> Annot
map ac = A.mapd (annotMap ac)

mapC :: AnnotCntx -> ThName -> Cost
mapC ac = A.mapdC (annotMap ac)

mapS :: AnnotCntx -> ThName -> USet
mapS ac = A.mapdS (annotMap ac)

mapSu :: AnnotCntx -> ThName -> USet
mapSu ac = A.mapdSu (annotMap ac)

sumcost :: AnnotCntx -> USet -> Cost
sumcost ac = A.sumcostd (annotMap ac)


data Result a = Result { value :: a, annot :: Annot }
    deriving (Eq, Show)

costAnnot :: Result a -> Cost
costAnnot = fst . annot

usageAnnot :: Result a -> USet
usageAnnot = snd . annot


newtype M a = M (AnnotCntx -> (Result a, AnnotCntx))

ret :: a -> M a
ret x = M $ \ac -> (Result x A.zero, ac)

bind :: M a -> (a -> M b) -> M b
bind (M f) k = M $ \ac ->
    let (Result x a, ac') = f ac
        M f' = k x
        (r, ac'') = f' ac'
    in (r {annot = a `A.add` annot r}, ac'')

instance Functor M where
  fmap = liftM

instance Applicative M where
  pure = ret
  (<*>) = ap

instance Monad M where
  return = pure
  (>>=) = bind


-- More combinators

lazy :: M a -> M (Th a)
lazy (M f) = M $ \ac ->
    let (Result x a, ac') = f ac
        ac'' = ext ac' a
    in (Result (Th (lastName ac'') x) A.zero, ac'')

lazybind :: M a -> (Th a -> M b) -> M b
lazybind m = (lazy m >>=)

collect :: ThName -> M ()
collect i = M $ \ac -> (Result () (A.fromSet (mapSu ac i)), ac)

forcing :: Th a -> (a -> M b) -> M b
forcing t f = do
    collect $ tname t
    f $ tval t

force :: Th a -> M a
force t = forcing t ret

tick :: M ()
tick = M $ \ac -> (Result () (A.fromCost 1), ac)


-- Running the computation
run :: M a -> AnnotCntx -> (Result a, AnnotCntx)
run (M f) = f

eval :: M a -> AnnotCntx -> Result a
eval m = fst <$> run m

evalValue :: M a -> AnnotCntx -> a
evalValue m = value <$> eval m
