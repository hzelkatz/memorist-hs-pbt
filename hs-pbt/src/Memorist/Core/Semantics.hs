module Memorist.Core.Semantics where

import Data.Set as S (union)
import Memorist.Core.Thunk as T
import Memorist.Core.Annotation as A


data Result a = Result { value :: a, annot :: Annot, cntx :: AnnotCntx }
    deriving (Eq, Show)

costAnnot :: Result a -> Cost
costAnnot = fst . annot

usageAnnot :: Result a -> USet
usageAnnot = snd . annot


-- TODO: monad class

type M a = AnnotCntx -> Result a

ret :: a -> M a
ret x = \ac -> Result {value = x, annot = zero, cntx = ac}

bind :: M a -> (a -> M b) -> M b
bind m k = \ac ->
    let Result {value = x, annot = a, cntx = ac'} = m ac in
        let Result {value = y, annot = a', cntx = ac''} = (k x) ac' in 
            Result {value = y, annot = a `add` a', cntx = ac''}

lazy :: M a -> M (Th a)
lazy m = \ac ->
    let Result {value = x, annot = a, cntx = ac'} = m ac in
        Result {value = Th (nextIdx ac') x, annot = A.zero, cntx = ext ac' a}

lazybind :: M a -> (Th a -> M b) -> M b
lazybind m = bind (lazy m)

collect :: ThName -> M ()
collect i = \ac -> Result {value = (), annot = fromSet (mapSu ac i), cntx = ac}

forcing :: Th a -> (a -> M b) -> M b
forcing t f = bind (collect (tname t)) (\_ -> f (tval t))

force :: Th a -> M a
force t = forcing t ret

tick :: M ()
tick = \ac -> Result {value = (), annot = fromCost 1, cntx = ac}



-- u: usage from value
-- This will be generalised
infcost' :: Result a -> USet -> AnnotCntx -> Cost
infcost' r u ac =
    sumcost (cntx r) s' + costAnnot r
    where s  = u `union` usageAnnot r
          s' = s `freshFrom` ac

infcost :: M a -> USet -> AnnotCntx -> Cost
infcost m u ac = infcost' (m ac) u ac


-- newtype M a = M (AnnotCntx -> Result a)


-- -- ret 
-- instance Monad M where
--     return x = 

--     m >>= k =


