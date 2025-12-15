module Memorist.Core.Semantics where

-- import Data.Set as S (union)
import Control.Monad
import Memorist.Core.Thunk as T
import Memorist.Core.Annotation as A


data Result a = Result { value :: a, annot :: Annot }
    deriving (Eq, Show)

costAnnot :: Result a -> Cost
costAnnot = fst . annot

usageAnnot :: Result a -> USet
usageAnnot = snd . annot


newtype M a = M (AnnotCntx -> (Result a, AnnotCntx))

ret :: a -> M a
ret x = M $ \ac -> (Result x zero, ac)

bind :: M a -> (a -> M b) -> M b
bind (M f) k = M $ \ac ->
    let (Result x a, ac') = f ac
        M f' = k x
        (r, ac'') = f' ac'
    in (r {annot = a `add` annot r}, ac'')

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
    in (Result (Th (nextIdx ac') x) A.zero, ext ac' a)

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
