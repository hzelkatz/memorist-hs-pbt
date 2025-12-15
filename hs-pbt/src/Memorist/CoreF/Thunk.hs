module Memorist.CoreF.Thunk where

-- | Named thunk
-- Int? Num(eric).Natural?
type ThName = Int

nzero :: ThName
nzero = 0

nnext :: ThName -> ThName
nnext = (+ 1)

{-
shiftUp :: ThName -> ThName -> ThName
shiftUp = (+)

shiftDown :: ThName -> ThName -> ThName
shiftDown = (-)
-}


data Th a = Th {tname :: ThName, tval :: a}
    deriving (Eq, Show)
