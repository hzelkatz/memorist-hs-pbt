module Memorist.Components.Thunk where

-- | Named thunk
-- Int? Alternative is Numeric.Natural?
-- Since we currently implment annot cntx as lists, Int is more convenient
type ThName = Int

data Th a = Th ThName a
    deriving (Eq, Show)

tname :: Th a -> ThName
tname (Th i _) = i

tval :: Th a -> a
tval (Th _ x) = x
