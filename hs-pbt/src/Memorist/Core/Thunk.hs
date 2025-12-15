module Memorist.Core.Thunk where

-- | Named thunk
-- Int? Alternative is Numeric.Natural?
-- Since we currently implment annot cntx as lists, Int is more convenient
type ThName = Int

data Th a = Th {tname :: ThName, tval :: a}
    deriving (Eq, Show)
