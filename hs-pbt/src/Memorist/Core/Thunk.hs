module Memorist.Core.Thunk where

-- | Named thunk
type ThName = Int

data Th a = Th {tname :: ThName, tval :: a}
    deriving (Eq, Show)
