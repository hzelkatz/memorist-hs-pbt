{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Memorist.DataT.Data where

import Memorist.Components.Thunk
import Memorist.Core


class Rep a b where
    repM :: a -> M b
    abst :: b -> a

instance Rep a b => Rep a (Th b) where
    repM = lazy . repM
    abst = abst . tval

class BaseType a

instance BaseType a => Rep a a where
    repM = ret
    abst = id

instance BaseType ()
instance BaseType Bool
instance BaseType Int


-- FIXME: Rep a, and without instance for Th
