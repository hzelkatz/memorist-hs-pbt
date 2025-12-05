{-# LANGUAGE TypeFamilies #-}
-- {-# LANGUAGE FlexibleInstances #-}
-- {-# LANGUAGE UndecidableInstances #-}

module Memorist.DataT.Data where

import Memorist.Core.Thunk
import Memorist.Core.Semantics

class Repr a where
    type Rep a
    reprM :: a -> M (Rep a)
    abstract :: Rep a -> a

{-
-- This doesn't work well.

class SimpleRepr a

instance SimpleRepr a => Repr a where
    type Rep a = a
    reprM = ret
    abstract = id

instance SimpleRepr ()
instance SimpleRepr Bool
instance SimpleRepr Int
-}

-- So define each instance separately

instance Repr () where
    type Rep () = ()
    reprM = ret
    abstract = id

instance Repr Bool where
    type Rep Bool = Bool
    reprM = ret
    abstract = id

instance Repr Int where
    type Rep Int = Int
    reprM = ret
    abstract = id
