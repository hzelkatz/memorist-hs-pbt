{-
This version imposes injectivity on associated types of Repr, so that
we can go from 'Rep a' type back to 'a' directly.

The intention is to give a generic way to define functions like 'compareVal'
(see below) which essentially lift functions on the source types to their
Memorist representation types (with the return type unchanged---i.e., this is
different from translating a source function of interest to a Memorist version).

However, the issue: once injectivity is imposed, we cannot define the 'Rep'
type instance for types such as pairs and lists, without also allowing
the 'UndecidableInstances' extension.
-}

{-# LANGUAGE TypeFamilies, TypeFamilyDependencies, UndecidableInstances #-}

module Memorist.Data.Interface.Data1 where

import Memorist.Base.Thunk
import Memorist.Base.Core

-- | 'Repr a' describes the translation of a datatype into its Memorist representation.
-- We define such representation type via Haskell's associated types.
--
-- In addition, we require the associated types to be injective, so that it
-- can typecheck in places where Memorist transformations and computations are
-- done internally and not visible from the type signature of a function.
class Repr a where
    type Rep a = r | r -> a
    reprM :: Memorist s m => a -> m (Rep a)
    abstract :: Rep a -> a

instance Repr () where
    type Rep () = ()
    reprM = return
    abstract = id

instance Repr Bool where
    type Rep Bool = Bool
    reprM = return
    abstract = id

instance Repr Int where
    type Rep Int = Int
    reprM = return
    abstract = id

-- Note: for types like pairs, Rep definitions like this would not work
-- if UndecidableInstances were not enabled.
instance (Repr a, Repr b) => Repr (a,b) where
    type Rep (a,b) = (Rep a, Rep b)
    reprM (x,y) = do { x' <- reprM x ; y' <- reprM y ; return (x',y') }
    abstract (x,y) = (abstract x, abstract y)

-- =============================================================================

fromPure1 :: (Memorist s m, Repr a) => (Th (Rep a) -> m b) -> a -> m b
fromPure1 fM x = do
    tx <- lazy $ reprM x
    fM tx

fromPure2 :: (Memorist s m, Repr a, Repr b) =>
    (Th (Rep a) -> Th (Rep b) -> m c) -> a -> b -> m c
fromPure2 fM x y = do
    tx <- lazy $ reprM x
    ty <- lazy $ reprM y
    fM tx ty

-- =============================================================================

-- Lift a function f that applies to values of type a and b
-- to apply to the Memorist representation types Rep a and Rep b.
applyAbs :: (Repr a, Repr b) => (a -> b -> c) -> Rep a -> Rep b -> c
applyAbs f x y = f (abstract x) (abstract y)

-- Lift the compare function of a type of 'Ord' to its representation type.
--
-- We define this function (instead of declaring an Ord instance directly)
-- because a representation type might have thunks embedded,
-- and it is not always clear how we should compare two thunks.
-- In many practical cases, we are only interested in comparing the actual values,
-- which is what this 'compareVal' expresses.
-- But what if we want to also compare the thunk names?
--
-- A potential place of application is in Memorist.Example.ListSort.
-- For instance, the 'insertionSortM' takes a comparison function that
-- works on the Memorist representation type. E.g.:
--
--     prop_insertM_ub x xs = fromPure2 (insertM compareVal) x xs `upperboundby` \d -> sizeD 1 d
--
-- Note: this typechecks only if the injectivity of 'Rep a' is imposed.
-- Otherwise the type of 'abstract x' may not always convert back to 'a'.
compareVal :: (Repr a, Ord a) => Rep a -> Rep a -> Ordering
compareVal = applyAbs compare
