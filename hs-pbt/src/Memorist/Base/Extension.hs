module Memorist.Base.Extension where

import Memorist.Base.Thunk
import Memorist.Base.Core

{-
    (.) :: (b -> c) -> (a -> b) -> a -> c
    (.) f g = \x -> f (g x)
-}
-- No ticks for simplicity. Function composition is often inlined anyway.
composeM :: Memorist s m => (Th b -> m c) -> (Th a -> m b) -> m (Th a -> m c)
-- composeM f g = return $ \tx -> do
--     tz <- lazy $ g tx
--     f tz
composeM f g = return $ \tx -> lazy (g tx) >>= f

-- A variant that works on thunked functions.
composeTM :: Memorist s m => Th (Th b -> m c) -> Th (Th a -> m b) -> m (Th a -> m c)
composeTM tf tg = return $ \tx -> do
    g <- force tg
    tz <- lazy $ g tx
    f <- force tf
    f tz


curryKM :: Memorist s m => (Th a -> Th b -> m c) -> Th a -> m (Th b -> m c)
curryKM f = return . f

uncurryKM :: Memorist s m => (Th a -> m (Th b -> m c)) -> Th a -> Th b -> m c
uncurryKM f = \tx ty -> f tx >>= \g -> g ty
