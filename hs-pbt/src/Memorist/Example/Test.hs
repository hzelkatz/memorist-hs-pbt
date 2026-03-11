module Memorist.Example.Test where

import Memorist.Memorist as M
import qualified Test.QuickCheck as QC

tick1 :: MemoristM ()
tick1 = tick

tick2 :: MemoristM ()
tick2 = tick >> tick

lazy1 :: MemoristM (Th ())
lazy1 = lazy $ tick

force1 :: MemoristM ()
force1 = tick >> lazy1 >>= force
