-- Internal helper module
module Memorist.Example.Util where

import qualified Test.QuickCheck as QC

quickCheckN :: QC.Testable prop => Int -> prop -> IO ()
quickCheckN n = QC.quickCheckWith QC.stdArgs { QC.maxSuccess = n }
