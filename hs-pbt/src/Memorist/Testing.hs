module Memorist.Testing where

-- import Memorist.Core.Thunk as T
import Memorist.Core.Annotation as A
import Memorist.Core.Semantics
import Memorist.Data.Interface
import Data.Set as S (union)
import qualified Test.QuickCheck as QC


infcost' :: (Result a, AnnotCntx) -> USet -> AnnotCntx -> Cost
infcost' (r, acFin) u acIni =
    sumcost acFin s' + costAnnot r
    where s  = u `union` usageAnnot r
          s' = s `freshFrom` acIni

-- NOTE: in practice, the usage set 'u' is extracted from the result of running m,
-- so the function below is basically useless.
--
-- infcost :: M a -> USet -> AnnotCntx -> Cost
-- infcost m u acIni = infcost' (run m acIni) u acIni

-- Takes the relevant annot cntx, the value, and a measure of size of the demand on the value
type ExtractFunc a = AnnotCntx -> a -> Int -> USet

-- Takes a monad, an extraction function, the size of the demand, and the initial annot cntx
infcost :: M a -> ExtractFunc a -> Int -> AnnotCntx -> Cost
infcost m f dsize acIni = infcost' final u acIni
    where final@(r, acFin) = run m acIni
          u = f acFin (value r) dsize
