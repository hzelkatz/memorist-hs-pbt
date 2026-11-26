-- The Newton Raphson algorithm, originally presented in Hughes (1990):
-- https://www.cs.kent.ac.uk/people/staff/dat/miranda/whyfp90.pdf

{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

module Memorist.Example.NewtonRaphson where

import Memorist.Memorist as M
import Memorist.Data.List
import Memorist.Example.Util
import Test.QuickCheck (Positive (getPositive), chooseInt, forAll, noShrinking)


-- The original algorithm

next :: Fractional a => a -> a -> a
next n x = (x + n/x)/2

repeatly :: (t -> t) -> t -> [t]
repeatly f a = a : repeatly f (f a)

within :: (Ord a, Num a) => a -> [a] -> a
within eps (a : (b : rest)) =
    if abs (a - b) <= eps then b
    else within eps (b : rest)

sqrtNR :: (Ord a, Fractional a) => a -> a -> a -> a
sqrtNR a0 eps n = within eps (repeatly (next n) a0)

sqrtNR' :: (Ord a, Floating a) => a -> a -> a
sqrtNR' eps n = sqrtNR (2**(logBase 2 n / 2)) eps n

-- ------------------------------------------------

-- Translated:

-- One typical cost model is the number of iterations.
-- Hence we count in this function modelling the iterations, and only here.
-- NOTE: counting here versus counting number of invocations of repeatly
-- will give slightly different result (a constant difference of 2?).
nextM :: Double -> Double -> MemoristM Double
nextM n x = do
    tick    -- count # of iterations, or rather,
            -- # of times this action being iterated actually gets executed
    z1 <- return $ n / x
    z2 <- return $ x + z1
    return $ z2 / 2

-- nextM tn tx = do
--     n <- force tn
--     x <- force tx
--     z1 <- return $ n / x
--     z2 <- return $ x + z1
--     return $ z2 / 2

repeatlyM :: (Th a -> MemoristM a) -> Th a -> MemoristM (ListT a)
repeatlyM fM ta = do
    ta1 <- lazy $ fM ta
    tl <- lazy $ repeatlyM fM ta1
    return $ ConsT ta tl


withinM :: (Ord b, Num b) => Th b -> Th (ListT b) -> MemoristM b
withinM teps tas = do
    as <- force tas
    case as of
        ConsT ta tas' -> do
            as' <- force tas'
            case as' of
                ConsT tb _ -> do
                    a <- force ta
                    b <- force tb
                    eps <- force teps
                    cond <- return $ abs (a - b) <= eps
                    if cond then return b
                    else withinM teps tas'

sqrtNRM :: Th Double -> Th Double -> Th Double -> MemoristM Double
sqrtNRM ta0 teps tn = do
    n <- force tn
    fn <- return $ \tx -> nextM n =<< force tx
    withinM teps =<< lazy (repeatlyM fn ta0)

-- qcN_sqrtNRMCorrect :: Int -> IO ()
-- qcN_sqrtNRMCorrect n = quickCheckN n $ \(m::Positive Integer) ->
--     forAll (chooseInt (1,50)) $ \k ->
--     let x = fromInteger $ getPositive m :: Double in
--     let e = 10 ** fromIntegral (-k) :: Double in
--     let a0 = initial1 x :: Double in
--     fromPure3 sqrtNRM a0 e x `correct` sqrtNR a0 e x

-- It is easy to translate, specify bounds and test it.
-- The real issue is to find the specification itself.
-- Ideally, this algorithm runs in O(log n) where n is the digit precision,
-- when we count number of iterations, *provided that* we have a good initial estimation.
-- But what is a good initial estimation?

-- For a number x, $x / 2$ is a practical candidate, though it seems not so optimal.
-- Testing provides various counterexamples, but the cost gaps are generally
-- resaonbly small.
qcN_sqrtNRM1 :: Int -> IO ()
qcN_sqrtNRM1 n = quickCheckN n $ noShrinking $ \(m::Positive Integer) ->
    forAll (chooseInt (1,30)) $ \k ->
    let x = fromInteger $ getPositive m :: Double in
    let e = 10 ** fromIntegral (-k) :: Double in
    let a0 = initial1 x :: Double in
    fromPure3 sqrtNRM a0 e x `upperboundby` \_ _ -> max 1 $ log (fromIntegral k) :: Double

-- The following initial estimation (see 'initial2'), for instance,
-- makes the algorithm converge very fast, passing all of the tests we have run.
-- In principle there should be cases still requiring more iterations, but it seems rare.
qcN_sqrtNRM2 :: Int -> IO ()
qcN_sqrtNRM2 n = quickCheckN n $ noShrinking $ \(m::Positive Integer) ->
    forAll (chooseInt (1,30)) $ \k ->
    let x = fromInteger $ getPositive m :: Double in
    let e = 10 ** fromIntegral (-k) :: Double in
    let a0 = initial2 x :: Double in
    fromPure3 sqrtNRM a0 e x `upperboundby` \_ _ -> max 1 $ log (fromIntegral k) :: Double

initial1 :: Fractional a => a -> a
initial1 x = x / 2

initial2 :: Floating a => a -> a
initial2 x = 2**(logBase 2 x / 2)


-- TODO: another version

relative :: (Ord a, Fractional a) => a -> [a] -> a
relative eps (a : (b : rest)) =
    if abs (a/b - 1) <= eps then b
    else relative eps (b : rest)

relativesqrtNR :: (Ord a, Fractional a) => a -> a -> a -> a
relativesqrtNR a0 eps n = relative eps (repeatly (next n) a0)

