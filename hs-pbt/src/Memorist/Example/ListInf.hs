-- {-# LANGUAGE RecursiveDo #-}

{-# OPTIONS_GHC -Wno-x-partial #-}
-- {-# OPTIONS_GHC -Wno-type-defaults #-}

module Memorist.Example.ListInf where

import Memorist.Memorist as M
import Memorist.Data.List
import Memorist.Example.Util
import Memorist.Example.List (takeM)
-- import Test.QuickCheck as QC ( NonNegative (..), (==>) )


-- Simple infinite list examples
-- 
-- translatable, likely works fine, not finished yet.


{-
scanl                   :: (b -> a -> b) -> b -> [a] -> [b]
scanl                   = scanlGo
  where
    scanlGo           :: (b -> a -> b) -> b -> [a] -> [b]
    scanlGo f q ls    = q : (case ls of
                               []   -> []
                               x:xs -> scanlGo f (f q x) xs)
-}
scanlM :: Th (Th b -> Th a -> MemoristM b) -> Th b -> Th (ListT a) -> MemoristM (ListT b)
scanlM tf tq tl = do
    tick
    tzs <- lazy $ do
        l <- force tl
        case l of
            NilT -> return NilT
            ConsT tx txs -> do
                tq' <- lazy $ do
                    f <- force tf
                    f tq tx
                scanlM tf tq' txs
    return $ ConsT tq tzs


-- triangulars = scanl (+) 1 [2..]

-- sumsM txs = do
--     ta <- lazy $ return addM
--     t1 <- lazy $ return 1
--     scanlM ta t1 txs

-- factorials = scanl (*) 1 [1..]

prodsM :: Th (ListT Integer) -> MemoristM (ListT Integer)
prodsM txs = do
    ta <- lazy $ return multM
    t1 <- lazy $ return 1
    scanlM ta t1 txs

prc :: [Integer] -> Cost
prc xs = infcost (fromPure1 prodsM xs) fullDemand

factorialsM :: MemoristM (ListT Integer)
-- factorialsM = prodsM =<< lazy (reprM ([1..] :: [Integer]))
factorialsM = tick >> (prodsM =<< lazy . enumFromM =<< lazy (return 1))

factsM :: Th Int -> MemoristM (ListT Integer)
factsM tn = takeM tn =<< lazy factorialsM

-- NOTE: seems ok
factc :: Int -> Cost
factc n = infcost (fromPure1 factsM n) fullDemand


enumFromM :: Num a => Th a -> MemoristM (ListT a)
enumFromM tn = do
    tick
    tn1 <- lazy $ do
        n <- force tn
        return $ n + 1
    tns <- lazy $ enumFromM tn1
    return $ ConsT tn tns

-- addM :: Num n => Th n -> Th n -> MemoristM n
-- addM tx ty = do
--     tick
--     x <- force tx
--     y <- force ty
--     return $ x + y

multM :: Num n => Th n -> Th n -> MemoristM n
multM tx ty = do
    tick
    x <- force tx
    y <- force ty
    return $ x * y
