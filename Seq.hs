{-# LANGUAGE MultiParamTypeClasses #-}

module Seq where

import Data.Monoid
import FingerTree

import Prelude hiding ( length, splitAt )

newtype Size = Sz {getSize :: Int}
             deriving (Eq, Ord, Show)
newtype Elem a = Elem {getElem :: a}
               deriving Show

instance Monoid Size where
  mempty = Sz 0
  mappend (Sz a) (Sz b) = Sz (a + b)

instance Measured (Elem a) Size where
  measure (_) = Sz 1

newtype Seq a = Seq (FingerTree Size (Elem a))
              deriving Show

instance Measured (Seq a) Size where
  measure (Seq t) = measure t

length :: Seq a -> Int
length = getSize . measure

splitAt :: Int -> Seq a -> (Seq a, Seq a)
splitAt n (Seq t) = (Seq l, Seq r)
  where (l, r) = split (>= Sz n) t

(!) :: Seq a -> Int -> a
Seq t ! n = getElem x
  where Split _ x _ = splitTree (>= Sz n) mempty t

fromList :: [a] -> Seq a
fromList = Seq . FingerTree.fromList . map Elem
