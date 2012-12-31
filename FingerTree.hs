{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}

module FingerTree where

import Prelude hiding ( foldr, foldl )

import Data.Foldable ( Foldable (foldr, foldl), toList )
import Data.Monoid ( Monoid (mappend, mempty), mconcat )

class Monoid v => Measured a v where
  measure :: a -> v

data Node v a = Node2 v a a
              | Node3 v a a a
              deriving Show

data Digit a = Zero
             | One a
             | Two a a
             | Three a a a
             | Four a a a a
             deriving Show

data FingerTree v a = Empty
                    | Single a
                    | Deep v (Digit a) (FingerTree v (Node v a)) (Digit a)
                    deriving Show

instance Foldable (Node v) where
  foldr (-<) z (Node2 _ a b)   = a -< (b -< z)
  foldr (-<) z (Node3 _ a b c) = a -< (b -< (c -< z))

  foldl (>-) z (Node2 _ a b)   = (z >- a) >- b
  foldl (>-) z (Node3 _ a b c) = ((z >- a) >- b) >- c

instance Foldable Digit where
  foldr (-<) z Zero           = z
  foldr (-<) z (One a)        = a -< z
  foldr (-<) z (Two a b)      = a -< (b -< z)
  foldr (-<) z (Three a b c)  = a -< (b -< (c -< z))
  foldr (-<) z (Four a b c d) = a -< (b -< (c -< (d -< z)))

  foldl (-<) z Zero           = z
  foldl (>-) z (One a)        = z >- a
  foldl (>-) z (Two a b)      = (z >- a) >- b
  foldl (>-) z (Three a b c)  = ((z >- a) >- b) >- c
  foldl (>-) z (Four a b c d) = (((z >- a) >- b) >- c) >- d

instance Foldable (FingerTree v) where
  foldr :: forall a b . (a -> b -> b) -> b -> FingerTree v a -> b
  foldr (-<) z Empty            = z
  foldr (-<) z (Single a)       = a -< z
  foldr (-<) z (Deep _ dl t dr) = dl -<< (t -<<< (dr -<< z))
    where (-<<) :: Foldable t => t a -> b -> b
          (-<<) = flip (foldr (-<))

          (-<<<) :: (Foldable t1, Foldable t2) => t1 (t2 a) -> b -> b
          (-<<<) = flip (foldr (-<<))

  foldl :: forall b a . (b -> a -> b) -> b -> FingerTree v a -> b
  foldl (>-) z Empty          = z
  foldl (>-) z (Single a)     = z >- a
  foldl (>-) z (Deep _ dl t dr) = ((z >>- dl) >>>- t) >>- dr
    where (>>-) :: Foldable t => b -> t a -> b
          (>>-) = foldl (>-)

          (>>>-) :: (Foldable t1, Foldable t2) => b -> (t1 (t2 a)) -> b
          (>>>-) = foldl (>>-)

instance Monoid v => Measured (Node v a) v where
  measure (Node2 v _ _)   = v
  measure (Node3 v _ _ _) = v

instance Measured a v => Measured (Digit a) v where
  measure = foldr (mappend . measure) mempty

instance Measured a v => Measured (FingerTree v a) v where
  measure Empty          = mempty
  measure (Single a)     = measure a
  measure (Deep v _ _ _) = v

node2 :: Measured a v => a -> a -> Node v a
node2 a b = Node2 v a b
  where v = mconcat [measure a, measure b]

node3 :: Measured a v => a -> a -> a -> Node v a
node3 a b c = Node3 v a b c
  where v = mconcat (map measure [a, b, c])

deep :: Measured a v
     => Digit a -> FingerTree v (Node v a) -> Digit a -> FingerTree v a
deep dl t dr = Deep v dl t dr
  where v = mconcat [measure dl, measure t, measure dr]

deepL :: Measured a v
      => Digit a -> FingerTree v (Node v a) -> Digit a -> FingerTree v a
deepL Zero (viewL -> NilL) dr     = fromFoldable dr
deepL Zero (viewL -> Cons n t) dr = deep (node2digit n) t dr
deepL dl t dr                     = deep dl t dr

deepR :: Measured a v
      => Digit a -> FingerTree v (Node v a) -> Digit a -> FingerTree v a
deepR dl (viewR -> NilR) Zero     = fromFoldable dl
deepR dl (viewR -> Snoc t n) Zero = deep dl t (node2digit n)
deepR dl t dr                     = deep dl t dr

node2digit :: Node v a -> Digit a
node2digit (Node2 _ a b)   = Two a b
node2digit (Node3 _ a b c) = Three a b c

list2digit []           = Zero
list2digit [a]          = One a
list2digit [a, b]       = Two a b
list2digit [a, b, c]    = Three a b c
list2digit [a, b, c, d] = Four a b c d

dcons :: a -> Digit a -> Digit a
dcons a (One b)       = Two a b
dcons a (Two b c)     = Three a b c
dcons a (Three b c d) = Four a b c d

dsnoc :: Digit a -> a -> Digit a
dsnoc (One b) a       = Two b a
dsnoc (Two c b) a     = Three c b a
dsnoc (Three d c b) a = Four d c b a

dheadL :: Digit a -> a
dheadL (One a)        = a
dheadL (Two a _)      = a
dheadL (Three a _ _)  = a
dheadL (Four a _ _ _) = a

dtailL :: Digit a -> Digit a
dtailL (One _)        = Zero
dtailL (Two _ b)      = One b
dtailL (Three _ b c)  = Two b c
dtailL (Four _ b c d) = Three b c d

dheadR :: Digit a -> a
dheadR (One a)        = a
dheadR (Two _ a)      = a
dheadR (Three _ _ a)  = a
dheadR (Four _ _ _ a) = a

dtailR :: Digit a -> Digit a
dtailR (One _)        = Zero
dtailR (Two a _)      = One a
dtailR (Three a b _)  = Two a b
dtailR (Four a b c _) = Three a b c

infixr 5 ◁
(◁) :: Measured a v => a -> FingerTree v a -> FingerTree v a
a ◁ Empty                      = Single a
a ◁ Single b                   = deep (One a) Empty (One b)
a ◁ Deep _ (Four b c d e) t dr = deep (Two a b) (node3 c d e ◁ t) dr
a ◁ Deep _ dl t dr             = deep (dcons a dl) t dr

infixl 5 ▷
(▷) :: Measured a v => FingerTree v a -> a -> FingerTree v a
Empty ▷ a                      = Single a
Single b ▷ a                   = deep (One b) Empty (One a)
Deep _ dl t (Four b c d e) ▷ a = deep dl (t ▷ node3 b c d) (Two e a)
Deep _ dl t dr ▷ a             = deep dl t (dsnoc dr a)

fromFoldable :: (Foldable t, Measured a v) => t a -> FingerTree v a
fromFoldable = foldr (◁) Empty

fromList :: Measured a v => [a] -> FingerTree v a
fromList = fromFoldable

data ViewL s a = NilL
               | Cons a (s a)

viewL :: Measured a v => FingerTree v a -> ViewL (FingerTree v) a
viewL Empty            = NilL
viewL (Single a)       = Cons a Empty
viewL (Deep _ dl t dr) = Cons (dheadL dl) (deepL (dtailL dl) t dr)

isEmpty :: Measured a v => FingerTree v a -> Bool
isEmpty (viewL -> NilL) = True
isEmpty _               = False

headL :: Measured a v => FingerTree v a -> a
headL (viewL -> Cons a _) = a

tailL :: Measured a v => FingerTree v a -> FingerTree v a
tailL (viewL -> Cons _ t) = t

data ViewR s a = NilR
               | Snoc (s a) a

viewR :: Measured a v => FingerTree v a -> ViewR (FingerTree v) a
viewR Empty            = NilR
viewR (Single a)       = Snoc Empty a
viewR (Deep _ dl t dr) = Snoc (deepR dl t (dtailR dr)) (dheadR dr)

headR :: Measured a v => FingerTree v a -> a
headR (viewR -> Snoc _ a) = a

tailR :: Measured a v => FingerTree v a -> FingerTree v a
tailR (viewR -> Snoc t _) = t

(⋈) :: Measured a v => FingerTree v a -> FingerTree v a -> FingerTree v a
xs ⋈ ys = app3 xs Zero ys
  where app3 :: Measured a v
             => FingerTree v a -> Digit a -> FingerTree v a -> FingerTree v a
        app3 Empty ts xs      = foldr (◁) xs ts
        app3 xs ts Empty      = foldl (▷) xs ts
        app3 (Single x) ts xs = x ◁ (foldr (◁) xs ts)
        app3 xs ts (Single x) = (foldl (▷) xs ts) ▷ x

        app3 (Deep _ dl₁ t₁ dr₁) ts (Deep _ dl₂ t₂ dr₂) =
          deep dl₁ (app3 t₁ (nodes dr₁ ts dl₂) t₂) dr₂

        -- Generated by GenNodes.hs
        nodes :: Measured a v => Digit a -> Digit a -> Digit a -> Digit (Node v a)
        nodes (One a0) Zero (One a1) =
          One (node2 a0 a1)
        nodes (One a0) Zero (Two a1 a2) =
          One (node3 a0 a1 a2)
        nodes (One a0) Zero (Three a1 a2 a3) =
          Two (node2 a0 a1) (node2 a2 a3)
        nodes (One a0) Zero (Four a1 a2 a3 a4) =
          Two (node3 a0 a1 a2) (node2 a3 a4)
        nodes (One a0) (One a1) (One a2) =
          One (node3 a0 a1 a2)
        nodes (One a0) (One a1) (Two a2 a3) =
          Two (node2 a0 a1) (node2 a2 a3)
        nodes (One a0) (One a1) (Three a2 a3 a4) =
          Two (node3 a0 a1 a2) (node2 a3 a4)
        nodes (One a0) (One a1) (Four a2 a3 a4 a5) =
          Two (node3 a0 a1 a2) (node3 a3 a4 a5)
        nodes (One a0) (Two a1 a2) (One a3) =
          Two (node2 a0 a1) (node2 a2 a3)
        nodes (One a0) (Two a1 a2) (Two a3 a4) =
          Two (node3 a0 a1 a2) (node2 a3 a4)
        nodes (One a0) (Two a1 a2) (Three a3 a4 a5) =
          Two (node3 a0 a1 a2) (node3 a3 a4 a5)
        nodes (One a0) (Two a1 a2) (Four a3 a4 a5 a6) =
          Three (node3 a0 a1 a2) (node2 a3 a4) (node2 a5 a6)
        nodes (One a0) (Three a1 a2 a3) (One a4) =
          Two (node3 a0 a1 a2) (node2 a3 a4)
        nodes (One a0) (Three a1 a2 a3) (Two a4 a5) =
          Two (node3 a0 a1 a2) (node3 a3 a4 a5)
        nodes (One a0) (Three a1 a2 a3) (Three a4 a5 a6) =
          Three (node3 a0 a1 a2) (node2 a3 a4) (node2 a5 a6)
        nodes (One a0) (Three a1 a2 a3) (Four a4 a5 a6 a7) =
          Three (node3 a0 a1 a2) (node3 a3 a4 a5) (node2 a6 a7)
        nodes (One a0) (Four a1 a2 a3 a4) (One a5) =
          Two (node3 a0 a1 a2) (node3 a3 a4 a5)
        nodes (One a0) (Four a1 a2 a3 a4) (Two a5 a6) =
          Three (node3 a0 a1 a2) (node2 a3 a4) (node2 a5 a6)
        nodes (One a0) (Four a1 a2 a3 a4) (Three a5 a6 a7) =
          Three (node3 a0 a1 a2) (node3 a3 a4 a5) (node2 a6 a7)
        nodes (One a0) (Four a1 a2 a3 a4) (Four a5 a6 a7 a8) =
          Three (node3 a0 a1 a2) (node3 a3 a4 a5) (node3 a6 a7 a8)
        nodes (Two a0 a1) Zero (One a2) =
          One (node3 a0 a1 a2)
        nodes (Two a0 a1) Zero (Two a2 a3) =
          Two (node2 a0 a1) (node2 a2 a3)
        nodes (Two a0 a1) Zero (Three a2 a3 a4) =
          Two (node3 a0 a1 a2) (node2 a3 a4)
        nodes (Two a0 a1) Zero (Four a2 a3 a4 a5) =
          Two (node3 a0 a1 a2) (node3 a3 a4 a5)
        nodes (Two a0 a1) (One a2) (One a3) =
          Two (node2 a0 a1) (node2 a2 a3)
        nodes (Two a0 a1) (One a2) (Two a3 a4) =
          Two (node3 a0 a1 a2) (node2 a3 a4)
        nodes (Two a0 a1) (One a2) (Three a3 a4 a5) =
          Two (node3 a0 a1 a2) (node3 a3 a4 a5)
        nodes (Two a0 a1) (One a2) (Four a3 a4 a5 a6) =
          Three (node3 a0 a1 a2) (node2 a3 a4) (node2 a5 a6)
        nodes (Two a0 a1) (Two a2 a3) (One a4) =
          Two (node3 a0 a1 a2) (node2 a3 a4)
        nodes (Two a0 a1) (Two a2 a3) (Two a4 a5) =
          Two (node3 a0 a1 a2) (node3 a3 a4 a5)
        nodes (Two a0 a1) (Two a2 a3) (Three a4 a5 a6) =
          Three (node3 a0 a1 a2) (node2 a3 a4) (node2 a5 a6)
        nodes (Two a0 a1) (Two a2 a3) (Four a4 a5 a6 a7) =
          Three (node3 a0 a1 a2) (node3 a3 a4 a5) (node2 a6 a7)
        nodes (Two a0 a1) (Three a2 a3 a4) (One a5) =
          Two (node3 a0 a1 a2) (node3 a3 a4 a5)
        nodes (Two a0 a1) (Three a2 a3 a4) (Two a5 a6) =
          Three (node3 a0 a1 a2) (node2 a3 a4) (node2 a5 a6)
        nodes (Two a0 a1) (Three a2 a3 a4) (Three a5 a6 a7) =
          Three (node3 a0 a1 a2) (node3 a3 a4 a5) (node2 a6 a7)
        nodes (Two a0 a1) (Three a2 a3 a4) (Four a5 a6 a7 a8) =
          Three (node3 a0 a1 a2) (node3 a3 a4 a5) (node3 a6 a7 a8)
        nodes (Two a0 a1) (Four a2 a3 a4 a5) (One a6) =
          Three (node3 a0 a1 a2) (node2 a3 a4) (node2 a5 a6)
        nodes (Two a0 a1) (Four a2 a3 a4 a5) (Two a6 a7) =
          Three (node3 a0 a1 a2) (node3 a3 a4 a5) (node2 a6 a7)
        nodes (Two a0 a1) (Four a2 a3 a4 a5) (Three a6 a7 a8) =
          Three (node3 a0 a1 a2) (node3 a3 a4 a5) (node3 a6 a7 a8)
        nodes (Two a0 a1) (Four a2 a3 a4 a5) (Four a6 a7 a8 a9) =
          Four (node3 a0 a1 a2) (node3 a3 a4 a5) (node2 a6 a7) (node2 a8 a9)
        nodes (Three a0 a1 a2) Zero (One a3) =
          Two (node2 a0 a1) (node2 a2 a3)
        nodes (Three a0 a1 a2) Zero (Two a3 a4) =
          Two (node3 a0 a1 a2) (node2 a3 a4)
        nodes (Three a0 a1 a2) Zero (Three a3 a4 a5) =
          Two (node3 a0 a1 a2) (node3 a3 a4 a5)
        nodes (Three a0 a1 a2) Zero (Four a3 a4 a5 a6) =
          Three (node3 a0 a1 a2) (node2 a3 a4) (node2 a5 a6)
        nodes (Three a0 a1 a2) (One a3) (One a4) =
          Two (node3 a0 a1 a2) (node2 a3 a4)
        nodes (Three a0 a1 a2) (One a3) (Two a4 a5) =
          Two (node3 a0 a1 a2) (node3 a3 a4 a5)
        nodes (Three a0 a1 a2) (One a3) (Three a4 a5 a6) =
          Three (node3 a0 a1 a2) (node2 a3 a4) (node2 a5 a6)
        nodes (Three a0 a1 a2) (One a3) (Four a4 a5 a6 a7) =
          Three (node3 a0 a1 a2) (node3 a3 a4 a5) (node2 a6 a7)
        nodes (Three a0 a1 a2) (Two a3 a4) (One a5) =
          Two (node3 a0 a1 a2) (node3 a3 a4 a5)
        nodes (Three a0 a1 a2) (Two a3 a4) (Two a5 a6) =
          Three (node3 a0 a1 a2) (node2 a3 a4) (node2 a5 a6)
        nodes (Three a0 a1 a2) (Two a3 a4) (Three a5 a6 a7) =
          Three (node3 a0 a1 a2) (node3 a3 a4 a5) (node2 a6 a7)
        nodes (Three a0 a1 a2) (Two a3 a4) (Four a5 a6 a7 a8) =
          Three (node3 a0 a1 a2) (node3 a3 a4 a5) (node3 a6 a7 a8)
        nodes (Three a0 a1 a2) (Three a3 a4 a5) (One a6) =
          Three (node3 a0 a1 a2) (node2 a3 a4) (node2 a5 a6)
        nodes (Three a0 a1 a2) (Three a3 a4 a5) (Two a6 a7) =
          Three (node3 a0 a1 a2) (node3 a3 a4 a5) (node2 a6 a7)
        nodes (Three a0 a1 a2) (Three a3 a4 a5) (Three a6 a7 a8) =
          Three (node3 a0 a1 a2) (node3 a3 a4 a5) (node3 a6 a7 a8)
        nodes (Three a0 a1 a2) (Three a3 a4 a5) (Four a6 a7 a8 a9) =
          Four (node3 a0 a1 a2) (node3 a3 a4 a5) (node2 a6 a7) (node2 a8 a9)
        nodes (Three a0 a1 a2) (Four a3 a4 a5 a6) (One a7) =
          Three (node3 a0 a1 a2) (node3 a3 a4 a5) (node2 a6 a7)
        nodes (Three a0 a1 a2) (Four a3 a4 a5 a6) (Two a7 a8) =
          Three (node3 a0 a1 a2) (node3 a3 a4 a5) (node3 a6 a7 a8)
        nodes (Three a0 a1 a2) (Four a3 a4 a5 a6) (Three a7 a8 a9) =
          Four (node3 a0 a1 a2) (node3 a3 a4 a5) (node2 a6 a7) (node2 a8 a9)
        nodes (Three a0 a1 a2) (Four a3 a4 a5 a6) (Four a7 a8 a9 a10) =
          Four (node3 a0 a1 a2) (node3 a3 a4 a5) (node3 a6 a7 a8) (node2 a9 a10)
        nodes (Four a0 a1 a2 a3) Zero (One a4) =
          Two (node3 a0 a1 a2) (node2 a3 a4)
        nodes (Four a0 a1 a2 a3) Zero (Two a4 a5) =
          Two (node3 a0 a1 a2) (node3 a3 a4 a5)
        nodes (Four a0 a1 a2 a3) Zero (Three a4 a5 a6) =
          Three (node3 a0 a1 a2) (node2 a3 a4) (node2 a5 a6)
        nodes (Four a0 a1 a2 a3) Zero (Four a4 a5 a6 a7) =
          Three (node3 a0 a1 a2) (node3 a3 a4 a5) (node2 a6 a7)
        nodes (Four a0 a1 a2 a3) (One a4) (One a5) =
          Two (node3 a0 a1 a2) (node3 a3 a4 a5)
        nodes (Four a0 a1 a2 a3) (One a4) (Two a5 a6) =
          Three (node3 a0 a1 a2) (node2 a3 a4) (node2 a5 a6)
        nodes (Four a0 a1 a2 a3) (One a4) (Three a5 a6 a7) =
          Three (node3 a0 a1 a2) (node3 a3 a4 a5) (node2 a6 a7)
        nodes (Four a0 a1 a2 a3) (One a4) (Four a5 a6 a7 a8) =
          Three (node3 a0 a1 a2) (node3 a3 a4 a5) (node3 a6 a7 a8)
        nodes (Four a0 a1 a2 a3) (Two a4 a5) (One a6) =
          Three (node3 a0 a1 a2) (node2 a3 a4) (node2 a5 a6)
        nodes (Four a0 a1 a2 a3) (Two a4 a5) (Two a6 a7) =
          Three (node3 a0 a1 a2) (node3 a3 a4 a5) (node2 a6 a7)
        nodes (Four a0 a1 a2 a3) (Two a4 a5) (Three a6 a7 a8) =
          Three (node3 a0 a1 a2) (node3 a3 a4 a5) (node3 a6 a7 a8)
        nodes (Four a0 a1 a2 a3) (Two a4 a5) (Four a6 a7 a8 a9) =
          Four (node3 a0 a1 a2) (node3 a3 a4 a5) (node2 a6 a7) (node2 a8 a9)
        nodes (Four a0 a1 a2 a3) (Three a4 a5 a6) (One a7) =
          Three (node3 a0 a1 a2) (node3 a3 a4 a5) (node2 a6 a7)
        nodes (Four a0 a1 a2 a3) (Three a4 a5 a6) (Two a7 a8) =
          Three (node3 a0 a1 a2) (node3 a3 a4 a5) (node3 a6 a7 a8)
        nodes (Four a0 a1 a2 a3) (Three a4 a5 a6) (Three a7 a8 a9) =
          Four (node3 a0 a1 a2) (node3 a3 a4 a5) (node2 a6 a7) (node2 a8 a9)
        nodes (Four a0 a1 a2 a3) (Three a4 a5 a6) (Four a7 a8 a9 a10) =
          Four (node3 a0 a1 a2) (node3 a3 a4 a5) (node3 a6 a7 a8) (node2 a9 a10)
        nodes (Four a0 a1 a2 a3) (Four a4 a5 a6 a7) (One a8) =
          Three (node3 a0 a1 a2) (node3 a3 a4 a5) (node3 a6 a7 a8)
        nodes (Four a0 a1 a2 a3) (Four a4 a5 a6 a7) (Two a8 a9) =
          Four (node3 a0 a1 a2) (node3 a3 a4 a5) (node2 a6 a7) (node2 a8 a9)
        nodes (Four a0 a1 a2 a3) (Four a4 a5 a6 a7) (Three a8 a9 a10) =
          Four (node3 a0 a1 a2) (node3 a3 a4 a5) (node3 a6 a7 a8) (node2 a9 a10)
        nodes (Four a0 a1 a2 a3) (Four a4 a5 a6 a7) (Four a8 a9 a10 a11) =
          Four (node3 a0 a1 a2) (node3 a3 a4 a5) (node3 a6 a7 a8) (node3 a9 a10 a11)

data Split f a = Split (f a) a (f a)
               deriving Show

splitList :: Measured a v => (v -> Bool) -> v -> [a] -> Split [] a
splitList p i [x] = Split [] x []
splitList p i (x : xs)
  | p i'      = Split [] x xs
  | otherwise = Split (x : l) a r
  where i' = i `mappend` measure x
        Split l a r = splitList p i' xs

splitDigit :: Measured a v => (v -> Bool) -> v -> Digit a -> Split Digit a
splitDigit p i d = Split (list2digit l) a (list2digit r)
  where Split l a r = splitList p i (toList d)

splitTree :: Measured a v
          => (v -> Bool) -> v -> FingerTree v a -> Split (FingerTree v) a
splitTree p i (Single a) = Split Empty a Empty
splitTree p i (Deep _ dl t dr)
  | p vdl = let Split l a r = splitDigit p i dl
            in Split (fromFoldable l) a (deepL r t dr)
  | p vt  = let Split tl ta tr = splitTree p vdl t
                Split l a r = splitList p (vdl `mappend` measure tl) (toList ta)
            in Split (deepR dl tl (list2digit l)) a (deepL (list2digit r) tr dr)
  | otherwise = let Split l a r = splitDigit p vt dr
                in Split (deepR dl t l) a (fromFoldable r)
  where vdl = i `mappend` measure dl
        vt  = vdl `mappend` measure t

split :: Measured a v
      => (v -> Bool) -> FingerTree v a -> (FingerTree v a, FingerTree v a)
split p Empty = (Empty, Empty)
split p t     = (l, a ◁ r)
  where Split l a r = splitTree p mempty t
