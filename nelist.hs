{-# OPTIONS_GHC -Wall #-}

{-# LANGUAGE GADTs, FlexibleInstances #-}

module NeList where

-- Beginning example of GADTs:  adding a flag to lists to 
-- indicate whether they are empty. The head function then is 
-- defined only for nonempty lists.

-- Developed as class notes for Advanced Programming, Fall 2011
-- at The University of Pennsylvania

data Empty
data NonEmpty

data Flag f where
  Empty    :: Flag Empty
  NonEmpty :: Flag NonEmpty

data List f a' where 
  Nil  :: List Empty a
  Cons :: a -> List flag a -> List NonEmpty a

instance Eq (List Empty a) where
  Nil == Nil = True

instance Eq a => Eq (List NonEmpty a) where
  (Cons x1 Nil) == (Cons x2 Nil) = (x1 == x2)
  (Cons _ Nil) == (Cons _ (Cons _ _)) = False
  (Cons _ (Cons _ _)) == (Cons _ Nil) = False
  (Cons x1 xs1@(Cons _ _)) == (Cons x2 xs2@(Cons _ _)) =
    x1 == x2 && xs1 == xs2

instance Show (List Empty a) where
  show = const "[]"

instance Show a => Show (List NonEmpty a) where
  show xs = '[' : showHelper ", " "]" xs

instance Ord a => Ord (List NonEmpty a) where
  (Cons x1 xs1) `compare` (Cons x2 xs2) = case x1 `compare` x2 of
    LT -> LT
    GT -> GT
    EQ -> case (xs1, xs2) of
      (Nil, Nil)               -> EQ
      (Nil, (Cons _ _))        -> LT
      ((Cons _ _), Nil)        -> GT
      ((Cons _ _), (Cons _ _)) -> xs1 `compare` xs2

showHelper :: Show a => String -> String -> List NonEmpty a -> String
showHelper _ term   (Cons x Nil) = show x ++ term
showHelper sperse term (Cons x xs'@(Cons _ _)) = 
      show x ++ sperse ++ showHelper sperse term xs'

nehead :: List NonEmpty a -> a
nehead (Cons x _) = x
-- head Nil = error "head of nil"

netail :: List NonEmpty a -> Either (List Empty a)
                                 (List NonEmpty a)
netail (Cons _ Nil) = Left Nil
netail (Cons _ xs@(Cons _ _)) = Right xs

necons :: a -> 
          Either (List Empty a) (List NonEmpty a)          
          -> List NonEmpty a
necons a (Left Nil) = Cons a Nil
necons a (Right xs) = Cons a xs

nemap :: (a -> b) -> List f a -> List f b
nemap _ Nil = Nil
nemap f (Cons x xs) = Cons (f x) (nemap f xs)

neLast :: List NonEmpty a -> a 
neLast (Cons x Nil) = x
neLast (Cons _ xs@(Cons _ _)) = neLast xs

nefold :: (a -> b -> b) -> (a -> b) -> List NonEmpty a -> b
nefold _f fbase (Cons x Nil) = fbase x
nefold f fbase (Cons x xs@(Cons _ _)) =
  f x (nefold f fbase xs)

instance Functor (List NonEmpty) where
--  fmap :: (a -> b) -> List NonEmpty a -> List NonEmpty b
  fmap f xs = nefold (\a bs -> Cons (f a) bs) (\a -> Cons (f a) Nil) xs

neall :: (a -> Bool) -> List NonEmpty a -> Bool
neall p xs = nefold (\a b -> p a && b) p xs

neany :: (a -> Bool) -> List NonEmpty a -> Bool
neany p xs = nefold (\a b -> p a || b) p xs

nedrop :: (a -> Bool) -> List NonEmpty a -> [a]
nedrop p xs = nefold (\x xs' -> if p x then xs' else x:xs')
                     (\x     -> if p x then [] else [x])
                     xs

nebuild :: [a] -> List NonEmpty a
nebuild []     = error "can't build NonEmpty from []"
nebuild [x]    = Cons x Nil
nebuild (x:xs@(_:_)) = Cons x $ nebuild xs