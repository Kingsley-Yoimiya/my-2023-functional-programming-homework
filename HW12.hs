module HW12 where

import           Prelude hiding (Maybe (..))

-- Problem #1: Maybe, Foldable and Traversable
data Maybe a = Nothing | Just a
  deriving (Show, Eq, Ord)

instance Functor Maybe where
  -- fmap :: (a -> b) -> Maybe a -> Maybe b
  fmap _ Nothing = Nothing
  fmap f (Just a) = Just (f a)

instance Foldable Maybe where
  -- foldMap:: Monoid b => (a -> b) -> Maybe a -> b
  foldMap f (Nothing) = mempty
  foldMap f (Just x) = f x
  -- foldr :: (a -> b -> b) -> b -> Maybe a -> b
  foldr f cur_val (Just x) = f x cur_val
  foldr f cur_val Nothing = cur_val
  -- foldl :: (b -> a -> b) -> b -> Maybe a -> b
  foldl f cur_val (Just x) = f cur_val x
  foldl f cur_val Nothing = cur_val

foldMaybe :: Monoid a => Maybe a -> a
foldMaybe (Nothing) = mempty
foldMaybe (Just x) = x

instance Traversable Maybe where
  -- tranverse :: applicative f => (a -> f b) -> Maybe a -> f (Maybe b)
  traverse g (Just x) = pure Just <*> g x
  traverse g (Nothing) = pure Nothing
-- End Problem #1

-- Problem #2: Tree, Foldable and Traversable
data Tree a = Leaf | Node (Tree a) a (Tree a)
  deriving Show

instance Functor Tree where
  -- fmap :: (a -> b) -> Tree a -> Tree b
  fmap _ Leaf = Leaf
  fmap f (Node l x r) = (Node (fmap f l) (f x) (fmap f r))

instance Foldable Tree where
  -- foldMap :: Monoid b => (a -> b) -> Tree a -> b
  foldMap _ Leaf = mempty
  foldMap f (Node l x r) = (foldMap f l) <> (f x) <> (foldMap f r)
  -- foldl :: (b -> a -> b) -> b -> Tree a -> b
  foldl f cur_val Leaf = cur_val
  foldl f cur_val (Node l x r) = foldl f (f (foldl f cur_val l) x) r
  -- foldr :: (a -> b -> b) -> b -> Tree a -> b
  foldr f cur_val Leaf = cur_val
  foldr f cur_val (Node l x r) = foldr f (f x (foldr f cur_val r)) l

foldTree :: Monoid a => Tree a -> a
foldTree (Leaf) = mempty
foldTree (Node l x r) = (foldTree l) <> x <> (foldTree r)

instance Traversable Tree where
  -- traverse :: applicative f => (a -> f b) -> Tree a -> f (Tree b)
  traverse g Leaf = pure Leaf
  traverse g (Node l x r) = pure Node <*> (traverse g l) <*> (g x) <*> (traverse g r)
-- End Problem #2

-- Problem #3: fibonacci using zip/tail/list-comprehension
fibs :: [Integer]
fibs = [0, 1] ++ (map (\(x, y) -> x + y) $ zip fibs $ tail fibs)
-- End Problem #3

-- Problem #4: Newton's square root
sqroot :: Double -> Double
sqroot n = (head . filter (\a -> (abs(a - (a + n / a) / 2) < 0.000001))) $ iterate (\a -> (a + n / a) / 2) 1
-- End Problem #4
