data Tree a = Leaf | Node (Tree a) a (Tree a) deriving (Show)
instance Functor Tree where
 -- fmap :: (a -> b) -> Tree a -> Tree b
    fmap _ Leaf = Leaf
    fmap f (Node ls x rs) = Node (fmap f ls) (f x) (fmap f rs)
