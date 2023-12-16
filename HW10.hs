module HW10 where

import           Prelude hiding (Applicative (..), Functor (..), Monad (..))

infixl 4 <$
infixl 1 >>, >>=
infixl 4 <*>

class Functor f where
  fmap        :: (a -> b) -> f a -> f b
  (<$)        :: a -> f b -> f a
  (<$)        =  fmap . const

class Functor f => Applicative f where
  pure :: a -> f a
  (<*>) :: f (a -> b) -> f a -> f b

class Applicative m => Monad m where
  return :: a -> m a
  return = pure
  (>>=) :: m a -> (a -> m b) -> m b
  (>>) :: m a -> m b -> m b
  m >> k = m >>= \_ -> k

-- Problem #1: Monad ((->) a)
instance Functor ((->) a) where
  fmap = (.)

instance Applicative ((->) a) where
  pure = const
  (<*>) f g = \x -> f x $ g x

instance Monad ((->) r) where
  (>>=) f g = \x -> let x' = f x in g x' x
-- End Problem #1

-- Problem #2: Functor, Applicative, Monad
data Expr a
  = Var a
  | Val Int
  | Add (Expr a) (Expr a)
  deriving (Show)

instance Functor Expr where
  fmap f (Var x) = Var (f x)
  fmap f (Val x) = Val x
  fmap f (Add x y) = Add (fmap f x) (fmap f y)

instance Applicative Expr where
  pure x = Var x
  (<*>) (Var f) g = fmap f g
  (<*>) (Val f) g = Val f
  (<*>) (Add x y) g = Add (x <*> g) (y <*> g)

instance Monad Expr where
  (>>=) (Var f) trans = trans f
  (>>=) (Val f) _ = Val f
  (>>=) (Add x y) trans = Add (x >>= trans) (y >>= trans)


-- Write your example here:
expr1 = (Add (Var "x") (Add (Val 114) (Var "x")))
expr2 = expr1 >>= (\x -> Add (Var 114) (Var 114))
-- And explain what the >>= operator for this type does
{- Manual #2
  将 Expr a 中 Var a 批量替换成一个表达式 / 值。
-}
-- End Problem #2
