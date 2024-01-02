module HW21 where

unfold :: (b -> Bool) -> (b -> a) -> (b -> b) -> b -> [a]
unfold p f g x = if p x then [] else f x : unfold p f g (g x)

-- Ch26: BMF4-1
merge :: (Ord a) => [a] -> [a] -> [a]
merge xs ys = unfold p f g (xs, ys)
  where
    p (x : _, y : _) = False
    p _ = True
    f (x : _, y : _) = if x < y then x else y
    g (x : xs, y : ys) = if x < y then (xs, y : ys) else (x : xs, ys)

-- Ch26: BMF4-2
-- Change the following definition of fib to generate all Fibonacci
-- numbers that are less than 1000,000.
fib :: (Int, Int) -> [Int]
fib = unfold ((> 1000000) . snd) fst (\(x, y) -> (y, x + y))
