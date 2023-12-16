module HW13 where

-- Problem #1: Write a Haskell program to solve the maximum segment
--   sum problem, following the three steps in the slides.

mss :: [Integer] -> Integer
mss ns = maximum [sum xs |  let len = length ns,
                            l <- [1..len],
                            r <- [(l - 1)..len],
                            let xs = take (r - l + 1) (drop (l - 1) ns)]

-- End Problem #1

-- Problem #2: Write a Haskell program to solve the maximum segment
--   sum problem, using the smart algorithm in the slides.

mss' :: [Integer] -> Integer
mss' ns = maximum (foldl (\x y -> if last x + y >= 0 then x ++ [last x + y] else x ++ [0]) [0] ns)

-- End Problem #2
