module HW18 where

-- Code the derived linear algorithm for mss in Haskell
mss :: [Int] -> Int
mss = maximum . g 0
  where
    g _ [] = [0]
    g currrentS (x : xs) = currrentS + x : g (max 0 (currrentS + x)) xs