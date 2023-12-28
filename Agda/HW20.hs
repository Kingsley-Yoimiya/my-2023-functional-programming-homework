module HW20 where

-- Ch24: BMF2-2
comp' :: (Ord a) => [a] -> [a] -> [a]

comp' [] xs = xs -- dead end
comp' xs [] = xs -- dead end
comp' (x : xs) (y : ys)  | x < y = x : xs
                         | x > y = y : ys
                         | otherwise = y : comp' xs ys
comp :: (Ord a) => [a] -> [a] -> [a]
comp xs ys  | length xs < length ys = ys
            | length xs > length ys = xs
            | otherwise = comp' xs ys

add :: (a -> Bool) -> [a] -> a -> [a]
add p xs y = if p y then xs ++ [y] else []


lsp :: (Ord a) => (a -> Bool) -> [a] -> [a]
lsp p = foldl comp [] . scanl (add p) []

-- Ch25: BMF3-2
tailsums :: (Num a) => [a] -> [a]
tailsums = fst. foldr oplus ([0], 0)
        where oplus a (res, sum) = (res ++ [a + sum], sum + a) 
