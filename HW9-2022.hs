module HW9 where

calc :: Int -> IO Int
calc 0 = do
    return 0
calc n = do
    snumber <- getLine
    let rnumber = read snumber :: Int
    ret <- calc (n - 1)
    return $ rnumber + ret

adder :: IO ()
adder = do
    putStr "How many numbers? "
    snumber <- getLine
    let number = read snumber :: Int
    ret <- calc number
    putStrLn ("The total is " ++ (show ret))
