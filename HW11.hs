module HW11 where

import           Prelude hiding (Maybe (..))
import           Data.Char
import           Control.Applicative

-- Problem #1: Extend the expression parser
newtype Parser a = P { parse :: String -> [(a,String)] }

item :: Parser Char
item = P $ \program -> case program of
                            [] -> []
                            (x : xs) -> [(x, xs)]

instance Functor Parser where
    -- fmap :: (a -> b) -> Parser a -> Parser b
    fmap f lf = P $ \program -> case parse lf program of
                                     [] -> []
                                     [(x, out)] -> [(f x, out)]

instance Applicative Parser where
    pure x = P $ \program -> [(x, program)]
    (<*>) pf pg = P $ \program -> case parse pf program of
                                      [] -> []
                                      [(x, out)] -> parse (x <$> pg) out

instance Monad Parser where
    f >>= g = P $ \program -> case parse f program of
                                   [] -> []
                                   [(x, out)] -> parse (g x) out

instance Alternative Parser where
    empty = P $ \program -> []
    f <|> g = P $ \program -> case parse f program of
                                   [] -> parse g program
                                   val@[(x, out)] -> val

sat :: (Char -> Bool) -> Parser Char
sat check = do x <- item
               if check x then return x else empty

char :: Char -> Parser Char
char ch = sat (==ch)

digit :: Parser Char
digit = sat (isDigit)

nat :: Parser Int
nat = do xs <- some digit
         return (read xs)

space :: Parser ()
space = do many (sat isSpace)
           return()

string :: String -> Parser String
string [] = return []
string (x : xs) = do char x
                     string xs
                     return (x : xs)

int :: Parser Int
int = do char ('-')
         x <- nat
         return $ -x
         <|> nat

token :: Parser a -> Parser a
token f = do space
             x <- f
             space
             return x

natural :: Parser Int
natural = token nat

integer :: Parser Int
integer = token int

symbol :: String -> Parser String
symbol xs = token $ string xs

eval :: String -> Int
eval = fst . head . parse expr

expr :: Parser Int
expr = do t <- term
          x <- pmexpr t
          return x

pmexpr :: Int -> Parser Int
pmexpr t = do { symbol "+"; x <- term; res <- pmexpr $ t + x; return res } <|> do { symbol "-"; x <- term; res <- pmexpr $ t - x; return res } <|> return t

term :: Parser Int
term = do f <- factor
          x <- pmterm f
          return x

pmterm :: Int -> Parser Int
pmterm t = do { symbol "*"; x <- factor; res <- pmterm $ t * x; return res } <|> do { symbol "/"; x <- factor; res <- pmterm $ t `div` x; return res } <|> return t

factor :: Parser Int
factor = do     symbol "("
                e <- expr
                symbol ")"
                return e
            <|> integer

-- End Problem #1
