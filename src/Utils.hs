module Utils where

import System.IO.Unsafe

-- useful for debugging
debug :: Show a => String -> a -> a
debug str x = seq (unsafePerformIO $ do putStr "<"; putStr str; putStr ": "; print x; putStr ">") x

update :: Eq a => (a -> b) -> a -> b -> a -> b
update f a b x = if x == a then b else f x

partitions :: [a] -> [[[a]]]
partitions [] = [[]]
partitions (x:xs) = [[x]:yss | yss <- partitions xs] ++ [(x:ys):yss | (ys:yss) <- partitions xs]

catalan :: Int -> [[Int]]
catalan n = map (map length) $ partitions [1..n]

merge :: [a] -> [a] -> [a]
merge [] bs = bs
merge (a : as) bs = a : merge bs as

merges :: [[a]] -> [a]
merges [] = []
merges (as : ass) = merge as (merges ass)

functions :: (Eq a) => [a] -> [b] -> [a -> b]
functions [] _ = [undefined]
functions (a : as) bs = merges [[update f a b | f <- functions as bs] | b <- bs]