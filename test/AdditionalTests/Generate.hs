module AdditionalTests.Generate ( allStrs ) where

allStrs :: [a] -> Int -> Int -> [[a]]
allStrs _ _ 0 = [[]]
allStrs a 0 n = []:allStrs a 1 n
allStrs a m n = let smaller = allStrs a (m - 1) (n - 1)
                in ((\str chr -> chr:str) <$> smaller <*> a)
