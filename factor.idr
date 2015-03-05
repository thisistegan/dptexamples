module Main

import Effects
import Effect.Select
import Effect.Exception

{- Simple program used to find the factors of a given number. 
Used to demonstrate the SELECT effect used to solve constraint problems-}

factors : Int -> { [SELECT, EXCEPTION String] } Eff (Int, Int, Int)
factors n = do x <- select [1..(n-1)];
				y <- select [1..x];
				if (y * x == n)
					then pure (n, x,y)
					else raise "No factors"


main : IO ()
main = print $ the (List _) $ run (factors 234)