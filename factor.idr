module Main

import Effects
import Effect.Select
import Effect.Exception

{- Simple program used to find the factors of a given number. 
Demonstration of the SELECT effect used to solve constraint problems. 

The Select effect is a non-determinism effect which allows the program to choose
a value from a list of possibilities in such a way as the entire computation succeeds. -}

{- f : (x1 : a1) -> (x2 : a2) -> ... -> { effs } Eff t-}

{-Eff : (x : Type) -> List EFFECT -> (x -> List EFFECT) -> Type-}

factors : Int -> { [SELECT, EXCEPTION String] } Eff (Int, Int, Int)
factors n = do x <- select [1..(n-1)];
				y <- select [1..x];
				if (y * x == n)
					then pure (n, x,y)
					else raise "No factors"


main : IO ()
{- In the Maybe, factors will return the first triple found while in the List context, 
it will return all triples found. -}
main = do { print $ the (Maybe _) $ run (factors 234);
			 print $ the (List _) $ run (factors 234)}