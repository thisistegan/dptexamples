module Main

import Effects
import Effect.StdIO
import Effect.System
import Effect.Random
import Data.So
import Data.Fin
import Data.Vect
import Effect.Random
import Effect.Select


cycle: Vect (S n) a -> Vect (S n) a
cycle v = insertAt 0 (last v) (tail v)

data GState = Running Nat Nat Nat| NotRunning
data Hand = Rock | Paper | Scissors 
data Game: GState->Type
data Result= Win|Lose|Tie

toHand: String -> Hand
toHand "R" = Rock
toHand "S" = Scissors
toHand _ = Paper

data RPS : GState -> Type where
     Init     : RPS NotRunning 
     GameOver  : Nat->Nat->RPS NotRunning
     MkG      : (guesses : Vect (S n) Hand) ->
                (score : Nat) ->
                (scoregame: Nat)->
                (round: Nat)->
                RPS (Running score scoregame round)

instance Default (RPS NotRunning) where
    default = Init


winlose: Hand->Hand->Result
winlose Rock Rock = Tie
winlose Paper Paper = Tie
winlose Scissors Scissors = Tie
winlose Rock Paper = Lose
winlose Paper Scissors = Lose
winlose Scissors Rock = Lose
winlose Paper Rock = Win
winlose Scissors Paper = Win
winlose Rock Scissors = Win

instance Show (RPS s) where
    show Init = "Not ready yet"
    show (GameOver s sg) = "Game over! Your score was " ++ (cast (toIntegerNat s)) ++ " and mine was " ++ (cast (toIntegerNat sg))
    show (MkG g s sg r) = "We're still playin! Your score is " ++ (cast (toIntegerNat s)) ++ " and mine is " ++ (cast (toIntegerNat sg))


initState: (x: Vect 3 Hand) -> RPS (Running Z Z 3)
initState hand = MkG hand Z Z 3 

data Rules: Effect where
    Play: (x:Hand)->{ RPS (Running n m (S r)) ==> {res} (case res of 
                                            Win => RPS (Running (S n) m r)
                                            Lose => RPS (Running n (S m) r)
                                            Tie => RPS (Running n m r))} Rules Result
    Over: { RPS (Running n m 0) ==> RPS NotRunning } Rules ()
    NewGame: (h: Vect 3 Hand) -> {g==>RPS (Running Z Z 3)} Rules ()
    Get: { g } Rules g

RPSGAME: GState -> EFFECT
RPSGAME g = MkEff (RPS g) Rules


play: Hand -> { [RPSGAME (Running n m (S k))] ==> {res} [RPSGAME (case res of 
                                            Win => (Running (S n) m k)
                                            Lose => (Running n (S m) k)
                                            Tie => (Running n m k))]} Eff Result

play hand = call(Main.Play hand)

over : { [RPSGAME (Running n m 0)] ==> [RPSGAME NotRunning]} Eff ()
over = call Over

newgame: (h: Vect 3 Hand) -> { [RPSGAME g] ==> [RPSGAME (Running Z Z 3)]} Eff ()
newgame h = call(NewGame h)

get: { [RPSGAME g] } Eff (RPS g)
get = call Get

instance Handler Rules m where
    handle st Get k = k st st
    handle st (NewGame hand) k = k () (initState hand)
    handle (MkG g s sg (S r)) (Play x) k = case (winlose x (last g)) of
        Win => k Win (MkG (cycle g) (S s) sg r);
        Lose => k Lose (MkG (cycle g) s (S sg) r)
        Tie => k Tie (MkG (cycle g) s sg r)
    handle (MkG g s sg Z) Over k = k () (GameOver s sg)
   
  
game : { [RPSGAME (Running s sg (S r)), STDIO] ==> 
         [RPSGAME NotRunning, STDIO] } Eff ()
game  = do {putStrLn (show !get);
                putStr "Enter guess: ";
                let guess = trim !getStr;
                processPlay (toHand guess)}
            where
                processPlay: Hand -> {[RPSGAME (Running s sc (S r)), STDIO] ==> 
                             [RPSGAME NotRunning, STDIO]} Eff ()
                processPlay g {r}
                    = case !(play g) of 
                        Win => case r of 
                                Z => over
                                (S k) => game
                        Lose => case r of 
                            Z => over
                            (S k) => game
                        Tie => case r of 
                            Z => over
                            (S k) => game


runGame : { [RPSGAME NotRunning, RND, SYSTEM, STDIO] } Eff ()
runGame = do { newgame [Rock,Paper,Scissors]
             game
             putStrLn (show !get)}
main : IO ()
main = run runGame

