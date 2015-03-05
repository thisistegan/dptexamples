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
cycle v = (last v)::(tail v)

data GState = Running Nat Nat Nat Nat| NotRunning
data Hand = Rock | Paper | Scissors 
data Game: GState->Type
data Result= Win|Lose|Tie

toHand: String -> Hand
toHand "R" = Rock
toHand "S" = Scissors
toHand _ = Paper

data RPS : GState -> Type where
     Init     : RPS NotRunning 
     GameOver  : Nat->Nat->Nat->RPS NotRunning
     MkG      : (guesses : Vect (S n) Hand) ->
                (wins : Nat) ->
                (losses: Nat)->
                (ties: Nat)->
                (round: Nat)->
                RPS (Running wins losses ties round)

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
    show (GameOver w l t) = "Game over! Your score was " ++ (cast (toIntegerNat w)) ++ " and mine was " ++ (cast (toIntegerNat l))
    show (MkG g w l t r) = "We're still playin! Your score is " ++ (cast (toIntegerNat w)) ++ " and mine is " ++ (cast (toIntegerNat l))



initState: (x: Vect 3 Hand) -> RPS (Running Z Z Z 3)
initState hand = MkG hand Z Z Z 3 


data Rules: Effect where
    Play: (x:Hand)->{ RPS (Running w l t (S r)) ==> {res} (case res of 
                                            Win => RPS (Running (S w) l t r)
                                            Lose => RPS (Running w (S l) t r)
                                            Tie => RPS (Running w l (S t) r))} Rules Result
    Over: { RPS (Running w l t 0) ==> RPS NotRunning } Rules ()
    NewGame: (h: Vect 3 Hand) -> {g==>RPS (Running Z Z Z 3)} Rules ()
    Get: { g } Rules g

RPSGAME: GState -> EFFECT
RPSGAME g = MkEff (RPS g) Rules


play: Hand -> { [RPSGAME (Running w l t (S k))] ==> {res} [RPSGAME (case res of 
                                            Win => (Running (S w) l t k)
                                            Lose => (Running w (S l) t k)
                                            Tie => (Running w l (S t) k))]} Eff Result

play hand = call(Main.Play hand)


over : { [RPSGAME (Running w l t 0)] ==> [RPSGAME NotRunning]} Eff ()
over = call Over

newgame: (h: Vect 3 Hand) -> { [RPSGAME g] ==> [RPSGAME (Running Z Z Z 3)]} Eff ()
newgame h = call(NewGame h)

get: { [RPSGAME g] } Eff (RPS g)
get = call Get

instance Handler Rules m where
    handle st Get k = k st st
    handle st (NewGame hand) k = k () (initState hand)
    handle (MkG g w l t (S r)) (Play x) k = case (winlose x (head g)) of
        Win => k Win (MkG ((last g)::(init g)) (S w) l t r);
        Lose => k Lose (MkG ((last g)::(init g)) w (S l) t r)
        Tie => k Tie (MkG ((last g)::(init g)) w l (S t) r)
    handle (MkG g w l t Z) Over k = k () (GameOver w l t)

  
game : { [RPSGAME (Running w l t (S r)), STDIO] ==> 
         [RPSGAME NotRunning, STDIO] } Eff ()
game  = do {putStrLn (show !get);
                putStr "Enter guess: ";
                let guess = trim !getStr;
                processPlay (toHand guess)}
            where
                processPlay: Hand -> {[RPSGAME (Running w l t (S r)), STDIO] ==> 
                             [RPSGAME NotRunning, STDIO]} Eff ()
                processPlay g {r}
                    = case !(play g) of 
                        Win => do {putStrLn "Ah, you won!!!";
                                (case r of 
                                Z => over
                                (S k) => game)}
                        Lose => do {putStrLn "Hah, I win!!";
                            (case r of 
                            Z => over
                            (S k) => game)}
                        Tie => do {putStrLn "Looks like we tied....";
                            (case r of 
                            Z => over
                            (S k) => game)}

runGame : { [RPSGAME NotRunning, RND, SYSTEM, STDIO] } Eff ()
runGame = do { newgame [Rock,Paper,Scissors]
             game
             putStrLn (show !get)}

main : IO ()
main = run runGame
