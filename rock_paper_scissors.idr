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

--We can make our own EFFECTS!!!--

--Here is a simple program to play Rock Paper Scissors for a series of rounds, keeping track of the score.--

--Define the same state. Can either be running (with scores win, lose, tie) or not running. 
data GState = Running Nat Nat Nat Nat| NotRunning

--Possible hands to play--
data Hand = Rock | Paper | Scissors 

--The result of possible plays--
data Result = Win | Lose| Tie


{-Helper function used to convert a string into a hand. Currently the only valid inputs for 
non-Paper hands are r and s. All others default to Paper-}
toHand: String -> Hand
toHand "r"= Rock
toHand "s" = Scissors
toHand _ = Paper

{-Here we define a function from the game state to a type, giving a concrete representation of
 the game state. This is the resource of the effect we will be making. -}

{-There are three possible types. Before the game starts, after the game is over, and during 
the game (MkG). MkG captures the sta eof a game currently running.-}  

--guesses correponds to a vector of the computers guesses--

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

--All the ways that two hands can be played and the appropriate results.--
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

--An instance of show. Defines what to output in each of the game states--

instance Show (RPS s) where
    show Init = "Not ready yet"
    show (GameOver w l t) = "Game over! Your score was " ++ (cast (toIntegerNat w)) ++ " and mine was " ++ (cast (toIntegerNat l))
    show (MkG g w l t r) = "We're still playin! Your score is " ++ (cast (toIntegerNat w)) ++ " and mine is " ++ (cast (toIntegerNat l))


{-The inital state. A function of a vector of hands, the computer's guesses. Currently I have 
set the number of rounds to be five and the vector of the computer's guesses to be the same 
length.-}

initState: (x: Vect 5 Hand) -> RPS (Running Z Z Z 5)
initState hand = MkG hand Z Z Z 5 

--My effects signature. Note how the resources of the effect RPS can change. This is especially interesting in the Play case as the change in the resource depends on res, the result of playing a hand. Note that this signature does not explain how the rules are implemented. --


data Rules: Effect where
    --We continue to play as long as the number of rounds has not reached zero, updating the win, lose or tie count and the number of rounds remaining as appropriate --

    Play: (x:Hand)->{ RPS (Running w l t (S r)) ==> {res} (case res of 
                                            Win => RPS (Running (S w) l t r)
                                            Lose => RPS (Running w (S l) t r)
                                            Tie => RPS (Running w l (S t) r))} Rules Result

    --The game is over when the number of rounds left has reached zero--
    Over: { RPS (Running w l t 0) ==> RPS NotRunning } Rules ()

    --A new game takes a new vector of guesses--
    NewGame: (h: Vect 5 Hand) -> {g==>RPS (Running Z Z Z 5)} Rules ()

    --Get just returns the current effect--
    Get: { g } Rules g

{-MkEff constructs an EFFECT by taking the resource type and the effect signature. Converts our GState to something usable in an effects list. -}

RPSGAME: GState -> EFFECT
RPSGAME g = MkEff (RPS g) Rules

--The call function converts an effect (such as Play hand) into a function in Eff. The proof that the effect is available is essesntialy an index into the list of effects and so can be automatically constructed.--

play: Hand -> { [RPSGAME (Running w l t (S k))] ==> {res} [RPSGAME (case res of 
                                            Win => (Running (S w) l t k)
                                            Lose => (Running w (S l) t k)
                                            Tie => (Running w l (S t) k))]} Eff Result

play hand = call(Main.Play hand)


over : { [RPSGAME (Running w l t 0)] ==> [RPSGAME NotRunning]} Eff ()
over = call Over

newgame: (h: Vect 5 Hand) -> { [RPSGAME g] ==> [RPSGAME (Running Z Z Z 5)]} Eff ()
newgame h = call(NewGame h)

get: { [RPSGAME g] } Eff (RPS g)
get = call Get

--We need to explain how each effect is executed in a particular computation context m in order to run the effectful program. This is achieved by creating an instance of the class Handler. --

--Handler e m means that the effect with signature e is declared in the context m.--

--The handle function takes a resource of input (in this case the current resource associated with RPSGAME), the effectful operation, a continuation (k) which is passed the result of the operation and updated resource. --


instance Handler Rules m where
    handle st Get k = k st st
    handle st (NewGame hand) k = k () (initState hand)
    handle (MkG g w l t (S r)) (Play x) k = case (winlose x (head g)) of
        Win => k Win (MkG ((last g)::(init g)) (S w) l t r);
        Lose => k Lose (MkG ((last g)::(init g)) w (S l) t r)
        Tie => k Tie (MkG ((last g)::(init g)) w l (S t) r)
    handle (MkG g w l t Z) Over k = k () (GameOver w l t)


--Now, we can actually play the game :)--

--Note the (!)-notation. !expr means that the expression should be evaluated and then implicitely bound. !expr will evaluate expression, bind it to a fresh name x, and then replace !expr with x. A method to escape verbose do notation. --

  
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
runGame = do { newgame [Rock,Paper,Scissors, Scissors, Paper]
             game
             putStrLn (show !get)}

--We use run to run an effected profram in Eff--
main : IO ()
main = run runGame
