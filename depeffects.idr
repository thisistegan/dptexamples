import Effects
import Effect.State
import Effect.StdIO

--To be used as an example for discussion only. Note that it will not type check --


readIntBroke : { [STATE (Vect n Int), STDIO] } Eff ()
readIntBroke = do {let x = trim !getStr;
				put (cast x :: !get)}

readIntFixed : { [STATE (Vect n Int), STDIO] ==> [STATE (Vect (S n) Int), STDIO] } Eff ()
readIntFixed = do {let x = trim !getStr;
				putM (cast x :: !get)}

readInt : { [STATE (Vect n Int), STDIO] ==>
				{ok} if ok then [STATE (Vect (S n) Int), STDIO]
							else [STATE (Vect n Int), STDIO] } Eff Bool
readInt = do {let x = trim !getStr;
			(case all isDigit (unpack x) of
				False => pure False
				True => do {putM (cast x :: !get);
						pure True})