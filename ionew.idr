module ionew

import Prelude.List

{- Only point of this is to demonstrate case where type can only be known after evaluation. 
What happens in Idris in this case? Can ignore until next comment is reached. Based on Edwin
Brady's old code. -}

data Lock = Locked | Unlocked

data FType = FUnit | FInt | FStr | FPtr | FFloat | FAny Type
           
i_ftype : FType -> Type
i_ftype FInt = Int
i_ftype FStr = String
i_ftype FPtr = Ptr
i_ftype FFloat = Float
i_ftype FUnit = ()
i_ftype (FAny ty) = ty

data ForeignFun = FFun String (List FType) FType

f_retType : ForeignFun -> FType
f_retType (FFun nm args ret) = ret

f_args : ForeignFun -> (List FType)
f_args (FFun nm args ret) = args

f_name : ForeignFun -> String
f_name (FFun nm args ret) = nm

data FArgList : (List FType) -> Type where
    fNil : FArgList Nil
    fCons : {x:FType} -> (fx:i_ftype x) -> (fxs:FArgList xs) ->
			 (FArgList (x::xs))

fapp : {xs,ys:List FType} -> 
       (FArgList xs) -> (FArgList ys) -> (FArgList (xs ++ ys))
fapp fNil fxs = fxs
fapp (fCons fx fxs) fys = fCons fx (fapp fxs fys)

namespace IONew{
using (A:Type){
  data IONew : Type -> Type

  data IORef A = MkIORef Int

  data Command : Type where
      PutStr : String -> Command
      GetStr : Command
      Fork : {A:Type} -> A -> Command
      NewLock : Int -> Command
      DoLock : Lock -> Command
      DoUnlock : Lock -> Command
      NewRef : Command
      ReadRef : Type -> Int -> Command
      WriteRef : {A:Type} -> Int -> A -> Command
      While : (IONew Bool) -> (IONew ()) -> Command
      WhileAcc : {A:Type} -> (IONew Bool) -> A -> (A -> IONew A) -> Command
      Within : Int -> (IONew A) -> (IONew A) -> Command
      IOLift : {A:Type} -> (IONew A) -> Command 
      Foreign : (f:ForeignFun) -> 
  	        (args:FArgList (f_args f)) -> Command 


  Response : Command -> Type
  Response (PutStr s) = ()
  Response GetStr = String
  Response (Fork proc) = ()
  Response (NewLock i) = Lock
  Response (DoLock l) = ()
  Response (DoUnlock l) = ()
  Response NewRef = Int
  Response (ReadRef A i) = A
  Response (WriteRef i val) = ()
  Response (While _ body) = ()
  Response (WhileAcc {A} _ acc body) = A
  Response (Within {A} time body failure) = A
  Response (IOLift {A} f) = A
  Response (Foreign t args) = i_ftype (f_retType t)

  data IONew: Type -> Type where
     IOReturn : A -> (IONew A)
     IODo : (c:Command) -> ((Response c) -> (IONew A)) -> (IONew A)


  bind : (IONew a) -> (a -> (IONew b)) -> (IONew b)
  bind (IOReturn a) k = k a
  bind (IODo c p) k = IODo c (\y => (bind (p y) k));

  ret : a -> IONew a
  ret x = IOReturn x
  
}
}

kbind : (IONew a) -> (a -> b) -> (IONew b)
kbind (IOReturn a) k = IOReturn (k a)
kbind (IODo c p) k = IODo c (\x => (kbind (p x) k))

{-Consider the definition of fork. We have IDo (c:command) l. We need l:Response c -> (IONew a
-}

{-Based on pattern matching, Idris will find that l = Response(Fork proc) -> IONew(a). Great,
so all we need know is Response(Fork proc) = (), which we clearly know from the definition of
Response given above-}

{-The compiler does not know this though. If we run this without the EqualityFork proposition
and its proof, the compiler will be unable to unify Response (Fork proc) with (). You can edit
the code to try this yourself. -}

{-Thus, we have to manually prove Response(Fork proc) = (), which is fairly trivial but needed
-}

EqualityFork: (proc:IO())->Response (Fork proc) = ()
EqualityFork proc = ?EqualF

EqualityNLock: (i:Int)->Response (NewLock i) = Lock
EqualityNLock i = ?EqualNL

EqualityLock: (l:Lock)->Response (DoLock l) = ()
EqualityLock l = ?EqualL

EqualityULock: (l:Lock)->Response (DoUnlock l) = ()
EqualityULock l = ?EqualUL

EqualityNIORef: Response NewRef = Int
EqualityNIORef= ?EqualNRef

fork : (proc:IONew ()) -> (IONew ())
fork proc = IODo (Fork proc) (\x=> IOReturn x)

newLock : Int -> (IONew Lock)
newLock i = IODo (NewLock i) (\l => (IOReturn l))

lock : Lock -> (IONew ())
lock l = IODo (DoLock l) (\a => (IOReturn a))

unlock : Lock -> (IONew ())
unlock l = IODo (DoUnlock l) (\a => (IOReturn a))

newIORefPrim : IONew Int
newIORefPrim = IODo (NewRef) (\i => (IOReturn i))

using (A:Type){
  EqualityReadRef: (i:Int)-> Response(ReadRef A i) = A
  EqualityReadRef {A} i = ?EqualRR

  EqualityWriteRef: (i:Int)->(val:A)-> Response(WriteRef i val) = ()
  EqualityWriteRef i val = ?EqualWR

  readIORefPrim : Int -> (IONew A)
  readIORefPrim {A} i = IODo (ReadRef A i) (\a => (IOReturn a))

  writeIORefPrim : Int -> A -> (IONew ())
  writeIORefPrim {A} i val = IODo (WriteRef {A} i val) (\a => (IOReturn a))

  readIORef : (IORef A) -> (IONew A)
  readIORef (MkIORef i) = readIORefPrim i

  writeIORef : (IORef A) -> A -> (IONew ())
  writeIORef (MkIORef i) val = writeIORefPrim i val

}


---------- Proofs ----------

ionew.EqualWR = proof
  intros
  refine Refl


ionew.EqualRR = proof
  intros
  refine Refl


ionew.EqualNRef = proof
  refine Refl


ionew.EqualUL = proof
  intros
  refine Refl


ionew.EqualL = proof
  intros
  refine Refl


ionew.EqualNL = proof
  intros
  refine Refl


ionew.EqualF = proof
  intros
  refine Refl


