module matrixcomplete

--vect Data Type--
data Vect: Nat -> Type -> Type where
	Nil : Vect Z a
	(::): a -> Vect k a -> Vect (S k) a

--Concatenate two vects--
(++) : Vect n a -> Vect m a -> Vect (n + m) a
(++) Nil ys = ys
(++) (x :: xs) ys = x :: xs ++ ys

--Adapted from the List zipWith Function-- 
zipWith : (a -> b -> c) -> Vect n a -> Vect n b -> Vect n c
zipWith f []      []      = []
zipWith f (x::xs) (y::ys) = f x y :: zipWith f xs ys

--Adapted from the List map function--
map : (a -> b) -> Vect n a-> Vect n b 
map f Nil        = Nil
map f (x::xs) = f x :: map f xs

--Adds two vects of the same length--
VecAdd : Num a => {n:Nat}-> Vect n a -> Vect n a -> Vect n a
VecAdd Nil Nil = Nil
VecAdd (x :: xs) (y :: ys) = (x + y) :: (VecAdd xs ys)

--Subtracts two vects of the same length--
VecSub : Num a => {n:Nat}->Vect n a -> Vect n a -> Vect n a
VecSub Nil Nil = Nil
VecSub (x :: xs) (y :: ys) = x - y :: VecSub xs ys

--Returns the first element of a vect. Vect must have at least one element--
VecHead : {n:Nat}->Vect (S n) a -> a
VecHead (x::xs) = x

--Returns the last element of a vect. Vect must have at least one element--
VecTail : {n:Nat}->Vect (S n) a -> a
VecTail (x::Nil) = x
VecTail (x::y::xs) = VecTail (y::xs)

--Performs scalar multiplication (dot product) on two vectors of the same length--
ScalMult : Num a => Vect n a -> Vect n a -> a
ScalMult Nil Nil = 0
ScalMult (x::xs) (y::ys) = x*y + (ScalMult xs ys)

--Computes the cross product of two 3 x 3 vectors--
CrossProduct: Num a => Vect (S (S (S Z))) a -> Vect (S (S (S Z))) a -> Vect (S (S (S Z))) a
CrossProduct [u1, u2, u3] [v1, v2, v3] = [u2*v3-u3*v2,u3*v1-u1*v3,u1*v2-u2*v1]

--Multiplies a vector times a scalar--
VectXScal : Num a => Vect n a -> a -> Vect n a
VectXScal Nil a = Nil 
VectXScal (v::vs) s = (v*s::(VectXScal vs s))

--Defines a Matrix datatype--
Matrix : Nat->Nat->Type->Type 
Matrix n m a = Vect n (Vect m a) 

--Adds two matrixes of the same dimensions together--
MatAdd : Num a => Matrix n m a -> Matrix n m a -> Matrix n m a
MatAdd Nil Nil = Nil
MatAdd (m1::m) (m2::n) = (VecAdd m1 m2)::(MatAdd m n)

--Subtracts two matrixes of the same dimensions--
MatSub: Num a => Matrix n m a -> Matrix n m a -> Matrix n m a
MatSub Nil Nil = Nil
MatSub (m1::m) (m2::n) = (VecSub m1 m2)::(MatSub m n)

--Makes n copies of type--
repeat : (n : Nat) -> a -> Vect n a
repeat Z _ = []
repeat (S k) x = x :: repeat k x

--Computes the transpose of a matrix--
MatTrans : Matrix n m a -> Matrix m n a
MatTrans [] = repeat _ []
MatTrans (r :: rs) = zipWith (::) r (MatTrans rs)

--Multiplies a matrix by a vector of the appropriate length--
MatrixVectMult : (Num a) => Vect j a -> Matrix k j a -> Vect k a
MatrixVectMult v m = zipWith ScalMult m (repeat _ v)

--Performs matrix multiplication--
MatMult : (Num a) => Matrix i j a-> Matrix j k a-> Matrix i k a
MatMult m n = zipWith MatrixVectMult m (repeat _ n')
    where n' = MatTrans n
         