module Examples

import Data.Vect
import Data.Fin

import Tensor
import NumericImplementations
--import Einsum

%access public export
%default total


Array : Vect rank Nat -> Type -> Type
Array []        a = a
Array (m :: ms) a = Vect m (Array ms a)

fromArray : {xs : Vect rank Nat} -> Array xs a -> Tensor xs a
fromArray {xs = []} y = TZ y
fromArray {xs = (_ :: _)} y = TS (fromArray <$> y)

toArray : {xs : Vect n Nat} -> Tensor xs a -> Array xs a
toArray (TZ x) = x
toArray (TS xs) = toArray <$> xs

t' : Array [3, 4] Double
t' = [ [0, 1, 2, 3]
     , [4, 5, 6, 7]
     , [8, 9, 10, 11]]

a : Tensor' [2, 3] Double
a = fromArray $ [ [10, 11, 12]
                , [100, 110, 120]]

b : Tensor' [3, 4] Double
b = fromArray t'

--c1 : Tensor ['i', 'j'] Double
--c2 : Tensor ['j', 'k'] Double

s : Tensor' [3, 3] Double
s = fromArray $ [ [0, 1, 2]
                , [3, 4, 5]
                , [6, 7, 8]]


{-
t'' : TensorType [3, 4] Double
t'' = toArray t


w' : TensorType [2, 3, 4] Double
w' = [[[1, 2, 3, 4],
     [5, 6, 7, 8],
     [9, 10, 11, 12]],
     [[13, 14, 15, 16],
     [17, 18, 19, 20],
     [21, 22, 23, 24]]]

w : Tensor [2, 3, 4] Double
w = fromArray w'

{-
w1 : Tensor [2, 1, 4] Double
w1 = takeTensor [2, 1, 4] $ dropTensor [0, 0, 0] w

w2 : Tensor [2, 1, 4] Double
w2 = takeTensor [2, 1, 4] $ dropTensor [0, 1, 0] w

w3 : Tensor [2, 1, 4] Double
w3 = takeTensor [2, 1, 4] $ dropTensor [0, 2, 0] w




r1 : Tensor [1, 4] Double
r1 = takeTensor [1, 4] $ dropTensor [0, 0] t

r2 : Tensor [1, 4] Double
r2 = takeTensor [1, 4] $ dropTensor [1, 0] t

r3 : Tensor [1, 4] Double
r3 = takeTensor [1, 4] $ dropTensor [2, 0] t

-}

-}
