module Examples

import Data.Vect
import Data.Fin

import Tensor
import NumericImplementations
--import Einsum

%default total

b : Tensor [3] Bool
b = fromArray $ [True, False, True]

t1 : Tensor [3] Double
t1 = fromArray $ [0, 1, 2]

t2 : Tensor [2] Double
t2 = fromArray $ [10, 20]

t' : TensorType [3, 4] Double
t' = [ [0, 1, 2, 3]
     , [4, 5, 6, 7]
     , [8, 9, 10, 11]]


s : Tensor [3, 3] Double
s = fromArray $ [ [0, 1, 2]
                , [3, 4, 5]
                , [6, 7, 8]]

t : Tensor [3, 4] Double
t = fromArray t'

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
