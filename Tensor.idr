module Main

import Data.Vect
import Data.Fin
import NumericImplementations

import TensorProofs

%access public export
%default total

{-
GOAL WITH DROPS AND TAKES:
being able to select certain slices/rows/elements


Tensor product (join) doesn't seem to make sense:
does the tensor product sum the axes? If so, then what does it do when one tensor has two axis named the same?

products in einsum is just some variant of smart zipping

to sum just some of the axes, multidimensional slicing needs to be implemented


if tensortype is defined like it is right now (not a dataype), tensor creation becomes incredibly simple.
but everything else becomes harder?

Three ways to create tensor:
data Tensor : Vect n Nat -> Type -> Type where
    Scalar  : a -> Tensor [] a
    Tensor  : Vect d (Tensor ds a) -> Tensor (d :: ds) a

data Tensor : Vect n Nat -> Type -> Type where
    MkTensor : {n : Nat} -> {xs : Vect n Nat} -> TensorType xs a -> Tensor xs a

data Tensor : Vect n Nat -> Type -> Type where
    MkTensor : {dims : Vect n Nat} -> foldr Vect a dims -> Tensor dims a


-- the following doesn't work because the compiler can't pattern match on zipWith
dropTensor : {n : Nat} ->
              {ms : Vect n Nat} ->
              (ns : Vect n Nat) ->
              TensorType (zipWith (+) ns ms) a ->
              TensorType ms a
dropTensor {ms = []} [] t = t
dropTensor {ms = (m :: ms)} (x :: xs) t = map (dropTensor {ms=ms} xs) $ drop {m=m} x t


-}



TensorType : Vect rank Nat -> Type -> Type
TensorType []        a = a
TensorType (m :: ms) a = Vect m (TensorType ms a)

data Tensor : Vect rank Nat -> Type -> Type where
    TZ : a -> Tensor [] a
    TS : Vect d (Tensor ds a) -> Tensor (d :: ds) a

Functor (Tensor xs) where
    map f (TZ x) = TZ (f x)
    map f (TS xs) = TS (map (map f) xs)

Foldable (Tensor xs) where
    foldr f n (TZ y) = f y n
    foldr f n (TS ys) = foldr (flip (foldr f)) n ys

Show a => Show (Tensor xs a) where
    show (TZ x) = show x
    show (TS xs) = show xs ++ "\n"

zipWith : (a -> b -> c) -> Tensor ns a -> Tensor ns b -> Tensor ns c
zipWith f (TZ x) (TZ y) = TZ (f x y)
zipWith f (TS xs) (TS ys) = TS $ Vect.zipWith (zipWith f) xs ys

infixr 5 &&&

-- since idris' (&&) is lazy by default and it doesn't fit the type
(&&&) : Bool -> Bool -> Bool
(&&&) True x  = x
(&&&) False _ = False

Eq a => Eq (Tensor xs a) where
    (==) a = foldr (&&&) True . zipWith ((==)) a


replicate : {xs : Vect n Nat} -> a -> Tensor xs a
replicate {xs = []} x = TZ x
replicate {xs = (y :: ys)} x = TS (Vect.replicate y (replicate {xs=ys} x))

Num a => Num (Tensor xs a) where
    (+) = zipWith (+)
    (*) = zipWith (*)
    fromInteger {xs} x = replicate {xs=xs} (fromInteger x)

tensorFold : Monoid m => {n : Nat} -> {xs : Vect n Nat}
    -> (a -> m) -> Tensor xs a -> m
tensorFold f (TZ x) = f x
tensorFold f (TS xs) = concatMap (tensorFold f) xs


--fmap' : (a -> b) -> Tensor xs a -> Tensor xs b
--fmap' f = foldr ?ff ?nn

tensorSum : (Monoid a, Num a) => Tensor xs a -> a
tensorSum = concatMap {m=a} id

infixl 5 ><

(><) : Num a => {xs : Vect n Nat} -> {ys : Vect m Nat}
-> Tensor xs a -> Tensor ys a -> Tensor (xs ++ ys) a
(TZ x) >< b = (x*) <$> b
(TS xs) >< b = TS $ (>< b) <$> xs

--this is fmap (*a)?
--scalarMul : Num a => a -> Tensor xs a -> Tensor xs a
--scalarMul a t = ?scalarMul_rhs

{-
weakenList : {len : Nat} -> Vect len (Fin n) -> Vect len (Fin (n + len))
weakenList {len} xs = weakenN len <$> xs

-- like range, except it adds those values to already an existing vector
range' : Vect len (Fin (S n)) -> Vect len (Fin (S n))
range' [] = []
range' (x :: xs) = x :: (succ <$> range' xs)



-- plusInverseMinus : (n : Nat) -> (m : Nat) -> {auto smaller: LTE n m} -> m = plus n (m - n)
-- plusInverseMinus n m = ?plusMinusSmaller_rhs

-- weakenTo : {n : Nat} -> (m : Nat) -> (Fin n) -> {auto smaller: LTE n m} -> Fin m
-- weakenTo {n} m x = rewrite plusInverseMinus n m in weakenN (m - n) x

---- Tensor range
--range : {rank : Nat} -> {xs : Vect (S rank) Nat} -> Tensor xs (Fin (product xs))
--range {rank = Z} {xs = (y :: [])} = rewrite multOneRightNeutral y
--                                    in (TS (TZ <$> Vect.range {len=y}))
--range {rank = (S k)} {xs = (y :: ys)} = let other = range {rank=k} {xs=ys}
--                                            otherWeakened = weakenTo ((product ys) * y) <$> other
--                                        in ?range_rhs_1


{-
Type mismatch between
Fin (n + (m - n)) (Type of weakenN (m - n) x)
and
Fin m (Expected type)

Specifically:
Type mismatch between
plus n (m - n)
and
m
-}

-}

fromArray : {xs : Vect n Nat} -> TensorType xs a -> Tensor xs a
fromArray {xs = []} y = TZ y
fromArray {xs = (_ :: _)} y = TS (fromArray <$> y)

toArray : {xs : Vect n Nat} -> Tensor xs a -> TensorType xs a
toArray (TZ x) = x
toArray (TS xs) = toArray <$> xs

ConcatType : TensorType (x :: xs) a -> TensorType (y :: xs) a
    -> TensorType ((x + y) :: xs) a
ConcatType [] ys = ys
ConcatType (x :: xs) ys = x :: ConcatType xs ys

Concat : Tensor (x :: xs) a -> Tensor (y :: xs) a -> Tensor ((x + y) :: xs) a
Concat (TS xs) (TS ys) = TS (xs ++ ys)

{-
data Index2 : Vect n Nat -> Type where
    Nil  : Index2 []
    (::) : Fin (S m) -> Index2 ms -> Index2 (m :: ms)

takeSize : {ms : Vect n Nat} -> Index2 ms -> Vect n Nat
takeSize {ms = []} Nil = []
takeSize {ms = (n :: ns)} (x :: xs) = (finToNat x) :: takeSize {ms=ns} xs

dropSize : {ms : Vect n Nat} -> Index2 ms -> Vect n Nat
dropSize {ms = []} [] = []
dropSize {ms= (x :: xs)} (m :: ms) = ((-) {smaller=smallerThanBound m} x (finToNat m)) :: dropSize {ms=xs} ms

takeTensor : {xs : Vect n Nat} ->
    (inds : Index2 xs) -> Tensor xs a -> Tensor (takeSize {ms=xs} inds) a
takeTensor {xs = []} Nil (TZ x) = TZ x
takeTensor {xs = (m :: ms)} (d :: ds) (TS ys) = TS $ (takeTensor ds) <$>
    Vect.take {m=(-) {smaller=smallerThanBound d} m (finToNat d)} (finToNat d) (rewrite SfinPlusMinus d in ys)

dropTensor : {xs : Vect rank Nat} ->
    (inds : Index2 xs) -> Tensor xs a -> Tensor (dropSize {ms=xs} inds) a
dropTensor {xs = []} [] (TZ x) = TZ x
dropTensor {xs = (m :: ms)} (d :: ds) (TS ys) = TS $ (dropTensor {xs=ms} ds) <$>
    Vect.drop (finToNat d) (rewrite extfinPlusMinus d in ys)

--dropTakeTensor : {xs : Vect n Nat} ->
--    (dropInds : Index2 xs) ->
--    (takeInds : Index2 (dropSize {ms=xs} dropInds)) ->
--    Tensor xs a ->
--    Tensor (takeSize {ms=(dropSize {ms=xs} dropInds)} takeInds) a
--dropTakeTensor dropInds takeInds = takeTensor takeInds . dropTensor dropInds


{-
CONTINUATION of the comment on top:
we need to sum tensor axes.
We can do it in a way where we reduce the rank of the tensor by 1 or we keep the tensor rank intact


"bij,bjk->bik" can be done in a few steps:
bij   bjk
bji   bjk

1. "bij,bjk->bijk"
2. "bijk->bik"


Other:
1. for "bij" I can create "bj" "i" tensors. For "bjk" I can create "bj" "k" tensors
1. "bijbjk"
2. "bijk" (tensor product )
3. "bi1k" (sum along the axis)
4. "bik" (remove the unit axis)

-}

vectorOuterProduct : Num a => Vect n a -> Vect m a -> Vect n (Vect m a)
vectorOuterProduct [] b = []
vectorOuterProduct (x :: xs) b = ((x*) <$> b) :: vectorOuterProduct xs b

--sumAxisSize : (xs : Vect rank Nat) -> (i : Fin rank) -> {auto smaller: LTE 1 rank} -> Vect (rank - 1) Nat
--sumAxisSize {rank = (S Z)} (_ :: ms) FZ = ms
--sumAxisSize {rank = (S (S k))} (_ :: ms) FZ = ms
--sumAxisSize {rank = (S (S k))} (m :: ms) (FS i) = m :: rewrite sym $ minusZeroRight k in sumAxisSize ms i

sumAxisSize : (xs : Vect rank Nat) -> (i : Fin rank) -> Vect rank Nat
sumAxisSize (_ :: ms) FZ = 1 :: ms
sumAxisSize (m :: ms) (FS i) = m :: sumAxisSize ms i

--sumAxis : {rank : Nat} -> {xs : Vect rank Nat} -> Tensor xs a -> (i : Fin rank) -> {auto smaller: LTE 1 rank} -> Tensor (sumAxisSize xs i) a
--sumAxis t i = ?sumAxis_rhs

--allSliceIndexes : {rank : Nat} -> {xs : Vect rank Nat} -> Tensor xs a -> (i : Fin rank) -> {auto smaller: LTE 1 rank} -> Vect (index i xs) (Vect rank Nat)
--allSliceIndexes {rank = (S k)} _ i =
--    map (\j => insertAt i (finToNat j) (replicate k Z)) range

-- c : {ys : Vect n Nat} -> (xs : Vect n Nat) -> Index2 ys
-- c {ys = []} [] = []
-- c {ys = (y :: ys)} (x :: xs) = (myNatToFin (S y) x) :: c {ys} xs

zeroIndex2 : {xs : Vect n Nat} -> Index2 xs
zeroIndex2 {xs = []} = []
zeroIndex2 {xs = (_ :: _)} = FZ :: zeroIndex2

--reshape : {xs : Vect n Nat} -> Vect m a -> {auto SUM: (sum xs) = m} -> Tensor xs a
--reshape {xs = []} [] = TZ ?reshape_rhs_5
--reshape {xs = []} (x :: xs) = ?reshape_rhs_4
--reshape {xs = (x :: xs)} ms = ?reshape_rhs_2


-- WHY DO WE NEED ALL SLICES here?
-- to sum the tensor!
--allSliceIndexes : {rank : Nat} -> {xs : Vect rank Nat} -> Tensor xs a -> (i : Fin rank) -> {auto smaller: LTE 1 rank} -> Vect (index i xs) (Index2 xs)
--allSliceIndexes {rank = (S h)} {xs=xs} _ i = let e = replicate h Z
--                                                 --z = map (\j => insertAt i (finToNat j) e) range
--                                             in ?zzzz

-- allSlices : {rank : Nat} -> Tensor xs a -> (i : Fin rank) -> List (Tensor (sumAxisSize xs i) a)
-- allSlices {rank} {xs} x i = let rr = allSliceIndexes x i
--                                 ii = the (Index2 xs) (fromList rr)
--                                 -- mm = map (flip dropTensor x) ii
--                             in ?as

matMul : Tensor [j, i] Double -> Tensor [j, k] Double -> Tensor [i, k] Double
matMul x y = let p = x >< y in ?matMul_rhs



-- how does partial function application work here?
--dropTakeTensor : {xs : Vect rank Nat} ->
--    (v : (dropInds : Index2 xs ** (tak : Index2 (dropSize {ms=xs} dropInds)))) ->
--    Tensor xs a ->
--    (Tensor (takeSize {ms=(dropSize {ms=xs} dropInds)} (snd v)) a)
--dropTakeTensor dropInds takeInds = takeTensor takeInds . dropTensor dropInds

--tt : Tensor [1, 2] Double
--tt = dropTakeTensor [2, 2] [1, 2] t


sliceVect : (n : Nat) -> (m : Nat) -> Vect (n + m + p) a -> Vect m a
sliceVect n m {p} = rewrite sym $ plusAssociative n m p in take m . drop n


namespace I
    -- machinery for indexing arbitrary tensors
    data Index : Vect n Nat -> Type where
        Nil  : Index []
        (::) : Fin m -> Index ms -> Index (m :: ms)

index : Index ms -> Tensor ms a -> a
index [] (TZ x) = x
index (x :: xs) (TS ys) = index xs $ Vect.index x ys

esindex : Vect n Char -> Vect n Nat -> (p : Nat ** Vect p (Char, Nat))
esindex cs ns = let nubcs = nubBy (\a, b => fst a == fst b) $ zip cs ns
                in nubcs

{-

--index : Index ms -> TensorType ms a -> a
--index [] a = a
--index (x :: xs) a = index xs $ Vect.index x a

--einsum : {ns : Vect n Nat}
--    -> {ms : Vect m Nat}
--    -> Vect n Char
--    -> Vect m Char
--    -> {auto prf: LTE m n}
--    -> TensorType ns a
--    -> TensorType ms a
--einsum is os x = let free = filter (`elem` os) is
--                     summ = filter (not . (`elem` os)) is
--                 in ?test

--data Slice : Vect n (Nat, Nat) -> Type where
--    SNil  : Slice []
--    SCons : (n : Nat, m : Nat) -> Slice ms -> Slice ((n, m) :: ms)
--


-}
-}
