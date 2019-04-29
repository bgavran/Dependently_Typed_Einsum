module Tensor

import Data.Vect
import Data.Fin
import Data.SortedMap
import NumericImplementations

import TensorProofs

%access public export
%default total

{-
There's several goals here:
* Implementation of just np.einsum from Python
* Implementation of generic tensor indexing, slicing setting and getting functionality
    * Lenses seem like they might be useful here
    * Zippers also - products in einsum seem just like some variant of smart zippers

Rudimenatary dropping and taking of tensors are implemented. THe ida is to use that functionality for implementing slicing

Tensor product (join) doesn't seem to make sense:
does the tensor product sum the axes? If so, then what does it do when one tensor has two axis named the same?

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

data Tensor : {t : Type} -> Vect rank t -> Type -> Type where
    TZ : a -> Tensor [] a
    TS : Vect d (Tensor ds a) -> Tensor (d :: ds) a

-- specialization to Nat
Tensor' : Vect rank Nat -> Type -> Type
Tensor' = Tensor

record Tensor2 (mcs : SortedMap Char Nat) (a : Type) where
    constructor MkTensor
    tensor2 : Tensor' (fromList $ values mcs) a

    --i : keys mcs ->

--index2 : (Char, Fin s) -> Tensor2 ms a -> Tensor ns a
--index2 (a, b) y = ?index2_rhs_1

-- machinery for indexing tensors
data Index : Vect n Nat -> Type where
    Nil  : Index []
    (::) : Fin m -> Index ms -> Index (m :: ms)

index' : Fin len -> Tensor' (len :: ls) a -> Tensor' ls a
index' l (TS xs) = Vect.index l xs

--map' : Functor f => Fin len -> (a -> b) -> f a -

index : Index ms -> Tensor' ms a -> a
index [] (TZ x) = x
index (x :: xs) t = index xs $ index' x t

--f : (xs : Vect (S n) Nat) -> (i : Fin (S n)) -> Fin (index i xs) -> Nat
--f _ i x = (finToNat i) + (finToNat x)


-- | [2, 3, 5] [1, 0, 2]
--permuteAxes : {xs : Vect rank Nat}
--    -> Tensor xs a ->
--    -> (ys : Vect rank Nat)
--    ->

Functor (Tensor xs) where
    map f (TZ x) = TZ (f x)
    map f (TS xs) = TS (map (map f) xs)

--tensorFold : Monoid m => {n : Nat} -> {xs : Vect n Nat}
--    -> (a -> m) -> Tensor xs a -> m
--tensorFold f (TZ x) = f x
--tensorFold f (TS xs) = concatMap (tensorFold f) xs

Foldable (Tensor xs) where
    foldr f n (TZ y) = f y n
    foldr f n (TS ys) = foldr (flip (foldr f)) n ys

Show a => Show (Tensor xs a) where
    show (TZ x) = show x
    show (TS xs) = show xs ++ "\n"


zipWith : (a -> b -> c) -> Tensor ns a -> Tensor ns b -> Tensor ns c
zipWith f (TZ x) (TZ y) = TZ (f x y)
zipWith f (TS xs) (TS ys) = TS $ Vect.zipWith (zipWith f) xs ys

zip : Tensor xs a -> Tensor xs b -> Tensor xs (a, b)
zip = zipWith MkPair

Eq a => Eq (Tensor xs a) where
    x == y = all (uncurry (==)) $ zip x y

replicate : {xs : Vect n Nat} -> a -> Tensor xs a
replicate {xs = []} x = TZ x
replicate {xs = (y :: ys)} x = TS $ Vect.replicate y (replicate {xs=ys} x)

Semigroup a => Semigroup (Tensor xs a) where
    (<+>) = zipWith (<+>)

Monoid a => Monoid (Tensor' xs a) where
    neutral = replicate neutral

Num a => Num (Tensor' xs a) where
    (+) = zipWith (+)
    (*) = zipWith (*)
    {-
    fromInteger actually involves creating a Tensor. The only tensors we can create are
    the ones with Nat as their dimension element type
    Since it involves creating a Tensor, we need to have Nat in the type and that means
    we have can't use a general Tensor xs a, but that we need to use Tensor' xs a
    -}
    fromInteger = replicate . fromInteger

dropNthElement : Fin (S k) -> Vect (S k) Nat -> Vect k Nat
dropNthElement FZ (_ :: xs) = xs
dropNthElement {k = S l} (FS i) (x :: xs) = x :: dropNthElement i xs

indexNthLevel : {xs : Vect (S r) Nat}
    -> (e : Fin (S r)) -> Fin (index e xs) -> Tensor xs a -> Tensor (dropNthElement e xs) a
indexNthLevel FZ i (TS ys) = index i ys
indexNthLevel {r = S k} (FS later) i (TS ys) = TS $ indexNthLevel later i <$> ys

-- same as above except its using Idris' (Elem x xs) functionality
indexNthLevel' : {xs : Vect (S r) Nat}
    -> (e : Elem x xs) -> Fin x -> Tensor xs a -> Tensor (dropElem xs e) a
indexNthLevel' Here i (TS ys) = index i ys
indexNthLevel' {r = S k} (There later) i (TS ys) = TS $ indexNthLevel' later i <$> ys


contractSpecificAxis : Monoid a => {xs : Vect (S r) Nat}
    -> (e : Fin (S r)) -> Tensor xs a -> Tensor (dropNthElement e xs) a
contractSpecificAxis {xs} e ys = Foldable.concat $ (\i => indexNthLevel e i ys) <$> range {len=index e xs}

infixl 5 ><

-- | Tensor product
(><) : Num a
    => {xs : Vect n Nat} -> {ys : Vect m Nat}
    -> Tensor xs a -> Tensor ys a -> Tensor (xs ++ ys) a
(TZ x) >< b = (x*) <$> b
(TS xs) >< b = TS $ (>< b) <$> xs

-- like range, except it adds those values to already an existing vector
range' : Vect len (Fin (S n)) -> Vect len (Fin (S n))
range' [] = []
range' (x :: xs) = x :: (succ <$> range' xs)



{-
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

Concat : {x : Nat}
    -> Tensor (x :: xs) a -> Tensor (y :: xs) a -> Tensor ((x + y) :: xs) a
Concat (TS xs) (TS ys) = TS (xs ++ ys)

namespace I
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


{-
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
-}

vectorOuterProduct : Num a => Vect n a -> Vect m a -> Vect n (Vect m a)
vectorOuterProduct [] b = []
vectorOuterProduct (x :: xs) b = ((x*) <$> b) :: vectorOuterProduct xs b

sumAxisSize : (i : Fin (S r)) -> (xs : Vect (S r) Nat) -> Vect r Nat
sumAxisSize FZ (_ :: xs) = xs
sumAxisSize (FS FZ) (x :: xs) = x :: sumAxisSize FZ xs
sumAxisSize (FS (FS i)) (x :: xs) = x :: sumAxisSize (FS i) xs

sumAxis : Monoid a
    => {xs : Vect (S r) Nat}
    -> (i : Fin (S r))
    -> Tensor xs a
    -> Tensor (sumAxisSize i xs) a
sumAxis FZ (TS xs) = concat xs
sumAxis (FS FZ) (TS xs) = TS (sumAxis FZ <$> xs)
sumAxis (FS (FS i)) (TS xs) = TS (sumAxis (FS i) <$> xs)

{-
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
-}

--
--esindex : Vect n Char -> Vect n Nat -> (p : Nat ** Vect p (Char, Nat))
--esindex cs ns = let nubcs = nubBy (\a, b => fst a == fst b) $ zip cs ns
--                in nubcs

{-

--index : Index ms -> TensorType ms a -> a
--index [] a = a
--index (x :: xs) a = index xs $ Vect.index x a

--data Slice : Vect n (Nat, Nat) -> Type where
--    SNil  : Slice []
--    SCons : (n : Nat, m : Nat) -> Slice ms -> Slice ((n, m) :: ms)
--


-}
