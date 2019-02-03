module TensorProofs

import Data.Vect
import Data.Fin

%access export
%default total

||| Proof that natural number made from Fin (S m) is smaller than m
smallerThanBound : {x : Nat} -> (m : Fin (S x)) -> LTE (finToNat m) x
--smallerThanBound FZ = LTEZero
--smallerThanBound (FS x) = LTESucc (smallerThanBound x)
smallerThanBound {x = Z} FZ = LTEZero
smallerThanBound {x = (S k)} FZ = LTEZero
smallerThanBound {x = (S k)} (FS y) = LTESucc (smallerThanBound y)

-----------------------------------------

revFinPlusMinus : {m : Nat} -> (d : Fin m) -> plus (minus m (finToNat d)) (finToNat d) = m
revFinPlusMinus {m = (S k)} FZ = rewrite plusZeroRightNeutral k in Refl
revFinPlusMinus {m = (S k)} (FS x) =
    rewrite sym $ plusSuccRightSucc (minus k (finToNat x)) (finToNat x)
    in cong (revFinPlusMinus x)

||| Proof that some natural number m doesn't change when we subtract and then add another natural number smaller than m
finPlusMinus : {m : Nat} -> (d : Fin m) -> (finToNat d) + (minus m (finToNat d)) = m
finPlusMinus {m} d = rewrite plusCommutative (finToNat d) (minus m (finToNat d))
    in revFinPlusMinus d

SfinPlusMinus : {m : Nat} -> (d : Fin (S m)) -> (finToNat d) + (minus m (finToNat d)) = m
SfinPlusMinus {m = Z} FZ = Refl
SfinPlusMinus {m = (S k)} FZ = Refl
SfinPlusMinus {m = (S k)} (FS x) = let tt = SfinPlusMinus x in cong tt

extfinPlusMinus : {m : Nat} -> (d : Fin (S m)) -> (finToNat d) + (minus m (finToNat d)) = m
extfinPlusMinus {m = Z} FZ = Refl
extfinPlusMinus {m = (S k)} FZ = Refl
extfinPlusMinus {m = (S k)} (FS x) = cong $ extfinPlusMinus {m=k} x

myNatToFin : (n : Nat) -> (m : Nat) -> {auto p : n `GT` m} -> Fin n
myNatToFin (S n) Z = FZ
myNatToFin (S n) (S m) {p = LTESucc _} = FS $ myNatToFin n m
