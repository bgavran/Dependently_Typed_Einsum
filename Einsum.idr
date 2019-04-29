module Einsum

import Data.Vect
import Data.SortedMap

import NumericImplementations
import Tensor
import Examples
import Misc

%access export
%default total

data CharFormat
    = ESChar Char CharFormat
    | ESComma CharFormat
    | ESArrow CharFormat
    | ESEnd

format : List Char -> CharFormat
format (','::cs) = ESComma (format cs)
format ('-'::'>'::cs) = ESArrow (format cs)
format (c::cs) = ESChar c (format cs)
format [] = ESEnd

data Format
    = InputTensor (Vect n Char) Format
    | OutputTensor (Vect n Char)

-- Vect n Char is the accumulator for tensor indices
fformat : Vect n Char -> CharFormat -> Format
fformat xs (ESChar c f) = fformat (c::xs) f
fformat xs (ESComma f) = InputTensor (reverse xs) $ fformat [] f
fformat xs (ESArrow f) = InputTensor (reverse xs) $ fformat [] f
fformat xs ESEnd = OutputTensor (reverse xs)

interpFormat : Type -> Format -> Type
interpFormat a (InputTensor xs f) = Tensor xs a -> interpFormat a f
interpFormat a (OutputTensor xs) = Tensor xs a

formatString : String -> Format
formatString = fformat [] . format . unpack


einsumType : Type -> String -> Type
einsumType a = interpFormat a . formatString

--einsum : (s : String) -> einsumType a s
--einsum s = let ast = formatString s
--           in ?einsum_rhs

{-
"iij" "ij""
[2, 2, 3]
[2, 3]


"iij" "ji""
[2, 2, 3]
[3, 2]

--------------------

"ij" "j"
[2, 3]
[3]

--------------------

"ij" "i""
[2, 3]
[2]
-}
{-
no repeated indices
-}

insertCharNatIntoDict : Char -> Nat -> SortedMap Char Nat -> Maybe (SortedMap Char Nat)
insertCharNatIntoDict k v dct = case (lookup k dct) of
    Nothing => Just $ insert k v dct
    Just val => case (v == val) of
        True => Just dct
        False => Nothing

insertIntoDict' : (cs : Vect rank Char) -> (xs : Vect rank Nat) -> SortedMap Char Nat -> Maybe (SortedMap Char Nat)
insertIntoDict' [] [] dct = Just dct
insertIntoDict' (c :: cs) (x :: xs) dct = insertCharNatIntoDict c x dct >>= insertIntoDict' cs xs

-- | Inserts a list of tensor names and their sizes into the corresponding dictionary
-- Fails if there are inconsistencies with the dimension names
-- "iij" [2, 4, 5] will fail
insertIntoDict : (cs : Vect rank Char) -> (xs : Vect rank Nat) -> Maybe (SortedMap Char Nat)
insertIntoDict cs xs = insertIntoDict' cs xs empty

-- | Two ways this can fail:
-- a) there's a repeated dimension name
-- b) new index names aren't in the map
newTensorSize : Vect rank Char -> SortedMap Char Nat -> Maybe (Vect rank Nat)
newTensorSize xs dct = case equating length (nub $ toList xs) (toList xs) of
    False => Nothing
    True => sequence $ flip lookup dct <$> xs


--newTensor : Vect rank Char -> SortedMap Char Nat -> Maybe (Tensor xs a)
--newTensor xs dct = let zz = newTensorSize xs dct in ?newTensor_rhs

contractSpecificAxes : Monoid a
    => {c's : Vect rank Nat} -> {t's : Vect newRank Nat}
    -> (cs : Vect rank Char) -> (ts : Vect newRank Char) -- incoming and outgoing names
    -> {auto smaller: newRank `LTE` rank}
    -> Tensor' c's a         -> Tensor' t's a -- incoming and result tensor
contractSpecificAxes {c's} {t's = []} cs res t = TZ $ concat t
contractSpecificAxes {c's} {t's = ys} cs res t =
    let tDct = insertIntoDict cs c's
        mT's = tDct >>= newTensorSize res
        t's' = fromMaybe ys mT's
    in ?contractSpecificAxes_rhs_1


-- | cs holds names for each axis in the accumulating tensor
-- t is the accumulating tensor?
-- we need to manually keep track of axis names and stuff?
toFunction : Num a => {ys : Vect rank Nat}
    -> (fmt : Format) -> (Vect rank Char, Tensor' ys a) -> interpFormat a fmt
toFunction (InputTensor xs f) (cs, t) = \i => toFunction f (cs, ?toFunction_rhs_1)
toFunction (OutputTensor xs) (cs, t) = ?toFunction_rhs_2


