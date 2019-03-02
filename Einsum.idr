module Einsum

import Data.Vect

import NumericImplementations
import Tensor
import Examples

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


ff : Type
ff = (i : Nat) -> Tensor [i, 3] Double

ee : Type
ee = (i : Nat) -> (j : Nat) -> Tensor (the (Vect 2 Nat) [i, j]) Double

interpFormat : Type -> Format -> Type
interpFormat a (InputTensor xs f) = Tensor xs a -> interpFormat a f
interpFormat a (OutputTensor xs) = Tensor xs a

formatString : String -> Format
formatString = fformat [] . format . unpack


einsumType : Type -> String -> Type
einsumType a = interpFormat a . formatString

einsum : (s : String) -> einsumType a s
einsum s = let ast = formatString s
           in ?einsum_rhs

VectSubset : (xs : Vect n a) -> (ys : Vect m a) -> {auto smaller: m `LTE` n} -> Type

contractSpecificAxes : VectSubset xs ys => Tensor xs a -> Tensor ys a

toFunction : Num a => (fmt : Format) -> Tensor ys a -> interpFormat a fmt
toFunction (InputTensor xs y) t = ?toFunction_rhs_1
toFunction (OutputTensor xs) t = ?toFunction_rhs_2


--toFunction a (InputTensor xs f) t = \t' : gen xs a => let t'' = t' in ?asdf
--toFunction a (OutputTensor xs) t = let outTensor = gen xs a
--                                       zzz = the outTensor (contractSpecificAxes t)
--                                       in ?tttt
