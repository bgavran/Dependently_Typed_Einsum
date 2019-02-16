module Einsum

import Data.Vect

import Tensor

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

fformat : Vect n Char -> CharFormat -> Format
fformat xs (ESChar c f) = fformat (c::xs) f
fformat xs (ESComma f) = InputTensor (reverse xs) $ fformat [] f
fformat xs (ESArrow f) = InputTensor (reverse xs) $ fformat [] f
fformat xs ESEnd = OutputTensor (reverse xs)


ff : Type
ff = (i : Nat) -> Tensor [i, 3] Double

ee : Type
ee = (i : Nat) -> (j : Nat) -> Tensor (the (Vect 2 Nat) [i, j]) Double

gen' : Vect m Nat -> Vect n Char -> Type -> Type
gen' ys [] a = Tensor ys a
gen' ys (x :: xs) a = (i : Nat) -> gen' (i::ys) xs a

gen : Vect n Char -> Type -> Type
gen = gen' []

interpFormat : Format -> Type -> Type
interpFormat (InputTensor xs f) a = gen xs a -> interpFormat f a
interpFormat (OutputTensor xs) a = gen xs a

formatString : String -> Format
formatString = fformat [] . format . unpack

VectSubset : (xs : Vect n a) -> (ys : Vect m a) -> {auto smaller: m `LTE` n}-> Type

contractSpecificAxes : VectSubset xs ys => Tensor xs a -> Tensor ys a

--toFunction : Num a => (a : Type) -> (fmt : Format) -> Tensor ys a -> interpFormat fmt a
--toFunction a (InputTensor xs f) t = \t' : gen xs a => let t'' = t' in ?asdf
--toFunction a (OutputTensor xs) t = let outTensor = gen xs a
--                                       zzz = the outTensor (contractSpecificAxes t)
--                                       in ?tttt

--einsum : (s : String) -> interpFormat (formatString s) a
--einsum s = let f = formatString s
--           in ?einsum_rhs
