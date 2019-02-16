module Einsum

import Data.Vect

import Tensor

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
    = FTensor (Vect n Char) Format
    | Arrow (Vect n Char)

fformat : Vect n Char -> CharFormat -> Format
fformat xs (ESChar c f) = fformat (c::xs) f
fformat xs (ESComma f) = FTensor (reverse xs) $ fformat [] f
fformat xs (ESArrow f) = FTensor (reverse xs) $ fformat [] f
fformat xs ESEnd = Arrow (reverse xs)


ff : Type
ff = (i : Nat) -> Tensor [i, 3] Double

ee : Type
ee = (i : Nat) -> (j : Nat) -> Tensor (the (Vect 2 Nat) [i, j]) Double

gen' : Vect m Nat -> Vect n Char -> Type -> Type
gen' ys [] a = Tensor ys a
gen' ys (x :: xs) a = {i : Nat} -> gen' (i::ys) xs a

gen : Vect n Char -> Type -> Type
gen = gen' []

interpFormat : Format -> Type -> Type
interpFormat (FTensor xs f) a = gen xs a -> interpFormat f a
interpFormat (Arrow xs) a = gen xs a

formatString : String -> Format
formatString = fformat [] . format . unpack

--toFunction : (fmt : Format) -> interpFormat fmt Double
--toFunction (FTensor xs x) = ?toFunction_rhs_1
--toFunction (Arrow xs) = ?toFunction_rhs_2

einsum : (s : String) -> interpFormat (formatString s) a
einsum s = let f = formatString s
           in ?einsum_rhs
