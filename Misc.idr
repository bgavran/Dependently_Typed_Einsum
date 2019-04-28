module Misc

import Data.Vect
--import Data.Matrix.Algebraic

%access export
%default total

equating : Eq b => (a -> b) -> a -> a -> Bool
equating f x y = f x == f y

weakenList : {len : Nat} -> Vect len (Fin n) -> Vect len (Fin (n + len))
weakenList {len} xs = weakenN len <$> xs


bb : Vect 2 Int
bb = [1, 2]

cc : Vect 2 Int
cc = [10, 20]

dd : List Int
dd = [1, 2, 3, 4]

--Ex3 : (String, String)
--Ex3 = ("Hello",2) & _2 .~ "World!"
--
--d : Maybe Int
--d = dd ^? ix 1

--Ixed (Vect n a) where
--  IxInd = Nat
--  IxVal = a
--  ix k (Mor f) = Mor (\xs0 => go xs0 k)
--      where
--          go a b = ?asdf

--go : (f : Type -> Type) -> Vect n a -> f (Vect n a)
--go f xs = ?go_rhs

--implementation Ixed (List a) where
--    IxInd = Nat
--    IxVal = a
--    ix k (Mor f) = Mor (\xs0 => go xs0 k)
--      where
--        go Nil _           = pure Nil
--        go (a :: as) Z     = (:: as) <$> (f a)
--        go (a :: as) (S n) = (a ::)  <$> (go as n)

