module Misc

import Data.Vect

%access export
%default total

equating : Eq b => (a -> b) -> a -> a -> Bool
equating f x y = f x == f y

weakenList : {len : Nat} -> Vect len (Fin n) -> Vect len (Fin (n + len))
weakenList {len} xs = weakenN len <$> xs
