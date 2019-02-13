module Control.Algebra.NumericImplementations

%access public export

-- Integer

Semigroup Integer where
  (<+>) = (+)

Monoid Integer where
  neutral = 0

-- Int

Semigroup Int where
  (<+>) = (+)

Monoid Int where
  neutral = 0

-- Double

Semigroup Double where
  (<+>) = (+)

Monoid Double where
  neutral = 0
