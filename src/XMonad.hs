{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}

module XMonad where

infixl 4 <*>:

class (forall i j. Functor (f i j)) => XApplicative f where
  xpure :: a -> f i i a
  (<*>:) :: f i j (a -> b) -> f j k a -> f i k b
  (<*>:) = liftX2 id
  liftX2 :: (a -> b -> c) -> f i j a -> f j k b -> f i k c
  liftX2 f x y = f <$> x <*>: y

-- Identity
-- > xpure id <*>: v = v
--
-- Composition
-- > xpure (.) <*>: u <*>: v <*>: w = u <*>: (v <*>: w)
--
-- Homomorphism
-- xpure f <*>: xpure x = xpure (f x)
--
-- Interchange
-- u <*>: xpure y = xpure ($ y) <*>: u

infixl 1 >>=:, >>:

class XApplicative m => XMonad m where
  xreturn :: a -> m i i a
  xreturn = xpure
  (>>=:) :: m i j a -> (a -> m j k b) -> m i k b
  (>>:) :: m i j a -> m j k b -> m i k b
  m >>: k = m >>=: \_ -> k

(>=>:) :: XMonad m => (a -> m i j b) -> (b -> m j k c) -> (a -> m i k c)
f >=>: g = \x -> f x >>=: g

-- Left identity
-- > xreturn a >>=: k = k a
--
-- Right identity
-- > m >>=: xreturn = m
--
-- Associativity
-- > m >>=: (\x -> k x >>=: h) = (m >>=: k) >>=: h
-- > m >=>: (k >=>: h) = (m >=>: k) >=>: h
--
-- XMonad and XApplicative relation
-- > mf <*>: m = mf >>=: (\f -> m >>=: (\x -> xreturn (f x)))
