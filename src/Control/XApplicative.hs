{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}

-- |
-- Module : Control.XApplicative
-- Copyright : (c) Evgeny Poberezkin
-- License : BSD3
--
-- Maintainer  : evgeny@poberezkin.com
-- Stability   : experimental
-- Portability : non-portable
--
-- This module describes an intermediate type class between
-- a functor and an indexed monad 'XMonad' - an indexed applicative.
--
-- Types that can be made instances of this class must have two type parameters/indexes
-- that must continually chain in threaded computations (see type signature for '<*>:').
module Control.XApplicative
  ( -- * XApplicative
    XApplicative (..),

    -- ** Functions
    (<**>:),
    xliftA,
    xliftA3,
  )
where

infixl 4 <*>:, <*:, *>:, <**>:

-- | A poly-kinded type-parameterized (indexed) functor with application, with operations to
--
-- * embed pure expressions ('xpure'), and
-- * sequence computations and combine their results ('<*>:' and 'xliftA2').
--
-- These functors have kind @r -> r -> Type -> Type@, where the kind equality
-- of the of the first and the second type parameters is implied from chaining.
--
-- A minimal complete definition must include implementations of 'xpure'
-- and of either '<*>:' or 'xliftA2'. If it defines both, then they must behave
-- the same as their default definitions:
--
--      @('<*>:') = 'xliftA2' 'id'@
--
--      @'liftA2' f x y = f 'Prelude.<$>' x '<*>:' y@
--
-- The definition must satisfy the same laws as 'Applicative':
--
-- [Identity]
--
--      @'xpure' 'id' '<*>:' v = v@
--
-- [Composition]
--
--      @'xpure' (.) '<*>:' u '<*>:' v '<*>:' w = u '<*>:' (v '<*>:' w)@
--
-- [Homomorphism]
--
--      @'xpure' f '<*>:' 'xpure' x = 'xpure' (f x)@
--
-- [Interchange]
--
--      @u '<*>:' 'xpure' y = 'xpure' ('$' y) '<*>:' u@
--
--
-- The other methods have the following default definitions:
--
--   * @u '*>:' v = ('id' '<$' u) '<*>:' v@
--   * @u '<*:' v = 'xliftA2' 'const' u v@
--
-- The 'Functor' instance for @f p q@ will satisfy
--
--   * @'fmap' f x = 'xpure' f '<*>:' x@
--
-- If @f@ is also an 'XMonad', it should satisfy
--
--   * @'xpure' = 'Control.XMonad.xreturn'@
--   * @m1 '<*>:' m2 = m1 'Control.XMonad.>>=:' (\x1 -> m2 'Control.XMonad.>>=:' (\x2 -> 'Control.XMonad.xreturn' (x1 x2)))@
--   * @('*>:') = ('Control.XMonad.>>:')@
class (forall p q. Functor (f p q)) => XApplicative f where
  {-# MINIMAL xpure, ((<*>:) | xliftA2) #-}

  -- | Lift a value.
  xpure :: a -> f p p a

  -- | Sequential application.
  (<*>:) :: f p q (a -> b) -> f q r a -> f p r b
  (<*>:) = xliftA2 id

  -- | Lift a binary function to type-parameterized actions.
  --
  -- If 'fmap' is an expensive operation, it is likely better to use 'xliftA2' than to
  -- 'fmap' over the structure and then use '<*>:'.
  xliftA2 :: (a -> b -> c) -> f p q a -> f q r b -> f p r c
  xliftA2 f x = (<*>:) (fmap f x)

  -- | Sequence actions, discarding the value of the first argument.
  (*>:) :: f p q a -> f q r b -> f p r b
  a1 *>: a2 = (id <$ a1) <*>: a2

  -- | Sequence actions, discarding the value of the second argument.
  (<*:) :: f p q a -> f q r b -> f p r a
  (<*:) = xliftA2 const

-- | A variant of '<*>:' with the arguments reversed.
(<**>:) :: XApplicative f => f p q a -> f q r (a -> b) -> f p r b
(<**>:) = xliftA2 (\a f -> f a)

-- | Lift a function to actions.
-- This function may be used as a value for `fmap` in a `Functor` instance.
xliftA :: XApplicative f => (a -> b) -> f p q a -> f p q b
xliftA f a = xpure f <*>: a
{-# INLINEABLE xliftA #-}

-- | Lift a ternary function to actions.
xliftA3 :: XApplicative f => (a -> b -> c -> d) -> f p q a -> f q r b -> f r l c -> f p l d
xliftA3 f a b c = xliftA2 f a b <*>: c
{-# INLINEABLE xliftA3 #-}
