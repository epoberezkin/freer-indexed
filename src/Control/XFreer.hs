{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}

-- |
-- Module : Control.XFreer
-- Copyright : (c) Evgeny Poberezkin
-- License : BSD3
--
-- Maintainer  : evgeny@poberezkin.com
-- Stability   : experimental
-- Portability : non-portable
--
-- This module defines a "freer indexed monad" 'XFree'.
-- It generalizes freer monad to have type indices/parameters:
--
--   * <http://okmij.org/ftp/Haskell/extensible/more.pdf Freer Monads, More Extensible Effects by Oleg Kiselyov and Hiromi Ishii>
--   * <http://okmij.org/ftp/Computation/monads.html#param-monad Parameterized monads>
--   * <http://okmij.org/ftp/Haskell/extensible/index.html#extext Parameterized extensible effects and session types>
--
-- It defines 'Functor' instance for @'XFree' f p q@, 'XApplicative' and 'XMonad' instances for @'XFree' f@,
-- as well as 'Applicative' and 'Monad' instances for @'XFree' f p p@, where f is an effect of kind @k -> k -> Type -> Type@
--
-- 'XFree' simplifies defining indexed monadic computations as GADTs without making
-- them into ad-hoc indexed monads and defining all needed applicative and monadic functions on them.
--
-- __Example__
--
-- Given an indexed (non-composable) effect XState that allows
-- changing data type of the stored data and tracks these changes on the type level:
--
-- > data IxdState s s' x where
-- >   XGet :: IxdState s s s
-- >   XPut :: s' -> IxdState s s' ()
--
-- you can make it into an indexed monad and use it with do notation
-- (with @RebindableSyntax@ and @Control.XMonad.'Control.XMonad.Do'@)
-- with a few lines of boilerplate:
--
-- > type XState = XFree IxdState
-- >
-- > xGet :: XState s s s
-- > xGet = xfree XGet
-- >
-- > xPut :: s' -> XState s s' ()
-- > xPut = xfree . XPut
--
-- To execute this effect you need an interpreter:
--
-- > runXState :: XState s s' x -> s -> (x, s')
-- > runXState (Pure x) s = (x, s)
-- > runXState (Bind m j) s =
-- >   let (x, s') = unIxdState m s in runXState (j x) s'
-- >
-- > unIxdState :: IxdState s s' x -> (s -> (x, s'))
-- > unIxdState XGet s = (s, s)
-- > unIxdState (XPut s) _ = ((), s)
module Control.XFreer
  ( XFree (..),
    xfree,
  )
where

import Control.XApplicative
import Control.XMonad

-- | 'XFree' is the freer indexed monad that wraps an (algebraic, non-composable) effect
-- to provide 'Functor', 'XApplicative' and 'XMonad' (indexed applicative and monad) for free.
data XFree f p q a where
  Pure :: a -> XFree f p p a
  Bind :: f p q x -> (x -> XFree f q r a) -> XFree f p r a

-- | Function to convert an indexed effect to 'XFree' monad (see example above)
xfree :: f p q a -> XFree f p q a
xfree fa = Bind fa Pure

instance Functor (XFree f p q) where
  fmap f (Pure x) = Pure (f x)
  fmap f (Bind u j) = Bind u (fmap f . j)

instance XApplicative (XFree f) where
  xpure = Pure
  Pure f <*>: x = fmap f x
  Bind u j <*>: x = Bind u ((<*>: x) . j)

instance XMonad (XFree f) where
  Pure x >>=: f = f x
  Bind u f >>=: g = Bind u (f >=>: g)

Foldable

-- | @'XFree' (f p p)@ is a normal Applicative, it supports 'Control.Monad.forever', 'traverse', 'sequenceA', etc.
instance Applicative (XFree f p p) where
  pure = xpure
  (<*>) = (<*>:)

-- | @'XFree' (f p p)@ is a normal Monad, it supports 'mapM', 'Control.Monad.forM', 'sequence', etc.
instance Monad (XFree f p p) where
  (>>=) = (>>=:)
