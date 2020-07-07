{-# LANGUAGE PolyKinds #-}

-- |
-- Module : Control.XMonad.Do
-- Copyright : (c) Evgeny Poberezkin
-- License : BSD3
--
-- Maintainer  : evgeny@poberezkin.com
-- Stability   : experimental
-- Portability : non-portable
--
-- This module re-defines standard monadic operations to allow @do@ expressions
-- with indexed monad 'XMonad' instances using
-- <https://downloads.haskell.org/ghc/latest/docs/html/users_guide/glasgow_exts.html#extension-RebindableSyntax RebindableSyntax> extension.
--
-- In addition to importing this module (it is not re-exported by @Control.'XMonad'@),
-- you have to explicitly import Prelude (or any replacement) hiding standard monadic operations:
--
-- > import Prelude hiding (fail, (>>), (>>=))
--
-- 'fail' is only needed if your indexed monad is also an instance of 'XMonadFail'.
--
-- You cannot combine @do@ expressions for normal and indexed monads in the same module.
module Control.XMonad.Do
  ( -- * Monadic functions
    (>>=),
    (>>),
    fail,
  )
where

import Control.XMonad
import Prelude hiding (fail, (>>), (>>=))

infixl 1 >>=, >>

(>>=) :: XMonad m => m i j a -> (a -> m j k b) -> m i k b
(>>=) = (>>=:)

(>>) :: XMonad m => m i j a -> m j k b -> m i k b
(>>) = (>>:)

fail :: XMonadFail m => String -> m i j a
fail = xfail
