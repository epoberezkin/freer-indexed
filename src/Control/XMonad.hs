{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}

-- |
-- Module : Control.XMonad
-- Copyright : (c) Evgeny Poberezkin
-- License : BSD3
--
-- Maintainer  : evgeny@poberezkin.com
-- Stability   : experimental
-- Portability : non-portable
--
-- 'XMonad' and 'XMonadFail type classes for type-indexed (parameterized)
-- monads with additional functions on them.
module Control.XMonad
  ( -- * XMonad
    XMonad (..),

    -- ** XMonad functions
    (=<<:),
    xliftM,
    xliftM2,
    xliftM3,
    xap,
    xjoin,
    (>=>:),
    (<=<:),
    (<$!>:),

    -- * XMonadFail
    XMonadFail (..),
  )
where

import Control.XApplicative

infixl 1 >>:, >>=:

infixr 1 =<<:, <=<:, >=>:

-- | The 'XMonad' class defines the basic operations over a
-- parameterized (indexed) /monad/, where two type parameters must be
-- correctly chained.
--
-- These monads have been described by Oleg Kiselyov here: http://okmij.org/ftp/Computation/monads.html#param-monad
--
-- Indexed monads have been previously released by Edward A. Kmett and Reiner Pope as the package "indexed" -
-- this package adds functions and freer indexed monad 'Control.XFreer.XFree'.
--
-- Semantically, these computations can represent type-level state changes
-- of some associated resource, with the first index parameter meaning
-- initial resource state prior to the computation, and the second index -
-- the final resource state, making each computation an edge in the graph
-- of resource state transitions.
--
-- Chained type parameters in bind operation require that associated resource changes are continuos.
--
-- When combined with computations defined as GADTs and singleton types
-- they can be used to limit allowed computations depending on the context
-- (that is reflected in the final type of the previous and initial type
-- of the next computations) and to make type-level state transitions dependent on the
-- run-time parameters and also on the results of the previous computations.
--
-- @do@ expressions can support such parameterized monads using RebindableSyntax
-- extension and @Control.XMonad.'Control.XMonad.Do'@ module
-- (it has to be imported separately).
--
-- If your code contains any action that can fail (e.g. "monadic" binding with
-- a potentially incomplete pattern match, you computation needs to be an instance
-- of 'XMonadFail' as well to be used in @do@ expression, although it is not recommended,
-- it is better to avoid incomplete pattern matches.
--
-- To use @do@ expressions 'GHC.Base.Prelude' has to be explicitly imported hiding monad operators:
--
-- > import Prelude hiding ((>>), (>>=))
--
-- Instances of 'XMonad' should satisfy the same laws as 'Monad':
--
-- [Left identity]  @'xreturn' a '>>=:' k  =  k a@
-- [Right identity] @m '>>=:' 'xreturn'  =  m@
-- [Associativity]  @m '>>=:' (\\x -> k x '>>=:' h)  =  (m '>>=:' k) '>>=:' h@
--
-- 'XMonad' and 'XApplicative' operations should relate as follows:
--
--   * @'xpure' = 'xreturn'@
--   * @mf '<*>:' m = mf '>>=:' (\\f -> m '>>=:' (\\x -> 'xreturn' (f x)))@
--
-- The above laws imply:
--
--   * @'fmap' f xs  =  xs '>>=:' 'xreturn' . f@
--   * @('>>:') = ('*>:')@
--
-- and that 'xpure' and ('<*>:') satisfy the applicative functor laws.
class XApplicative m => XMonad m where
  -- | Sequentially compose two parameterized actions, passing any value produced
  -- by the first as an argument to the second, and ensuring the continuity in
  -- type parameters changes.
  (>>=:) :: forall a b p q r. m p q a -> (a -> m q r b) -> m p r b

  -- | Sequentially compose two actions, discarding any value produced
  -- by the first, and ensuring the continuity in type parameters changes.
  (>>:) :: forall a b p q r. m p q a -> m q r b -> m p r b
  m >>: k = m >>=: \_ -> k
  {-# INLINE (>>:) #-}

  -- | Inject a value into the monadic type.
  xreturn :: a -> m p p a
  xreturn = xpure

(=<<:) :: XMonad m => (a -> m q r b) -> m p q a -> m p r b
f =<<: x = x >>=: f

-- | Promote a function to XMonad.
xliftM :: (XMonad m) => (a -> r) -> m p q a -> m p q r
xliftM f m = m >>=: \x -> xreturn (f x)
{-# INLINEABLE xliftM #-}

-- | Promote a binary function to XMonad, scanning the monadic arguments from left to right.
xliftM2 :: (XMonad m) => (a -> b -> c) -> m p q a -> m q r b -> m p r c
xliftM2 f m1 m2 =
  m1 >>=: \x1 ->
    m2 >>=: \x2 ->
      xreturn (f x1 x2)
{-# INLINEABLE xliftM2 #-}

-- | Promote a function to a monad, scanning the monadic arguments from left to right.
xliftM3 :: (XMonad m) => (a -> b -> c -> d) -> m p q a -> m q r b -> m r s c -> m p s d
xliftM3 f m1 m2 m3 =
  m1 >>=: \x1 ->
    m2 >>=: \x2 ->
      m3 >>=: \x3 ->
        xreturn (f x1 x2 x3)
{-# INLINEABLE xliftM3 #-}

-- | 'liftXM' operations can be replaced by uses of 'ap', which promotes function application.
--
-- > return f `ap` x1 `ap` ... `ap` xn
--
-- is equivalent to
--
-- > liftMn f x1 x2 ... xn
xap :: (XMonad m) => m p q (a -> b) -> m q r a -> m p r b
xap m1 m2 =
  m1 >>=: \x1 ->
    m2 >>=: \x2 ->
      xreturn (x1 x2)
{-# INLINEABLE xap #-}

-- | The 'xjoin' function removes one level of indexed monadic structure, projecting its
-- bound argument into the outer level.
--
-- \'@'join' bss@\' can be understood as the @do@ expression
--
-- @
-- do bs <- bss
--    bs
-- @
--
-- Please note the chaining order of type parameters - from outside to inside.
xjoin :: (XMonad m) => m p q (m q r a) -> m p r a
xjoin m = m >>=: id

-- | Left-to-right composition of Kleisli arrows.
--
-- \'@(f '>=>:' g) a@\' is equivalent to @\\x -> f x '>>=:' g@
(>=>:) :: XMonad m => (a -> m p q b) -> (b -> m q r c) -> (a -> m p r c)
f >=>: g = \x -> f x >>=: g

-- | Right-to-left composition of Kleisli arrows.
-- Same as @('>=>:')@, with the arguments flipped.
--
-- This operator resembles function composition @('.')@:
--
-- > (.)    ::             (b ->       c) -> (a ->       b) -> a ->       c
-- > (<=<:) :: XMonad m => (b -> m q r c) -> (a -> m p q b) -> a -> m p r c
(<=<:) :: XMonad m => (b -> m q r c) -> (a -> m p q b) -> (a -> m p r c)
(<=<:) = flip (>=>:)

infixl 4 <$!>:

-- | Strict version of 'Data.Functor.<$>' for indexed monads.
(<$!>:) :: XMonad m => (a -> b) -> m p q a -> m p q b
{-# INLINE (<$!>:) #-}
f <$!>: m =
  m >>=: \x ->
    let z = f x
     in z `seq` xreturn z

-- | When a type-indexed computation value is bound in @do@-notation (using RebindableSyntax for 'XMonad'),
-- the pattern on the left hand side of @<-@ might not match. In this case, this class
-- provides a function 'xfail' to recover.
--
-- An 'XMonad' without an 'XMonadFail' instance may only be used in conjunction
-- with pattern that always match, such as newtypes, tuples, data types with
-- only a single data constructor, and irrefutable patterns (@~pat@).
--
-- Instances of 'XMonadFail' should satisfy the following law: @xfail s@ should
-- be a left zero for '>>=:'.
--
-- @
-- xfail s >>=: f = xfail s
-- @
class XMonad m => XMonadFail m where
  xfail :: String -> m p q a
