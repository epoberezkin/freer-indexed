{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE PolyKinds #-}

module XEff where

import GHC.Exts (inline)
import XFTCQueue
import XMonad
import XOpenUnion

-- Effectful arrow type: a function from a to b that also does indexed effects
-- denoted by r i j
type XArr r i j a b = a -> XEff r i j b

-- An effectful function from 'a' to 'b' that is a composition
-- of several effectful functions. The paremeter r describes the overall
-- effect.
-- The composition members are accumulated in a type-aligned queue
type XArrs r i j a b = XFTCQueue (XEff r) i j a b

-- The XEff XMonad
-- It is a parameterized / indexed "monad" (XMonad)
data XEff r i j a where
  Val :: a -> XEff r i i a
  E :: XUnion r b -> XArrs r i j b a -> XEff r i j a

instance Functor (XEff r i j) where
  {-# INLINE fmap #-}
  fmap f (Val x) = Val (f x)
  fmap f (E u q) = E u (q |> (Val . f)) -- does no mapping yet!

instance XApplicative (XEff r) where
  xpure = Val
  (<*>:) :: XEff r i j (a -> b) -> XEff r j k a -> XEff r i k b
  Val f <*>: Val x = Val (f x)
  Val f <*>: E u q = E u (q |> (Val . f))
  E u q <*>: Val x = E u (q |> (Val . ($ x)))
  E u q <*>: m = E u (q |> (`fmap` m))

instance XMonad (XEff r) where
  {-# INLINE xreturn #-}
  {-# INLINE [2] (>>=:) #-}
  xreturn x = Val x
  Val x >>=: k = k x
  E u q >>=: k = E u (q |> k) -- just accumulates continuations
  {-
    Val _ >>: m = m
    E u q >>: m = E u (q |> const m)
  -}

-- -- Application to the `generalized effectful function' XArrs r i j b w

-- -- {-# INLINEABLE qApp #-}

qApp :: XArrs r i j b w -> b -> XEff r i j w
qApp q x =
  case inline tviewl q of
    TOne k -> k x
    k :| t -> case k x of
      Val y -> qApp t y
      E u q -> E u (q >< t)

-- Compose effectful arrows (and possibly change the effect!)
{-# INLINE qComp #-}
qComp :: XArrs r i j a b -> (XEff r i j b -> XEff r' k l c) -> XArr r' k l a c
-- qComp g h = (h . (g `qApp`))
qComp g h a = h $ qApp g a

{-# INLINE qComps #-}
qComps :: XArrs r i j a b -> (XEff r i j b -> XEff r' k l c) -> XArrs r' k l a c
qComps g h = tsingleton $ \a -> h $ qApp g a

-- send a request and wait for a reply
-- {-# INLINE [2] send #-}
-- this does not compile
-- send :: Member t r => t i j v -> XEff r i j v
-- send t = E (inj t) (tsingleton Val)
