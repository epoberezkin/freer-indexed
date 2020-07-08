{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -fno-max-relevant-binds #-}
{-# OPTIONS_GHC -fno-warn-unticked-promoted-constructors #-}

module XEff where

import Control.XApplicative
import Control.XMonad
import GHC.Exts (inline)
import XFTCQueue
import XOpenUnion

-- Effectful arrow type: a function from a to b that also does indexed effects
-- denoted by r i j
type XArr fs i j a b = a -> XEff fs i j b

-- An effectful function from 'a' to 'b' that is a composition
-- of several effectful functions. The paremeter r describes the overall
-- effect.
-- The composition members are accumulated in a type-aligned queue
type XArrs fs i j a b = XFTCQueue (XEff fs) i j a b

-- The XEff XMonad
-- It is a parameterized / indexed "monad" (XMonad)
data XEff fs i j a where
  Val :: a -> XEff fs i i a
  E :: XUnion fs i j b -> XArrs fs j k b a -> XEff fs i k a

instance Functor (XEff fs i j) where
  {-# INLINE fmap #-}
  fmap f (Val x) = Val (f x)
  fmap f (E u q) = E u (q |> (Val . f)) -- does no mapping yet!

instance XApplicative (XEff fs) where
  xpure :: a -> XEff fs i i a
  xpure = Val
  (<*>:) :: XEff fs i j (a -> b) -> XEff fs j k a -> XEff fs i k b
  Val f <*>: Val x = Val (f x)
  Val f <*>: E u q = E u (q |> (Val . f))
  E u q <*>: Val x = E u (q |> (Val . ($ x)))
  E u q <*>: m = E u (q |> (`fmap` m))

instance XMonad (XEff fs) where
  {-# INLINE xreturn #-}
  {-# INLINE [2] (>>=:) #-}
  xreturn :: a -> XEff fs i i a
  xreturn = Val
  (>>=:) :: XEff fs i j a -> (a -> XEff fs j k b) -> XEff fs i k b
  Val x >>=: k = k x
  E u q >>=: k = E u (q |> k) -- just accumulates continuations
  {-
    Val _ >>: m = m
    E u q >>: m = E u (q |> const m)
  -}

-- Application to the `generalized effectful function' XArrs r i j b w

--  {-# INLINEABLE qApp #-}
qApp :: XArrs fs i j b w -> b -> XEff fs i j w -- ?
qApp q x = case inline tviewl q of
  TOne k -> k x
  k :| t -> bind' (k x) t
  where
    bind' :: XEff fs i j a -> XArrs fs j k a b -> XEff fs i k b
    bind' (Val y) k = qApp k y
    bind' (E u q) k = E u (q >< k)

-- Compose effectful arrows (and possibly change the effect!)
{-# INLINE qComp #-}
qComp :: XArrs fs i j a b -> (XEff fs i j b -> XEff fs' i' j' c) -> XArr fs' i' j' a c
-- qComp g h = (h . (g `qApp`))
qComp g h a = h $ qApp g a

-- {-# INLINE qComps #-}
qComps :: XArrs fs i j a b -> (XEff fs i j b -> XEff fs' i' j' c) -> XArrs fs' i' j' a c
qComps g h = tsingleton $ qComp g h

-- send a request and wait for a reply
{-# INLINE [2] send #-}
send :: Member f fs => f i j x -> XEff fs is (Inj f j fs is) x
send t = E (inj t) (tsingleton Val)

run :: XEff DNil DNil DNil x -> x
run (Val x) = x
run (E _ _) = error ""

-- {-# INLINE handleRelay #-}
handleRelay ::
  forall f i j fs is js a b.
  (forall ks. a -> XEff fs ks ks b) ->
  (forall v p q qs. f p q v -> XArr fs qs js v b -> XEff fs qs js b) ->
  XEff (f ':> fs) (i ':> is) (j ':> js) a ->
  XEff fs is js b
handleRelay ret h e = loop e
  where
    loop :: XEff (f ':> fs) (i ':> is) (j ':> js) a -> XEff fs is js b
    loop (Val x) = ret x
    loop (E u q) = case decomp u of
      Right x -> h x k
      Left u -> E u (tsingleton k)
      where
        k = qComp q loop

-- runProtocol ::
--   forall m cmd ps s s' a.
--   Monad m =>
--   -- | function to interpret a command
--   (forall from to b. (Sing (P from) -> Sing (P to) -> cmd from to b -> m b)) ->
--   -- | protocol scenario (see example in @'Control.Protocol.Example.Scenario'@)
--   Protocol cmd ps s s' a ->
--   m a
-- runProtocol runCmd = loop
--   where
--     loop :: forall s1 s2 b. Protocol cmd ps s1 s2 b -> m b
--     loop (Pure x) = return x
--     loop (Bind c f) = run c >>= loop . f
--     run :: forall s1 s2 b. ProtocolCmd cmd ps s1 s2 b -> m b
--     run (ProtocolCmd from to cmd) = runCmd from to cmd

-- handleRelay fails with:
-- • Couldn't match type ‘j1’ with ‘k0 ':> is’
-- ‘j1’ is a rigid type variable bound by
--   a pattern with constructor:
--     E :: forall (fs :: DList) (i :: DList) (j :: DList) b (k :: DList)
--                 a.
--          XUnion fs i j b -> XArrs fs j k b a -> XEff fs i k a,
--   in an equation for ‘loop’
--   at src/XEff.hs:98:11-15
-- Expected type: XUnion (f ':> fs) (i ':> is) (k0 ':> is) b
--   Actual type: XUnion (f ':> fs) (i ':> is) j1 b
-- • In the first argument of ‘decomp’, namely ‘u’
-- In the expression: decomp u
-- In the expression:
--   case decomp u of
--     Right x -> h x k
--     Left u -> E u (tsingleton k)
-- • Relevant bindings include
--   k :: XArr fs is js b w (bound at src/XEff.hs:102:9)
--   q :: XArrs (f ':> fs) j1 (j ':> js) b a2
--     (bound at src/XEff.hs:98:15)
--   u :: XUnion (f ':> fs) (i ':> is) j1 b (bound at src/XEff.hs:98:13)
--   loop :: XEff (f ':> fs) (i ':> is) (j ':> js) a2 -> XEff fs is js w
--     (bound at src/XEff.hs:97:5)
--   e :: XEff (f ':> fs) (i ':> is) (j ':> js) a2
--     (bound at src/XEff.hs:95:19)
--   h :: forall v (k :: k1) (ks :: DList).
--        f i k v -> XArr fs ks js v w -> XEff fs is js w
--     (bound at src/XEff.hs:95:17)
--   ret :: a2 -> XEff fs is is w (bound at src/XEff.hs:95:13)
--   handleRelay :: (a2 -> XEff fs is is w)
--                  -> (forall v (k :: k1) (ks :: DList).
--                      f i k v -> XArr fs ks js v w -> XEff fs is js w)
--                  -> XEff (f ':> fs) (i ':> is) (j ':> js) a2
--                  -> XEff fs is js w
--     (bound at src/XEff.hs:95:1)

-- |
-- 98 |     loop (E u q) = case decomp u of
