{-# LANGUAGE GADTs #-}

module XFreer where

import XMonad

data XFree f i j a where
  XPure :: a -> XFree f i i a
  XImpure :: f i j x -> (x -> XFree f j k a) -> XFree f i k a

etaF :: f i j a -> XFree f i j a
etaF fa = XImpure fa XPure

instance Functor (XFree f i j) where
  fmap f (XPure x) = XPure (f x)
  fmap f (XImpure u j) = XImpure u (fmap f . j)

instance XApplicative (XFree f) where
  xpure = XPure
  XPure f <*>: x = fmap f x
  XImpure u j <*>: x = XImpure u ((<*>: x) . j)

instance XMonad (XFree f) where
  xreturn = XPure
  XPure x >>=: f = f x
  XImpure u f >>=: g = XImpure u (f >=>: g)

data XStateEff s s' x where
  XGet :: XStateEff s s s
  XPut :: s' -> XStateEff s s' ()

type XEffState = XFree XStateEff

xGetEff :: XEffState s s s
xGetEff = etaF XGet

xPutEff :: s' -> XEffState s s' ()
xPutEff = etaF . XPut

runXEffState :: XEffState s s' x -> s -> (x, s')
runXEffState (XPure x) s = (x, s)
runXEffState (XImpure m j) s =
  let (x, s') = unXEffState m s in runXEffState (j x) s'

unXEffState :: XStateEff s s' x -> (s -> (x, s'))
unXEffState XGet s = (s, s)
unXEffState (XPut s) _ = ((), s)
