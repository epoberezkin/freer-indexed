{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fno-warn-unticked-promoted-constructors #-}

module XOpenUnion where

import Data.Kind
import GHC.TypeLits (ErrorMessage (..), TypeError)
import Unsafe.Coerce (unsafeCoerce)

-- Generalize the union
-- Union for two *->*->*->* type constructors
-- The union of two security policies

-- But this assumes that f1 and f2 share the same typestate.
-- f1 and f2 may have different type-state, and we which to combine
-- it.
-- Here is the analogy with the vector space?
-- data SumP f1 f2 s1 s2 x = LP (f1 s1 s2 x) | RP (f2 s1 s2 x)

-- Won't work either: If the change is on the left, there is no change
-- in the component
-- That is, if LP is present, sr1 must be equal to sr2
-- data SumP f1 f2 (sl1,sr1) (sl2,sr2) x =
--  LP (f1 sl1 sl2 x) | RP (f2 sr1 sr2 x)

-- That is, we need GADT

data SumP f1 f2 t1 t2 x where
  LP :: f1 sl1 sl2 x -> SumP f1 f2 (sl1, sr) (sl2, sr) x
  RP :: f2 sr1 sr2 x -> SumP f1 f2 (sl, sr1) (sl, sr2) x

-- TODO This idea is probably missed below

infixr 3 :>

data DList = DNil | forall a. a :> DList

-- data XUnion (fs :: DList) (is :: DList) (js :: DList) x where
--   XUnion :: {-# UNPACK #-} !Int -> f i j x -> XUnion fs is js x

data XUnion (fs :: DList) (is :: DList) (js :: DList) x where
  XUnion :: {-# UNPACK #-} !Int -> f i j x -> XUnion fs is (Inj f j fs is) x

-- type family InState f i fs is :: Constraint where
--   InState f i (f ':> _) (i ':> _) = ()
--   InState f i (_ ':> fs) (_ ':> is) = InState f i fs is

{-# INLINE inj' #-}
inj' :: Int -> f i j x -> XUnion fs is (Inj f j fs is) x
inj' = XUnion

{-# INLINE prj' #-}
prj' :: Int -> XUnion fs is js x -> Maybe (f (Prj fs is f) (Prj fs js f) x)
prj' n (XUnion n' f)
  | n == n' = Just $ unsafeCoerce f
  | otherwise = Nothing

newtype P f fs = P {unP :: Int}

class FindElem f fs where
  elemNo :: P f fs

instance {-# INCOHERENT #-} g ~ f => FindElem g (f ':> DNil) where
  elemNo = P 0

instance {-# INCOHERENT #-} FindElem f (f ':> fs) where
  elemNo = P 0

instance {-# OVERLAPPABLE #-} FindElem g fs => FindElem g (f ':> fs) where
  elemNo = P $ 1 + unP (elemNo :: P g fs)

class (FindElem f fs) => Member (f :: k -> k -> Type -> Type) fs where
  inj :: f i j x -> XUnion fs is (Inj f j fs is) x
  prj :: XUnion fs is js x -> Maybe (f (Prj fs is f) (Prj fs js f) x)

instance {-# OVERLAPPING #-} g ~ f => Member g (f ':> DNil) where
  {-# INLINE inj #-}
  {-# INLINE prj #-}
  inj x = XUnion 0 x
  prj (XUnion _ x) = Just (unsafeCoerce x)

instance {-# INCOHERENT #-} (FindElem f fs) => Member f fs where
  {-# INLINE inj #-}
  {-# INLINE prj #-}
  inj = inj' (unP (elemNo :: P f fs))
  prj = prj' (unP (elemNo :: P f fs))

-- {-# INLINE [2] decomp #-}
decomp ::
  XUnion (f ':> fs) (i ':> is) (j ':> js) x ->
  Either (XUnion fs is js x) (f i j x)
decomp (XUnion 0 x) = Right $ unsafeCoerce x
decomp (XUnion n x) = Left . unsafeCoerce $ XUnion (n - 1) x

-- {-# RULES "decomp/singleton" decomp = decomp0 #-}

-- {-# INLINE decomp0 #-}
decomp0 ::
  XUnion (f ':> DNil) (i ':> DNil) (j ':> DNil) x ->
  Either (XUnion DNil DNil DNil x) (f i j x)
decomp0 (XUnion _ v) = Right $ unsafeCoerce v

weaken :: XUnion fs is js x -> XUnion (f ':> fs) (i ':> is) (j :> js) x
weaken (XUnion n x) = unsafeCoerce $ XUnion (n + 1) x

type family Inj f j (fs :: DList) (is :: DList) where
  Inj f j (f ':> _) (_ ':> is) = j ':> is
  Inj f j (_ ':> fs) (k ':> is) = k ':> Inj f j fs is
  Inj f _ DNil _ = TypeError (NoEffect f)
  Inj f _ _ DNil = TypeError (NoEffect f :$$: StateError)

type family Prj fs is f where
  Prj (f ':> _) (i ':> _) f = i
  Prj (_ ':> fs) (_ ':> is) f = Prj fs is f
  Prj DNil _ f = TypeError (NoEffect f)
  Prj _ DNil f = TypeError (NoEffect f :$$: StateError)

type NoEffect f = Text "Effect " :<>: ShowType f :<>: Text " is not found."

type StateError = Text "Specified fewer states than effects."
