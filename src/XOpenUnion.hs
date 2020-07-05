{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
-- Only for MemberU below, when emulating Monad Transformers
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
-- Only for MemberU below, when emulating Monad Transformers
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fno-warn-unticked-promoted-constructors #-}

-- Open unions (type-indexed co-products) for resource-aware effects

-- Our list r of open union components is a small Universe.
-- Therefore, we can use the Typeable-like evidence in that
-- universe. We hence can define
--
-- data Union r v where
--  Union :: t v -> TRep t r -> Union r v -- t is existential
-- where
-- data TRep t r where
--  T0 :: TRep t (t ': r)
--  TS :: TRep t r -> TRep (any ': r)
-- Then Member is a type class that produces TRep
-- Taken literally it doesn't seem much better than
-- OpenUinion41.hs. However, we can cheat and use the index of the
-- type t in the list r as the TRep. (We will need UnsafeCoerce then).

-- The interface is the same as of other OpenUnion*.hs
module XOpenUnion
  ( XUnion,
    inj,
    prj,
    decomp,
    Member,
    MemberU2,
    weaken,
  )
where

import Data.Kind
import Unsafe.Coerce (unsafeCoerce)

-- The data constructors of Union are not exported

-- Strong Sum (Existential with the evidence) is an open union
-- t is can be a GADT and hence not necessarily a Functor.
-- Int is the index of t in the list r; that is, the index of t in the
-- universe r
data XUnion (r :: [k -> k -> Type -> Type]) v where
  XUnion :: {-# UNPACK #-} !Int -> t i j v -> XUnion r v

{-# INLINE prj' #-}

{-# INLINE inj' #-}
inj' :: Int -> t i j v -> XUnion r v
inj' = XUnion

prj' :: Int -> XUnion r v -> Maybe (t i j v)
prj' n (XUnion n' x)
  | n == n' = Just (unsafeCoerce x)
  | otherwise = Nothing

newtype P t r = P {unP :: Int}

class (FindElem t r) => Member (t :: k -> k -> Type -> Type) r where
  inj :: t i j v -> XUnion r v
  prj :: XUnion r v -> Maybe (t i j v)

-- Optimized specialized instance
-- Explicit type-level equality condition is a dirty
-- hack to eliminate the type annotation in the trivial case,
-- such as @run (runReader get ())@.
--
-- There is no ambiguity when finding instances for
-- @Member t (a ': b ': r)@, which the second instance is selected.
--
-- The only case we have to concerned about is  @Member t '[s]@.
-- But, in this case, values of definition is the same (if present),
-- and the first one is chosen according to GHC User Manual, since
-- the latter one is incoherent. This is the optimal choice.
instance {-# OVERLAPPING #-} t ~ s => Member t '[s] where
  {-# INLINE inj #-}
  {-# INLINE prj #-}
  inj x = XUnion 0 x
  prj (XUnion _ x) = Just (unsafeCoerce x)

instance {-# INCOHERENT #-} (FindElem t r) => Member t r where
  {-# INLINE inj #-}
  {-# INLINE prj #-}
  inj = inj' (unP (elemNo :: P t r))
  prj = prj' (unP (elemNo :: P t r))

{-# INLINE [2] decomp #-}
decomp :: XUnion (t ': r) v -> Either (XUnion r v) (t i j v)
decomp (XUnion 0 v) = Right $ unsafeCoerce v
decomp (XUnion n v) = Left $ XUnion (n - 1) v

-- Specialized version
{-# RULES "decomp/singleton" decomp = decomp0 #-}

{-# INLINE decomp0 #-}
decomp0 :: XUnion '[t] v -> Either (XUnion '[] v) (t i j v)
decomp0 (XUnion _ v) = Right $ unsafeCoerce v

-- No other case is possible

weaken :: XUnion r w -> XUnion (any ': r) w
weaken (XUnion n v) = XUnion (n + 1) v

-- Find an index of an element in a `list'
-- The element must exist
-- This is essentially a compile-time computation.
class FindElem (t :: k -> k -> Type -> Type) r where
  elemNo :: P t r

-- Stopped Using Obsolete -XOverlappingInstances
-- and explicitly specify to choose the topmost
-- one for multiple occurence, which is the same
-- behaviour as OpenUnion51 with GHC 7.10.
-- instance {-# OVERLAPPING #-} t ~ s => FindElem t '[s] where
--   elemNo = P 0

instance {-# INCOHERENT #-} t ~ s => FindElem t '[s] where
  elemNo = P 0

instance {-# INCOHERENT #-} FindElem t (t ': r) where
  elemNo = P 0

instance {-# OVERLAPPABLE #-} FindElem t r => FindElem t (t' ': r) where
  elemNo = P $ 1 + unP (elemNo :: P t r)

type family EQU (a :: k) (b :: k) :: Bool where
  EQU a a = True
  EQU a b = False

-- This class is used for emulating monad transformers
class Member t r => MemberU2 (tag :: g -> k -> k -> Type -> Type) (t :: k -> k -> Type -> Type) r | tag r -> t

instance (MemberU' (EQU t1 t2) tag t1 (t2 ': r)) => MemberU2 tag t1 (t2 ': r)

class
  Member t r =>
  MemberU' (f :: Bool) (tag :: g -> k -> k -> Type -> Type) (t :: k -> k -> Type -> Type) r
    | tag r -> t

instance MemberU' True tag (tag e) (tag e ': r)

instance
  (Member t (t' ': r), MemberU2 tag t r) =>
  MemberU' False tag t (t' ': r)
