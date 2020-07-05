{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}

-- Fast type-aligned queue optimized to resourceful effectful functions
-- (a -> m i j b)
-- (indexed monad XMonad continuations have this type).
-- Constant-time append and snoc and
-- average constant-time left-edge deconstruction

module XFTCQueue
  ( XFTCQueue,
    tsingleton,
    (|>), -- snoc
    (><), -- append
    ViewL (..),
    tviewl,
  )
where

-- Non-empty tree. Deconstruction operations make it more and more
-- left-leaning

data XFTCQueue m i j a b where
  Leaf :: (a -> m i j b) -> XFTCQueue m i j a b
  Node :: XFTCQueue m i j a x -> XFTCQueue m j k x b -> XFTCQueue m i k a b

-- Exported operations

-- There is no tempty: use (tsingleton return), which works just the same.
-- The names are chosen for compatibility with FastTCQueue

{-# INLINE tsingleton #-}
tsingleton :: (a -> m i j b) -> XFTCQueue m i j a b
tsingleton = Leaf

-- snoc: clearly constant-time
{-# INLINE (|>) #-}
(|>) :: XFTCQueue m i j a x -> (x -> m j k b) -> XFTCQueue m i k a b
t |> k = Node t (Leaf k)

-- append: clearly constant-time
{-# INLINE (><) #-}
(><) :: XFTCQueue m i j a x -> XFTCQueue m j k x b -> XFTCQueue m i k a b
t1 >< t2 = Node t1 t2

-- Left-edge deconstruction
data ViewL m i j a b where
  TOne :: (a -> m i j b) -> ViewL m i j a b
  (:|) :: (a -> m i j x) -> XFTCQueue m j k x b -> ViewL m i k a b

{-# INLINEABLE tviewl #-}
tviewl :: XFTCQueue m i j a b -> ViewL m i j a b
tviewl (Leaf k) = TOne k
tviewl (Node t1 t2) = go t1 t2
  where
    go :: XFTCQueue m i j a x -> XFTCQueue m j k x b -> ViewL m i k a b
    go (Leaf k) tr = k :| tr
    go (Node tl1 tl2) tr = go tl1 (Node tl2 tr)
