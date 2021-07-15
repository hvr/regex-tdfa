module AdditionalTests.Fencepost ( FenceCase(..)
                                 , fenceVal
                                 , fencepost ) where
import Data.List.NonEmpty

{- The name of this module is "Fencepost" because it is nammed after my attempt to deal with fencepost errors.

   While a minor inconvience normally, they are even more annoying and relevent in this test suite because
   if I am searching through a list, sometimes I want to match a character based on the current character,
   but sometimes I want to match based on the previous character. Since I only need to worry about the
   previous character, writing a fold over the entire list seems like overkill, and will just make things
   more complicated. I only want to worry about the current character, or the relationship between two
   consequtive characters

   I do all of the case analysis in this module, and then I actually match a character in the regex against a
   character in the string in the parent module.  -}
data FenceCase a = FenceStart a    -- The first element
                 | FenceGap a a    -- The previous element and the current one
                 | FenceEnd a    -- The previous element
  deriving (Eq, Ord, Show)
instance Functor FenceCase where
  fmap f (FenceStart a) = FenceStart (f a)
  fmap f (FenceGap a b) = FenceGap (f a) (f b)
  fmap f (FenceEnd a)  = FenceEnd (f a)

fenceVal :: FenceCase a -> a
fenceVal (FenceStart c) = c
fenceVal (FenceGap _ c) = c
fenceVal (FenceEnd c) = c

fencepost :: NonEmpty a -> NonEmpty (FenceCase a)
fencepost (a:|[]) = FenceStart a:|[FenceEnd a]
fencepost (a:|b:c) = FenceStart a:|(inner b c) where
  inner x [] = [FenceEnd x]
  inner y (x:xs) = FenceGap y x:inner x xs

{-
fenceFoldl :: (b -> FenceCase a -> b) -> b -> Fence a -> b
fenceFoldl f b (Fence []) = f b FenceEmpty
fenceFoldl f b (Fence (x:xs)) = inner (f b (FenceStart x)) x xs where
  inner b' prev [] = f b' (FenceEnd prev)
  inner b' prev (y:ys) = let y' = FenceInner prev y
                             z = f b' y'
                         in seq z (inner (f z (FenceInner prev y)) y ys)

fenceFoldr :: (FenceCase a -> b -> b) -> b -> Fence a -> b
fenceFoldr f b (Fence []) = f FenceEmpty b
fenceFoldr f b (Fence (x:xs)) = f (FenceStart x) (inner b x xs) where
  inner b' prev [] = f (FenceEnd prev) b'
  inner b' prev (y:ys) = f (FenceInner prev y) (inner b' y ys)

fenceFoldrM :: (Monad m) => (FenceCase a -> b -> m b) -> m b -> Fence a -> m b
fenceFoldrM f b (Fence []) = b >>= f FenceEmpty
fenceFoldrM f b (Fence (x:xs)) = inner b x xs >>= f (FenceStart x) where
  inner b' prev [] = b' >>= f (FenceEnd prev)
  inner b' prev (y:ys) = inner b' y ys >>= f (FenceInner prev y) 


fenceMap :: (FenceCase a -> b) -> Fence a -> [b]
fenceMap f (Fence []) = [f FenceEmpty]
fenceMap f (Fence (x:xs)) = f (FenceStart x):inner x xs where
  inner y [] = [f (FenceEnd y)]
  inner y (ys:yss) = f (FenceInner y ys):inner ys yss

fenceTraverse :: (Applicative f) => (FenceCase a -> f b) -> Fence a -> f [b]
fenceTraverse f (Fence []) = (:[]) <$> f FenceEmpty
fenceTraverse f (Fence (x:xs)) = (:) <$> f (FenceStart x) <*> inner x xs where
  inner y [] = (:[]) <$> f (FenceEnd y)
  inner y (ys:yss) = (:) <$> f (FenceInner y ys) <*> inner ys yss

-}
