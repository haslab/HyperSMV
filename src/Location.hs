{-# LANGUAGE ScopedTypeVariables, DeriveFunctor, DeriveFoldable, DeriveTraversable #-}

module Location where
    
import Data.List as List
import Prettyprinter
import Prelude hiding ((<>))

data T = T {
  loc_fname :: String,
  loc_start :: (Int,Int),
  loc_end   :: (Int,Int),
  loc_bchar :: Int,
  loc_echar :: Int
} deriving (Eq,Ord,Show)

instance Pretty T where
    pretty loc = prettyLoc (loc_start loc) <> pretty ':' <> prettyLoc (loc_end loc)

prettyLoc :: (Int,Int) -> Doc ann
prettyLoc (l,c) = pretty "l" <> pretty l <> pretty "c" <> pretty c

_dummy = T {
  loc_fname = "",
  loc_start = (-1, -1),
  loc_end   = (-1, -1),
  loc_bchar = -1,
  loc_echar = -1
}

data I_loc = I_loc { 
    uid_loc  :: Int,
    base_loc :: T,
    stack_loc:: [T]
  } deriving (Eq,Ord,Show)

isdummy (p :: T) =
  loc_bchar p < 0 || loc_echar p < 0

merge (p1 :: T) (p2 :: T) =
  if isdummy p1 then p2 
  else if isdummy p2 then p1 
  else
    T { loc_fname = loc_fname p1,
      loc_start = min (loc_start p1) (loc_start p2) ,
      loc_end   = max (loc_end   p1) (loc_end   p2) ,
      loc_bchar = min (loc_bchar p1) (loc_bchar p2) ,
      loc_echar = max (loc_echar p1) (loc_echar p2)  }

mergeall (p :: [T]) =
  case p of
      []      -> _dummy
      t : ts -> List.foldl merge t ts

data Located a = Located {
  pl_loc  :: T,
  pl_desc :: a
} deriving (Eq,Ord,Show,Functor,Foldable,Traversable)
    

loc    x = pl_loc x
unloc  x = pl_desc x
unlocs x = List.map unloc x

lmk1 :: Located a -> c -> Located c
lmk1 la c = Located (loc la) c

lmk2 :: Located a -> Located b -> c -> Located c
lmk2 la lb c = Located (merge (loc la) (loc lb)) c

lmerge :: Located a -> Located b -> Located b
lmerge (Located p1 a) (Located p2 b) = Located (merge p1 p2) b

locMay :: Maybe (Located a) -> T
locMay Nothing = _dummy
locMay (Just l) = loc l

locCat :: [Located a] -> T
locCat = mergeall . map loc

lconcat :: Located [Located [a]] -> Located [a]
lconcat (Located p xs) = Located p $ concat (map unloc xs)

lmap2 :: (a -> b -> c) -> Located a -> Located b -> Located c
lmap2 f (Located p1 a) (Located p2 b) = Located (merge p1 p2) (f a b)

lmap3 :: (a -> b -> c -> d) -> Located a -> Located b -> Located c -> Located d
lmap3 f (Located p1 a) (Located p2 b) (Located p3 c) = Located (merge p1 p3) (f a b c)

lmap f x =
  x {  pl_desc = f (pl_desc x) }

mk_loc loc x =
  Located { pl_loc = loc, pl_desc = x }

dummyLoc :: a -> Located a
dummyLoc x = Located _dummy x

