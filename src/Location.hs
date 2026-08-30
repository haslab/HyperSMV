-- | Source-location spans and located values.
module Location where
    
import Data.List as List
import Prettyprinter
import Prelude hiding ((<>))

-- | A span in a source file.
data T = T {
  loc_fname :: String,
  loc_start :: (Int,Int),
  loc_end   :: (Int,Int),
  loc_bchar :: Int,
  loc_echar :: Int
} deriving (Eq,Ord,Show)

instance Pretty T where
    pretty loc = prettyLoc (loc_start loc) <> pretty ':' <> prettyLoc (loc_end loc)

-- | Pretty-prints a (line,column) pair.
prettyLoc :: (Int,Int) -> Doc ann
prettyLoc (l,c) = pretty "l" <> pretty l <> pretty "c" <> pretty c

_dummy = T {
  loc_fname = "",
  loc_start = (-1, -1),
  loc_end   = (-1, -1),
  loc_bchar = -1,
  loc_echar = -1
}

-- | A location with a unique id and a stack of enclosing locations.
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

-- | A value paired with its source location.
data Located a = Located {
  pl_loc  :: T,
  pl_desc :: a
} deriving (Eq,Ord,Show,Functor,Foldable,Traversable)
    

loc    x = pl_loc x
unloc  x = pl_desc x
unlocs x = List.map unloc x

-- | Reuses a located value's span for a new payload.
lmk1 :: Located a -> c -> Located c
lmk1 la c = Located (loc la) c

-- | Merges two located values' spans for a new payload.
lmk2 :: Located a -> Located b -> c -> Located c
lmk2 la lb c = Located (merge (loc la) (loc lb)) c

-- | Merges two located values' spans, keeping the second's payload.
lmerge :: Located a -> Located b -> Located b
lmerge (Located p1 a) (Located p2 b) = Located (merge p1 p2) b

-- | The location of an optional located value.
locMay :: Maybe (Located a) -> T
locMay Nothing = _dummy
locMay (Just l) = loc l

-- | Merges the spans of a list of located values.
locCat :: [Located a] -> T
locCat = mergeall . map loc

-- | Flattens a located list of located lists.
lconcat :: Located [Located [a]] -> Located [a]
lconcat (Located p xs) = Located p $ concat (map unloc xs)

-- | Combines two located values' payloads, merging their spans.
lmap2 :: (a -> b -> c) -> Located a -> Located b -> Located c
lmap2 f (Located p1 a) (Located p2 b) = Located (merge p1 p2) (f a b)

-- | Combines three located values' payloads, merging their spans.
lmap3 :: (a -> b -> c -> d) -> Located a -> Located b -> Located c -> Located d
lmap3 f (Located p1 a) (Located p2 b) (Located p3 c) = Located (merge p1 p3) (f a b c)

lmap f x =
  x {  pl_desc = f (pl_desc x) }

mk_loc loc x =
  Located { pl_loc = loc, pl_desc = x }

-- | Wraps a value with the dummy location.
dummyLoc :: a -> Located a
dummyLoc x = Located _dummy x

