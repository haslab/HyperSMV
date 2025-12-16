module Pretty where

import Prettyprinter
import Prelude hiding ((<>))

sepBy o [] = emptyDoc
sepBy o [x] = x
sepBy o (x:xs) = x <+> o <+> sepBy o xs

prettyprint :: Pretty a => a -> String
prettyprint a = show $ pretty a

nestvcat :: Int -> [Doc ann] -> Doc ann
nestvcat i [] = emptyDoc
nestvcat i (x:xs) = nest i (vcat $ pretty (replicate i ' ') <> x : xs)