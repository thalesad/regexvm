module Conversion where

import Semantics
import Instances
import Text.Regex.Applicative
import qualified Text.Regex.Posix as R

toRE :: Regex -> RE Char Code
toRE Eps = const [] <$> string ""
toRE (Chr c) = const [] <$> sym c
toRE (Cat e e') = (++) <$> toRE e <*> toRE e'
toRE (Choice e e') = ((\c -> zero ++ c) <$> toRE e) <|> ((\c -> one ++ c) <$> toRE e')
toRE (Star e) = buildC <$> many (toRE e)
                where
                  buildC [] = one
                  buildC (c : cs) =  zero ++ c ++ buildC cs

toRegex :: Regex -> R.Regex
toRegex = R.makeRegex . show

one, zero :: Code
zero = [O]
one = [I]
