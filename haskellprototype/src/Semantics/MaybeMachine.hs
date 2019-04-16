module Semantics.MaybeMachine where

import Control.Applicative
import Syntax.Context
import Syntax.Regex
import Syntax.Tree


exec :: Conf -> Maybe Conf
exec (Begin, Epsilon, ctx, bs, s)
  = exec (End, Epsilon, ctx, bs, s)
exec (Begin, Chr c, ctx, bs, a : s)
  | a == c = exec (End, Chr c, ctx, bs, s)
  | otherwise = Nothing
exec (Begin, e :+: e', ctx, bs, s)
  = exec (Begin, e, InChoiceL e' : ctx, Zero : bs, s) <|>
    exec (Begin, e', InChoiceR e : ctx, One : bs, s)
exec (Begin, e :@: e', ctx, bs, s)
  = exec (Begin, e, InCatL e' : ctx, bs, s)
exec (Begin, Star e, ctx, bs, s)
  = exec (Begin, e, InStar : ctx, Zero : bs, s) <|>
    exec (End, Star e, ctx, One : bs, s)
exec (End, e, InCatL e' : ctx, bs, s)
  = exec (Begin, e', InCatR e : ctx, bs, s)
exec (End, e', InCatR e : ctx, bs, s)
  = exec (End, e :@: e', ctx, bs, s) 
exec (End, e, InChoiceL e' : ctx, bs, s)
  = exec (End, e :+: e', ctx, bs, s)
exec (End, e', InChoiceR e : ctx, bs, s)
  = exec (End, e :+: e', ctx, bs, s)
exec (End, e, InStar : ctx, bs, s)
  = exec (Begin, e, InStar : ctx, Zero : bs, s) <|>
    exec (End, Star e, ctx, One : bs, s) 
exec conf
  | accepting conf = return conf
  | otherwise      = Nothing

vm :: String -> Regex -> Maybe Code
vm s e = maybe Nothing (\ (_,_,_,bs,_) -> Just (reverse bs))
                       (exec (Begin, e, [], [], s))


accepting :: Conf -> Bool
accepting (End, _, [], _, []) = True
accepting _                   = False
