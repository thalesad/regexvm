module Semantics.ThompsonMachine where

import Syntax.Regex
import Syntax.Context
import Syntax.Tree

next :: Conf -> [Conf]
next (Begin, Epsilon, ctx, bs,s)
  = [(End, Epsilon, ctx, bs,s)]
next (Begin, Chr c, ctx, bs, a:s)
  | a == c =  [(End, Chr c, ctx, bs, s)]
  | otherwise = []
next (Begin, e :+: e', ctx, bs, s)
  = [
      (Begin, e, InChoiceL e' : ctx, Zero : bs, s)
    , (Begin, e', InChoiceR e : ctx, One : bs, s)
    ]
next (Begin, e :@: e', ctx, bs, s)
  = [(Begin, e, InCatL e' : ctx, bs, s)]
next (Begin, Star e, ctx, bs, s)
  = [ (Begin, e , InStar : ctx, Zero : bs, s)
    , (End, (Star e), ctx, One : bs, s)
    ]
next (End, e, InCatL e' : ctx, bs, s)
  = [(Begin, e', InCatR e : ctx, bs, s)]
next (End, e', InCatR e : ctx, bs, s)
  = [(End, e :@: e', ctx, bs, s)]
next (End, e, InChoiceL e' : ctx, bs, s)
  = [(End, e :+: e', ctx, bs, s)]
next (End, e', InChoiceR e : ctx, bs, s)
  = [(End, e :+: e', ctx, bs, s)]
next (End, e, InStar : ctx, bs, s)
  = [
      (Begin, e, InStar : ctx, Zero : bs, s)
    , (End, (Star e), ctx, One : bs, s)
    ]
next _ = []


steps :: [Conf] -> [Conf]
steps [] = []
steps cs = steps (concatMap next cs) ++ cs --steps [c' | c <- cs, c' <- next c] ++ cs

finish :: Conf -> Bool
finish (End, _, [], _, []) = True
finish _ = False

taccept :: String -> Regex -> (Bool, Code)
taccept s e = let r = [c | c <- steps [(Begin, e, [], [], s)], finish c]
              in if null r then (False, []) else (True, bitcode (head r))
              where
                bitcode (_,_,_,bs,_) = reverse bs
