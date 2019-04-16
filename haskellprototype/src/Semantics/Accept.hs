module Semantics.Accept where

import Syntax.Regex

{-
Funções retirada do paper: A play on regular expressions
e serve como uma implementação da semântica big-step
-}

parts :: [a] -> [[[a]]]
parts [] = [[]]
parts [c] = [[[c]]]
parts (c : cs) = concat [[(c : p) : ps , [c] : p : ps] | p : ps <- parts cs]

split :: [a] -> [([a],[a])]
split [] = [([],[])]
split (c:cs) = ([], c : cs) : [(c : s1 , s2) | (s1,s2) <- split cs] 

accept :: Regex -> String -> Bool
accept Epsilon s = null s
accept (Chr c) s = s == [c]
accept (e :+: e') s = accept e s || accept e' s
accept (e :@: e') s = or [accept e s1 && accept e' s2 | (s1,s2) <- split s]
accept (Star e) s = or [and [accept e u | u <- ps] | ps <- parts s]

----------------------------------------------------------------------------
