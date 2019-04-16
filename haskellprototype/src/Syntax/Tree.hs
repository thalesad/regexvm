module Syntax.Tree where

-- tree for RE evidence

import Syntax.Regex

-- tree definition

data Tree
  = TUnit         -- evidence for Epsilon
  | TChar Char    -- evidence for character
  | Tree :*: Tree -- evidence for concatenation
  | InL Tree      -- evidence for left choice
  | InR Tree      -- evidence for right choice
  | TList [Tree]  -- evidence for Kleene star
  deriving Show


flatten :: Tree -> String
flatten TUnit = ""
flatten (TChar c) = [c]
flatten (t :*: t') = flatten t ++ flatten t'
flatten (InL t) = flatten t
flatten (InR t) = flatten t
flatten (TList ts) = concatMap flatten ts

tc :: Tree -> Regex -> Bool
tc TUnit Epsilon = True
tc (TChar c) (Chr c') = c == c'
tc (t :*: t') (e :@: e') = tc t e && tc t' e'
tc (InL t) (e :+: _) = tc t e
tc (InR t') (_ :+: e') = tc t' e'
tc (TList ts) (Star e) = all (flip tc e) ts
tc _ _ = False

-- bit codes

data Bit = Zero | One  deriving Show
type Code = [Bit]

code :: Tree -> Regex -> Code
code (InL t) (e :+: _) = Zero : code t e
code (InR t') (_ :+: e') = One : code t' e'
code (TList ts) (Star e) = codeList ts e
code (t :*: t') (e :@: e') = code t e ++ code t' e'
code _ _ = []

codeList :: [Tree] -> Regex -> Code
codeList ts e = foldr (\ t ac -> Zero : code t e ++ ac) [One] ts


decode :: Regex -> Code -> Maybe Tree
decode e bs
  = case decode' e bs of
       Just (t, []) -> Just t
       _            -> Nothing


decode' :: Regex -> Code -> Maybe (Tree, Code)
decode' Epsilon bs
  = return (TUnit, bs)
decode' (Chr c) bs
  = return (TChar c, bs)
decode' (e :+: _) (Zero : bs)
  = do
     (t,bs1) <- decode' e bs
     return (InL t, bs1)
decode' (_ :+: e') (One : bs)
  = do
     (t',bs1) <- decode' e' bs
     return (InR t', bs1)
decode' (e :@: e') bs
  = do
      (t, bs1) <- decode' e bs
      (t', bs') <- decode' e' bs1
      return (t :*: t', bs')
decode' (Star e) bs
  = do
      (ts,bs') <- decodeList e bs
      return (TList ts, bs')
decode' _ _ = fail "fail decode'"

decodeList :: Regex -> Code -> Maybe ([Tree], Code)
decodeList _ [] = fail "fail decodeList"
decodeList _ (One : bs)
  = return ([], bs)
decodeList e (Zero : bs)
  = do
      (t, be) <- decode' e bs
      (ts, bs') <- decodeList e be
      return (t : ts, bs')

