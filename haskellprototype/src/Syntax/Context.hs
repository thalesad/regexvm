module Syntax.Context where

import Syntax.Regex
import Syntax.Tree

data Ctx
  = InChoiceL Regex
  | InChoiceR Regex
  | InCatL Regex
  | InCatR Regex
  | InStar
  deriving (Show)

type RegexCtx = [Ctx]

data Type = Begin | End deriving Show

type GenConf a = (Type, Regex, RegexCtx, a, String)

type Conf = GenConf Code

type TConf = GenConf [Tree]
