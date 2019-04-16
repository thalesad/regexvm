module Parser where

import Data.Functor.Identity
import Semantics
import Text.Parsec
import Text.Parsec.Language
import Text.Parsec.Token as T
import Text.Parsec.Expr

type Parser a = ParsecT String () Identity a
type Lexer a = GenTokenParser String a Identity
type LangDef a = GenLanguageDef String a Identity

pRegex :: Parser Regex
pRegex
  = buildExpressionParser table pAtom <?> "regex top level"
    where
      table = [ [(Postfix ((pOperator "*") >> return Star))]
              , [(Infix ((pOperator "|") >> return Choice) AssocLeft)]
              ]

pAtom :: Parser Regex
pAtom = try (foldl1 Cat <$> many1 pChar) <|>
        pParens pRegex

pChar :: Parser Regex
pChar = Chr <$> noneOf "()|*"

regexdef :: LangDef a
regexdef
  = emptyDef {
      opStart = oneOf "|*"
    , opLetter = oneOf "|*"
    , reservedOpNames = ["|", "*"]
    }

lexer :: Lexer a
lexer = T.makeTokenParser regexdef

pOperator :: String -> Parser ()
pOperator = T.reservedOp lexer

pParens :: Parser a -> Parser a
pParens = T.parens lexer

parseRegex :: String -> Either String Regex
parseRegex inp
  = case parse pRegex "" inp of
      Left err -> Left (show err)
      Right e  -> Right e
